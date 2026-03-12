use crate::events::Event;
use crate::chain::transaction::OutPoint as FundingOutPoint;
use crate::ln::channel::DISCONNECT_PEER_AWAITING_RESPONSE_TICKS;
use crate::ln::channelmanager::PaymentId;
use crate::ln::functional_test_utils::*;
use crate::ln::msgs::{BaseMessageHandler, ChannelMessageHandler, MessageSendEvent};
use crate::ln::outbound_payment::RecipientOnionFields;

use bitcoin::hashes::Hash;
use bitcoin::ScriptBuf;
use bitcoin::Txid;

fn test_outpoint(byte: u8, vout: u16) -> FundingOutPoint {
	FundingOutPoint { txid: Txid::from_byte_array([byte; 32]), index: vout }
}

fn start_teleport<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>,
	channel_id: crate::ln::types::ChannelId, new_funding_txo: FundingOutPoint,
) {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

	initiator.node.teleport_channel(&channel_id, &responder_id, new_funding_txo).unwrap();

	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);

	let teleport_init = get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);
	responder.node.handle_teleport_init(initiator_id, &teleport_init);
}

fn ack_teleport<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>,
	channel_id: crate::ln::types::ChannelId,
) {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 2, "{responder_events:?}");
	let teleport_ack = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendTeleportAck { msg, .. } => msg,
		event => panic!("Unexpected event {event:?}"),
	};
	let responder_commitment_signed =
		match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
			MessageSendEvent::UpdateHTLCs { updates, .. } => updates.commitment_signed[0].clone(),
			event => panic!("Unexpected event {event:?}"),
		};
	initiator.node.handle_teleport_ack(responder_id, &teleport_ack);

	let initiator_commitment_signed =
		get_htlc_update_msgs(initiator, &responder_id).commitment_signed[0].clone();

	initiator
		.node
		.handle_commitment_signed(responder_id, &responder_commitment_signed);
	check_added_monitors(initiator, 1);

	responder
		.node
		.handle_commitment_signed(initiator_id, &initiator_commitment_signed);
	check_added_monitors(responder, 1);
}

fn current_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: crate::ln::types::ChannelId,
) -> FundingOutPoint {
	node
		.node
		.list_channels()
		.into_iter()
		.find(|channel| channel.channel_id == channel_id)
		.and_then(|channel| channel.funding_txo)
		.unwrap()
}

fn current_monitor_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: crate::ln::types::ChannelId,
) -> FundingOutPoint {
	get_monitor!(node, channel_id).get_funding_txo()
}

fn monitor_watches_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: crate::ln::types::ChannelId,
	funding_txo: FundingOutPoint,
) -> bool {
	get_monitor!(node, channel_id)
		.get_outputs_to_watch()
		.into_iter()
		.any(|(txid, outputs)| {
			txid == funding_txo.txid
				&& outputs.iter().any(|(idx, _)| *idx == funding_txo.index as u32)
		})
}

fn funding_watch_script<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: crate::ln::types::ChannelId,
	funding_txo: FundingOutPoint,
) -> ScriptBuf {
	get_monitor!(node, channel_id)
		.get_outputs_to_watch()
		.into_iter()
		.find(|(txid, outputs)| {
			*txid == funding_txo.txid && outputs.iter().any(|(idx, _)| *idx == funding_txo.index as u32)
		})
		.and_then(|(_, outputs)| {
			outputs
				.into_iter()
				.find(|(idx, _)| *idx == funding_txo.index as u32)
				.map(|(_, script)| script)
		})
		.unwrap()
}

#[test]
fn test_channel_teleport_happy_path_releases_holding_cell() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(3, 1);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	start_teleport(initiator, responder, channel_id, new_funding_txo);

	match get_event!(responder, Event::ChannelTeleport) {
		Event::ChannelTeleport {
			channel_id: ev_channel_id,
			user_channel_id: _,
			counterparty_node_id,
			new_funding_txo: ev_outpoint,
		} => {
			assert_eq!(ev_channel_id, channel_id);
			assert_eq!(counterparty_node_id, initiator_id);
			assert_eq!(ev_outpoint, new_funding_txo.into_bitcoin_outpoint());
		},
		_ => panic!(),
	}

	ack_teleport(initiator, responder, channel_id);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), original_funding_txo);
	assert!(monitor_watches_funding_txo(initiator, channel_id, new_funding_txo));
	assert!(monitor_watches_funding_txo(responder, channel_id, new_funding_txo));

	let payment_amount = 1_000_000;
	let (route, payment_hash, _, payment_secret) =
		get_route_and_payment_hash!(initiator, responder, payment_amount);
	let onion = RecipientOnionFields::secret_only(payment_secret, payment_amount);
	let payment_id = PaymentId(payment_hash.0);
	initiator.node.send_payment_with_route(route, payment_hash, onion, payment_id).unwrap();
	check_added_monitors(initiator, 0);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);

	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 2);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);
	assert_ne!(new_funding_txo, original_funding_txo);

	let update_add = get_htlc_update_msgs(initiator, &responder_id);
	check_added_monitors(initiator, 0);
	responder.node.handle_update_add_htlc(initiator_id, &update_add.update_add_htlcs[0]);
	do_commitment_signed_dance(responder, initiator, &update_add.commitment_signed, false, false);
	expect_and_process_pending_htlcs(responder, false);
	expect_payment_claimable!(responder, payment_hash, payment_secret, payment_amount);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

#[test]
fn test_channel_teleport_cancel_exits_quiescence() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let original_funding_txo = current_funding_txo(initiator, channel_id);

	start_teleport(initiator, responder, channel_id, test_outpoint(4, 0));
	let _ = get_event!(responder, Event::ChannelTeleport);

	responder.node.cancel_teleport(&channel_id, &initiator_id).unwrap();
	let teleport_abort =
		get_event_msg!(responder, MessageSendEvent::SendTeleportAbort, initiator_id);
	initiator.node.handle_teleport_abort(responder_id, &teleport_abort);

	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);

	send_payment(initiator, &[responder], 1_000_000);
}

#[test]
fn test_channel_teleport_disconnect_before_ack_sent_abandons_attempt() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let original_funding_txo = current_funding_txo(initiator, channel_id);

	start_teleport(initiator, responder, channel_id, test_outpoint(5, 0));
	let _ = get_event!(responder, Event::ChannelTeleport);
	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();

	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	let mut reconnect_args = ReconnectArgs::new(initiator, responder);
	reconnect_args.send_channel_ready = (true, true);
	reconnect_args.send_announcement_sigs = (true, true);
	reconnect_nodes(reconnect_args);

	let (route, payment_hash, _, payment_secret) =
		get_route_and_payment_hash!(initiator, responder, 1_000_000);
	let onion = RecipientOnionFields::secret_only(payment_secret, 1_000_000);
	let payment_id = PaymentId(payment_hash.0);
	initiator.node.send_payment_with_route(route, payment_hash, onion, payment_id).unwrap();
	check_added_monitors(initiator, 1);
	let _ = get_htlc_update_msgs(initiator, &responder_id);

	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
}

#[test]
fn test_channel_teleport_disconnect_after_ack_preserves_quiescence() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(6, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);
	ack_teleport(initiator, responder, channel_id);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), original_funding_txo);
	assert!(monitor_watches_funding_txo(initiator, channel_id, new_funding_txo));
	assert!(monitor_watches_funding_txo(responder, channel_id, new_funding_txo));

	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	let mut reconnect_args = ReconnectArgs::new(initiator, responder);
	reconnect_args.send_channel_ready = (true, true);
	reconnect_args.send_announcement_sigs = (true, true);
	reconnect_nodes(reconnect_args);

	for _ in 0..=DISCONNECT_PEER_AWAITING_RESPONSE_TICKS {
		initiator.node.timer_tick_occurred();
		responder.node.timer_tick_occurred();
	}
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
	assert!(responder.node.get_and_clear_pending_msg_events().is_empty());

	let (route, payment_hash, _, payment_secret) =
		get_route_and_payment_hash!(initiator, responder, 1_000_000);
	let onion = RecipientOnionFields::secret_only(payment_secret, 1_000_000);
	let payment_id = PaymentId(payment_hash.0);
	initiator.node.send_payment_with_route(route, payment_hash, onion, payment_id).unwrap();
	check_added_monitors(initiator, 0);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);
	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 2);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);

	let _ = get_htlc_update_msgs(initiator, &responder_id);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}
