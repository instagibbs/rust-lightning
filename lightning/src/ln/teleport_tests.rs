// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

//! Functional tests for the (Ark bridge-model) channel teleport state machine.
//!
//! These are a de-nonced adaptation of the donor branch's teleport tests. The bridge-model
//! new-funding spend is **stock ECDSA 2-of-2** (the `ArkChannel` funding output is stock P2WSH),
//! so the teleport flow carries **NO MuSig2 nonces** anywhere: the messages carry none, and the
//! new-scope `commitment_signed` exchange is the ordinary ECDSA path.
//!
//! The most safety-critical property exercised here is **commitment-number continuity** ([H1]):
//! the new `FundingScope` reuses the channel's funding keys and basepoints, so the per-commitment
//! point/secret derivation and the commitment-transaction-number sequence MUST continue across the
//! teleport and MUST NOT reset (resetting would re-reveal already-revealed per-commitment secrets
//! and pre-revoke the new scope — a catastrophic theft vector). `assert_commitment_number_*`
//! helpers below read the holder commitment-transaction-number straight off the channel and assert
//! it does not jump back to the initial value.

use crate::chain::transaction::OutPoint as FundingOutPoint;
use crate::events::Event;
use crate::ln::channel::DISCONNECT_PEER_AWAITING_RESPONSE_TICKS;
use crate::ln::channelmanager::PaymentId;
use crate::ln::functional_test_utils::*;
use crate::ln::msgs::{BaseMessageHandler, ChannelMessageHandler, MessageSendEvent};
use crate::ln::outbound_payment::RecipientOnionFields;
use crate::ln::types::ChannelId;
use crate::prelude::*;

use bitcoin::hashes::Hash;
use bitcoin::ScriptBuf;
use bitcoin::Txid;

fn test_outpoint(byte: u8, vout: u16) -> FundingOutPoint {
	FundingOutPoint { txid: Txid::from_byte_array([byte; 32]), index: vout }
}

/// Reads the holder commitment-transaction-number straight off the (funded) channel.
///
/// This is the load-bearing observable for the [H1] commitment-continuity property: it must be
/// preserved (continue counting down) across a teleport, never reset to `INITIAL_COMMITMENT_NUMBER`.
fn holder_commitment_number<'a, 'b, 'c>(node: &Node<'a, 'b, 'c>, channel_id: ChannelId) -> u64 {
	let per_peer_state = node.node.per_peer_state.read().unwrap();
	for (_, peer_state_mutex) in per_peer_state.iter() {
		let peer_state = peer_state_mutex.lock().unwrap();
		if let Some(chan) =
			peer_state.channel_by_id.get(&channel_id).and_then(|c| c.as_funded())
		{
			return chan.get_cur_holder_commitment_transaction_number();
		}
	}
	panic!("channel {channel_id} not found");
}

/// Reads the channel's `value_to_self_msat` for the holder side. Used to assert that a
/// `responder_value_removal_sat` reduces only the responder's balance.
fn value_to_self_msat<'a, 'b, 'c>(node: &Node<'a, 'b, 'c>, channel_id: ChannelId) -> u64 {
	let per_peer_state = node.node.per_peer_state.read().unwrap();
	for (_, peer_state_mutex) in per_peer_state.iter() {
		let peer_state = peer_state_mutex.lock().unwrap();
		if let Some(chan) =
			peer_state.channel_by_id.get(&channel_id).and_then(|c| c.as_funded())
		{
			return chan.funding.get_value_to_self_msat();
		}
	}
	panic!("channel {channel_id} not found");
}

fn start_teleport<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>, channel_id: ChannelId,
	new_funding_txo: FundingOutPoint,
) {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

	initiator.node.teleport_channel(&channel_id, &responder_id, new_funding_txo, 0).unwrap();

	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);

	let teleport_init = get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);
	responder.node.handle_teleport_init(initiator_id, &teleport_init);
}

fn ack_teleport<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>, channel_id: ChannelId,
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

	initiator.node.handle_commitment_signed(responder_id, &responder_commitment_signed);
	check_added_monitors(initiator, 1);

	responder.node.handle_commitment_signed(initiator_id, &initiator_commitment_signed);
	check_added_monitors(responder, 1);
}

fn current_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: ChannelId,
) -> FundingOutPoint {
	node.node
		.list_channels()
		.into_iter()
		.find(|channel| channel.channel_id == channel_id)
		.and_then(|channel| channel.funding_txo)
		.unwrap()
}

fn current_monitor_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: ChannelId,
) -> FundingOutPoint {
	get_monitor!(node, channel_id).get_funding_txo()
}

fn monitor_watches_funding_txo<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: ChannelId, funding_txo: FundingOutPoint,
) -> bool {
	get_monitor!(node, channel_id).get_outputs_to_watch().into_iter().any(|(txid, outputs)| {
		txid == funding_txo.txid
			&& outputs.iter().any(|(idx, _)| *idx == funding_txo.index as u32)
	})
}

fn funding_watch_script<'a, 'b, 'c>(
	node: &Node<'a, 'b, 'c>, channel_id: ChannelId, funding_txo: FundingOutPoint,
) -> ScriptBuf {
	get_monitor!(node, channel_id)
		.get_outputs_to_watch()
		.into_iter()
		.find(|(txid, outputs)| {
			*txid == funding_txo.txid
				&& outputs.iter().any(|(idx, _)| *idx == funding_txo.index as u32)
		})
		.and_then(|(_, outputs)| {
			outputs
				.into_iter()
				.find(|(idx, _)| *idx == funding_txo.index as u32)
				.map(|(_, script)| script)
		})
		.unwrap()
}

/// Happy path: open a channel, quiesce, then drive
/// `teleport_init` -> `teleport_ack` -> new-scope `commitment_signed` -> `teleport_complete` ->
/// `teleport_complete_ack`, with both peers promoting to the new funding scope.
///
/// Asserts the M4 correctness properties:
/// - **No MuSig2 nonce** is exchanged anywhere (the M3 messages carry none; the new-scope
///   commitment uses the stock-ECDSA `commitment_signed` path).
/// - **[H1] the commitment number CONTINUES across the scope** — the holder commitment-transaction
///   number is the same immediately before and after promotion (it does not reset).
/// - Promotion is **asymmetric** (responder promotes on `teleport_complete`, initiator on
///   `teleport_complete_ack`) and the channel **stays open** (no `channel_ready` is emitted).
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

	// [H1] Capture the commitment-transaction-number sequence position before the teleport so we
	// can assert it CONTINUES (rather than resetting) once the new scope is promoted.
	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);
	let responder_commitment_number_before = holder_commitment_number(responder, channel_id);

	// No MuSig2 nonce anywhere: exhaustively destructure each teleport message (no `..`). If a
	// nonce field were ever (re)introduced, these would fail to compile. The new-funding spend is
	// stock ECDSA 2-of-2, so the teleport protocol carries no nonces.
	let crate::ln::msgs::TeleportInit { channel_id: _, new_funding_txo: _, responder_value_removal_sat: _ } =
		crate::ln::msgs::TeleportInit {
			channel_id,
			new_funding_txo,
			responder_value_removal_sat: 0,
		};
	let crate::ln::msgs::TeleportAck { channel_id: _ } =
		crate::ln::msgs::TeleportAck { channel_id };
	let crate::ln::msgs::TeleportComplete { channel_id: _ } =
		crate::ln::msgs::TeleportComplete { channel_id };
	let crate::ln::msgs::TeleportCompleteAck { channel_id: _ } =
		crate::ln::msgs::TeleportCompleteAck { channel_id };
	let crate::ln::msgs::TeleportAbort { channel_id: _ } =
		crate::ln::msgs::TeleportAbort { channel_id };

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

	// Asymmetric promotion: the responder promotes on `teleport_complete` receipt; the initiator
	// is still on the old scope until it processes `teleport_complete_ack`.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);

	// [H1] The responder has just promoted to the new scope — its commitment-transaction-number
	// must be the continuation of the pre-teleport sequence, NOT reset to INITIAL_COMMITMENT_NUMBER.
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[H1] responder's commitment number must continue across the teleport, not reset",
	);

	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	let teleport_complete_ack =
		match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
			MessageSendEvent::SendTeleportCompleteAck { msg, .. } => msg,
			event => panic!("Unexpected event {event:?}"),
		};
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 2);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_ne!(new_funding_txo, original_funding_txo);

	// [H1] The initiator has now promoted as well — same continuity requirement.
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[H1] initiator's commitment number must continue across the teleport, not reset",
	);

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

/// A `teleport_abort` while the responder is still `AwaitingUserDecision` leaves both peers on the
/// OLD funding scope and exits quiescence so the channel keeps operating normally.
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

/// A disconnect after the responder dequeued (but before the initiator received) `teleport_ack`
/// abandons the attempt: `channel_reestablish` resolves the channel back onto the OLD scope and a
/// fresh teleport can be started afterwards.
#[test]
fn test_channel_teleport_disconnect_before_ack_sent_allows_fresh_attempt_after_reconnect() {
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
	let replacement_funding_txo = test_outpoint(7, 0);

	start_teleport(initiator, responder, channel_id, test_outpoint(5, 0));
	let _ = get_event!(responder, Event::ChannelTeleport);
	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();

	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	let mut reconnect_args = ReconnectArgs::new(initiator, responder);
	reconnect_args.send_channel_ready = (true, true);
	reconnect_args.send_announcement_sigs = (true, true);
	reconnect_nodes(reconnect_args);

	start_teleport(initiator, responder, channel_id, replacement_funding_txo);
	match get_event!(responder, Event::ChannelTeleport) {
		Event::ChannelTeleport {
			channel_id: ev_channel_id,
			user_channel_id: _,
			counterparty_node_id,
			new_funding_txo: ev_outpoint,
		} => {
			assert_eq!(ev_channel_id, channel_id);
			assert_eq!(counterparty_node_id, initiator_id);
			assert_eq!(ev_outpoint, replacement_funding_txo.into_bitcoin_outpoint());
		},
		_ => panic!(),
	}
	ack_teleport(initiator, responder, channel_id);

	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
}

/// A disconnect AFTER the new-scope `commitment_signed` exchange (so the pending teleport is
/// persistent) must carry BOTH funding scopes through reconnect: the channel stays quiesced and
/// the flow resumes to completion, with both peers promoting to the new scope.
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

	// [H1] Continuity baseline, captured before the teleport.
	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);
	let responder_commitment_number_before = holder_commitment_number(responder, channel_id);

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

	// [H1] Even across a disconnect/reconnect in the middle of the teleport, the commitment number
	// continues on both sides.
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[H1] initiator's commitment number must continue across teleport+reconnect, not reset",
	);
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[H1] responder's commitment number must continue across teleport+reconnect, not reset",
	);

	let _ = get_htlc_update_msgs(initiator, &responder_id);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// A disconnect after the responder dequeued (but before the initiator processed) the
/// `teleport_complete_ack` must complete the teleport once the `teleport_complete_ack` is resent on
/// reconnect — both peers end on the new scope.
#[test]
fn test_channel_teleport_disconnect_after_complete_ack_dequeued_before_delivery_completes_after_reconnect(
) {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(9, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);
	ack_teleport(initiator, responder, channel_id);

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);

	// The responder has queued `teleport_complete_ack`; drain it (simulating it being dequeued by
	// a `timer_tick`/send-path) so it is NOT delivered before the disconnect.
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 1, "{responder_events:?}");
	match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendTeleportCompleteAck { .. } => {},
		event => panic!("Unexpected event {event:?}"),
	};
	assert!(responder_events.is_empty());

	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	let initiator_init = crate::ln::msgs::Init {
		features: initiator.init_features(responder_id),
		networks: None,
		remote_network_address: None,
	};
	let responder_init = crate::ln::msgs::Init {
		features: responder.init_features(initiator_id),
		networks: None,
		remote_network_address: None,
	};
	initiator.node.peer_connected(responder_id, &responder_init, true).unwrap();
	let initiator_reestablish = get_chan_reestablish_msgs!(initiator, responder);
	assert_eq!(initiator_reestablish.len(), 1);
	responder.node.peer_connected(initiator_id, &initiator_init, false).unwrap();
	let responder_reestablish = get_chan_reestablish_msgs!(responder, initiator);
	assert_eq!(responder_reestablish.len(), 1);

	initiator.node.handle_channel_reestablish(responder_id, &responder_reestablish[0]);
	let _ = initiator.node.get_and_clear_pending_msg_events();
	responder.node.handle_channel_reestablish(initiator_id, &initiator_reestablish[0]);

	let responder_events = responder.node.get_and_clear_pending_msg_events();
	let teleport_complete_ack = responder_events
		.into_iter()
		.find_map(|event| match event {
			MessageSendEvent::SendTeleportCompleteAck { node_id, msg } => {
				assert_eq!(node_id, initiator_id);
				Some(msg)
			},
			_ => None,
		})
		.expect("teleport_complete_ack should be resent on reconnect");
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 1);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// Ark bridge: a `responder_value_removal_sat` declared at `teleport_channel()` time must reduce
/// ONLY the responder's `value_to_self` (the channel value shrinks by the same amount); the
/// initiator's balance is preserved. The new-scope spend is stock ECDSA, so the FULL ack /
/// `commitment_signed` / complete flow runs end-to-end here (no taproot-signing caveat).
#[test]
fn test_teleport_responder_value_removal_reduces_only_responder() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	// 1M sat channel with 500k sat pushed to the responder — leaves headroom on the responder's
	// value_to_self to pass the reserve check after a small removal.
	let channel_id =
		create_announced_chan_between_nodes_with_value(&nodes, 0, 1, 1_000_000, 500_000_000).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(3, 1);
	let removal_sat: u64 = 50_000;
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	let initiator_balance_before = value_to_self_msat(initiator, channel_id);
	let responder_balance_before = value_to_self_msat(responder, channel_id);
	// [H1] continuity baseline.
	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);
	let responder_commitment_number_before = holder_commitment_number(responder, channel_id);

	initiator
		.node
		.teleport_channel(&channel_id, &responder_id, new_funding_txo, removal_sat)
		.unwrap();

	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);

	let teleport_init =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);
	assert_eq!(
		teleport_init.responder_value_removal_sat, removal_sat,
		"TeleportInit msg must carry the removal value declared at teleport_channel()",
	);
	responder.node.handle_teleport_init(initiator_id, &teleport_init);
	let _ = get_event!(responder, Event::ChannelTeleport);

	ack_teleport(initiator, responder, channel_id);

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	// Single monitor update for the promotion (no pending payment to release a holding cell here).
	check_added_monitors(initiator, 1);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);

	// Only the responder's balance is reduced (by the removal); the initiator's is preserved.
	let initiator_balance_after = value_to_self_msat(initiator, channel_id);
	let responder_balance_after = value_to_self_msat(responder, channel_id);
	assert_eq!(
		initiator_balance_after, initiator_balance_before,
		"initiator's value_to_self must be preserved across a responder-side removal",
	);
	assert_eq!(
		responder_balance_before.saturating_sub(responder_balance_after),
		removal_sat * 1000,
		"responder's value_to_self must drop by exactly the removal amount",
	);

	// [H1] continuity holds even with a value-reducing teleport.
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[H1] initiator's commitment number must continue across a value-removal teleport",
	);
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[H1] responder's commitment number must continue across a value-removal teleport",
	);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// Ark bridge: the responder rejects (closes the channel on) a `TeleportInit` whose
/// `responder_value_removal_sat` would push the responder below its counterparty-selected reserve.
#[test]
fn test_teleport_responder_value_removal_rejected_when_below_reserve() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(4, 1);

	// Excessive removal: clearly above any reasonable responder balance.
	let removal_sat: u64 = 99_000_000;

	initiator
		.node
		.teleport_channel(&channel_id, &responder_id, new_funding_txo, removal_sat)
		.unwrap();

	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);

	let teleport_init =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);
	responder.node.handle_teleport_init(initiator_id, &teleport_init);

	let msg_events = responder.node.get_and_clear_pending_msg_events();
	assert!(
		msg_events.iter().any(|e| matches!(e, MessageSendEvent::HandleError { .. })),
		"expected responder to close-on-error for excessive removal, got: {msg_events:?}",
	);

	// Drain the close-on-error ChannelClosed event + monitor update so the test-utils'
	// end-of-test "no excess events / monitors" assertions are satisfied.
	let _ = responder.node.get_and_clear_pending_events();
	check_added_monitors(responder, 1);
}
