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
use crate::util::ser::Writeable;

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

	initiator.node.teleport_channel(&channel_id, &responder_id, new_funding_txo, 0, 0).unwrap();

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

/// Drive the teleport into the **asymmetric mid-exchange gap**: the responder processes the
/// initiator's new-scope `commitment_signed` and advances to the PERSISTENT `AwaitingRemoteComplete`,
/// but its own new-scope `commitment_signed` (CS_R) is NOT delivered to the initiator — so the
/// initiator stays in the persistent `AwaitingRemoteCommitmentSigned{is_initiator:true}`, awaiting a
/// CS_R it never received. Returns the held CS_R (the one-shot the responder emitted at `ack_teleport`
/// time, captured rather than delivered). This is exactly the window a post-`TeleportAck` mid-CS
/// disconnect lands in, and the one the responder's reconnect retransmission must close.
fn ack_teleport_into_gap<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>, channel_id: ChannelId,
) -> crate::ln::msgs::CommitmentSigned {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 2, "{responder_events:?}");
	let teleport_ack = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendTeleportAck { msg, .. } => msg,
		event => panic!("Unexpected event {event:?}"),
	};
	// Capture (do NOT deliver) the responder's new-scope `commitment_signed` (CS_R).
	let held_responder_cs =
		match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
			MessageSendEvent::UpdateHTLCs { updates, .. } => updates.commitment_signed[0].clone(),
			event => panic!("Unexpected event {event:?}"),
		};
	assert!(responder_events.is_empty());

	// The initiator processes `teleport_ack` and emits its own `commitment_signed`; deliver THAT to
	// the responder so the responder advances to `AwaitingRemoteComplete`. The initiator, never having
	// received CS_R, stays in `AwaitingRemoteCommitmentSigned{is_initiator:true}`.
	initiator.node.handle_teleport_ack(responder_id, &teleport_ack);
	let initiator_commitment_signed =
		get_htlc_update_msgs(initiator, &responder_id).commitment_signed[0].clone();
	responder.node.handle_commitment_signed(initiator_id, &initiator_commitment_signed);
	check_added_monitors(responder, 1);

	held_responder_cs
}

/// Reconnect two peers and drive the `channel_reestablish` exchange, returning the responder's
/// retransmitted new-scope `commitment_signed` (CS_R) if it sent one.
///
/// A responder in `AwaitingRemoteComplete` (CS_R already sent, initiator's `commitment_signed`
/// already processed, no `teleport_complete` yet) MUST retransmit CS_R on reconnect — it was dropped
/// on disconnect and is not covered by stock lost-commitment retransmission. This helper performs the
/// manual reestablish dance (rather than `reconnect_nodes`, which has no notion of the teleport CS_R)
/// and isolates that CS_R so callers can assert on it and feed it back in. It deliberately ignores
/// the ordinary reconnect churn (`channel_ready`/`announcement_signatures`/`channel_update`) that an
/// announced channel re-exchanges — those are not what these teleport tests are asserting.
fn teleport_reconnect_capturing_responder_cs<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>,
) -> Option<crate::ln::msgs::CommitmentSigned> {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

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

	// Deliver the reestablish messages.
	initiator.node.handle_channel_reestablish(responder_id, &responder_reestablish[0]);
	responder.node.handle_channel_reestablish(initiator_id, &initiator_reestablish[0]);

	// The kept initiator (still `AwaitingRemoteCommitmentSigned{is_initiator:true}` if it had not yet
	// processed CS_R, else already advanced) must not emit a stray teleport `commitment_signed`; it is
	// the responder that retransmits. Drain the initiator's reconnect churn and assert none of it is a
	// teleport-scope commitment.
	for event in initiator.node.get_and_clear_pending_msg_events() {
		if let MessageSendEvent::UpdateHTLCs { updates, .. } = &event {
			assert!(
				updates.commitment_signed.iter().all(|cs| cs.funding_txid.is_none()),
				"the initiator must not retransmit a new-scope teleport commitment_signed",
			);
		}
	}

	// Extract the responder's retransmitted CS_R (a teleport-scope `commitment_signed`, i.e. one
	// carrying a `funding_txid`), ignoring `channel_ready`/`announcement_signatures`/`channel_update`.
	let mut responder_cs = None;
	for event in responder.node.get_and_clear_pending_msg_events() {
		if let MessageSendEvent::UpdateHTLCs { node_id, updates, .. } = &event {
			assert_eq!(*node_id, initiator_id);
			let teleport_cs: Vec<_> = updates
				.commitment_signed
				.iter()
				.filter(|cs| cs.funding_txid.is_some())
				.cloned()
				.collect();
			if !teleport_cs.is_empty() {
				assert_eq!(teleport_cs.len(), 1, "exactly one CS_R expected");
				assert!(responder_cs.is_none(), "the responder retransmitted CS_R more than once");
				responder_cs = Some(teleport_cs[0].clone());
			}
		}
	}
	responder_cs
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
	let crate::ln::msgs::TeleportInit {
		channel_id: _,
		new_funding_txo: _,
		responder_value_removal_sat: _,
		initiator_value_removal_sat: _,
	} = crate::ln::msgs::TeleportInit {
		channel_id,
		new_funding_txo,
		responder_value_removal_sat: 0,
		initiator_value_removal_sat: 0,
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
			responder_value_removal_sat,
			initiator_value_removal_sat,
		} => {
			assert_eq!(ev_channel_id, channel_id);
			assert_eq!(counterparty_node_id, initiator_id);
			assert_eq!(ev_outpoint, new_funding_txo.into_bitcoin_outpoint());
			assert_eq!(responder_value_removal_sat, 0);
			assert_eq!(initiator_value_removal_sat, 0);
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
			responder_value_removal_sat,
			initiator_value_removal_sat,
		} => {
			assert_eq!(ev_channel_id, channel_id);
			assert_eq!(counterparty_node_id, initiator_id);
			assert_eq!(ev_outpoint, replacement_funding_txo.into_bitcoin_outpoint());
			assert_eq!(responder_value_removal_sat, 0);
			assert_eq!(initiator_value_removal_sat, 0);
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

	// Here the initiator had ALREADY processed the responder's CS_R before the disconnect (the
	// `ack_teleport` helper delivered it), so it is in `AwaitingLocalComplete`. On reconnect the
	// responder (in `AwaitingRemoteComplete`) still retransmits CS_R; that retransmission is a
	// DUPLICATE for the initiator and MUST be tolerated as a no-op. The outer teleport-CS drop in
	// `Channel::commitment_signed` dispatch catches it: a `commitment_signed` naming our in-flight
	// teleport's new scope that we have NOT yet promoted to (`AwaitingLocalComplete` is still
	// quiescent and still on the old scope). It is dropped there — before the normal
	// `commitment_signed` path, whose quiescent guard would otherwise reject it as a
	// "commitment_signed while quiescent" and force a disconnect.
	let responder_cs = teleport_reconnect_capturing_responder_cs(initiator, responder);
	let responder_cs =
		responder_cs.expect("responder must retransmit CS_R from AwaitingRemoteComplete");
	assert_eq!(responder_cs.funding_txid, Some(new_funding_txo.txid));
	initiator.node.handle_commitment_signed(responder_id, &responder_cs);
	// Idempotent: the duplicate CS_R is dropped (no new commitment), so no monitor update and — in
	// particular — NO disconnect/force-close (the duplicate is recognized before the quiescent guard).
	check_added_monitors(initiator, 0);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

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
		.teleport_channel(&channel_id, &responder_id, new_funding_txo, removal_sat, 0)
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
	// The responder's event must surface the initiator's declared removal — it is what the
	// handler verifies against the out-of-band-agreed value before acking.
	match get_event!(responder, Event::ChannelTeleport) {
		Event::ChannelTeleport { responder_value_removal_sat, .. } => {
			assert_eq!(
				responder_value_removal_sat, removal_sat,
				"ChannelTeleport event must carry the initiator's declared removal",
			);
		},
		_ => panic!(),
	}

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

/// Ark bridge: an `initiator_value_removal_sat` (the client-side `refresh` fee) declared at
/// `teleport_channel()` time must reduce ONLY the initiator's `value_to_self`, and a
/// `responder_value_removal_sat` declared alongside it ONLY the responder's; the channel value
/// shrinks by their sum. Runs the full flow end-to-end with both removals nonzero.
#[test]
fn test_teleport_both_side_value_removals_reduce_each_side() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	// 1M sat channel with 500k pushed to the responder — headroom on both sides for the removals
	// to pass the reserve checks.
	let channel_id =
		create_announced_chan_between_nodes_with_value(&nodes, 0, 1, 1_000_000, 500_000_000).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(3, 1);
	let responder_removal_sat: u64 = 50_000;
	let initiator_removal_sat: u64 = 7_000;
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	let initiator_balance_before = value_to_self_msat(initiator, channel_id);
	let responder_balance_before = value_to_self_msat(responder, channel_id);

	initiator
		.node
		.teleport_channel(
			&channel_id,
			&responder_id,
			new_funding_txo,
			responder_removal_sat,
			initiator_removal_sat,
		)
		.unwrap();

	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);

	let teleport_init =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);
	assert_eq!(teleport_init.responder_value_removal_sat, responder_removal_sat);
	assert_eq!(
		teleport_init.initiator_value_removal_sat, initiator_removal_sat,
		"TeleportInit must carry the initiator-side removal declared at teleport_channel()",
	);
	responder.node.handle_teleport_init(initiator_id, &teleport_init);
	match get_event!(responder, Event::ChannelTeleport) {
		Event::ChannelTeleport { responder_value_removal_sat, initiator_value_removal_sat, .. } => {
			assert_eq!(responder_value_removal_sat, responder_removal_sat);
			assert_eq!(
				initiator_value_removal_sat, initiator_removal_sat,
				"ChannelTeleport event must surface the initiator's declared removal",
			);
		},
		_ => panic!(),
	}

	ack_teleport(initiator, responder, channel_id);

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 1);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);

	// Each side's balance drops by exactly its own removal.
	let initiator_balance_after = value_to_self_msat(initiator, channel_id);
	let responder_balance_after = value_to_self_msat(responder, channel_id);
	assert_eq!(
		initiator_balance_before.saturating_sub(initiator_balance_after),
		initiator_removal_sat * 1000,
		"initiator's value_to_self must drop by exactly the initiator-side removal (the fee)",
	);
	assert_eq!(
		responder_balance_before.saturating_sub(responder_balance_after),
		responder_removal_sat * 1000,
		"responder's value_to_self must drop by exactly the responder-side removal",
	);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// Ark bridge: `teleport_channel()` pre-validates the initiator's OWN removal — one that exceeds
/// its balance or dips below the counterparty-selected reserve is refused at the API, before
/// anything goes on the wire.
#[test]
fn test_teleport_initiator_value_removal_rejected_at_api_when_below_reserve() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder_id = nodes[1].node.get_our_node_id();
	let new_funding_txo = test_outpoint(4, 1);

	// Excessive own-side removal: clearly above the initiator's balance.
	let err = initiator
		.node
		.teleport_channel(&channel_id, &responder_id, new_funding_txo, 0, 99_000_000)
		.unwrap_err();
	let err_str = format!("{err:?}");
	assert!(
		err_str.contains("initiator_value_removal_sat"),
		"expected an initiator-removal validation error, got: {err_str}",
	);
	// Nothing went on the wire.
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
}

/// Ark bridge: the responder rejects (closes the channel on) a crafted `TeleportInit` whose
/// `initiator_value_removal_sat` exceeds the initiator's balance — the symmetric protection to
/// the responder-removal reserve check, for a malicious initiator that bypasses its own API
/// pre-validation.
#[test]
fn test_teleport_initiator_value_removal_rejected_by_responder() {
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

	// Drive an honest teleport into quiescence, then deliver a CRAFTED teleport_init whose
	// initiator-side removal is absurd (the honest one is dropped).
	initiator.node.teleport_channel(&channel_id, &responder_id, new_funding_txo, 0, 0).unwrap();
	let stfu = get_event_msg!(initiator, MessageSendEvent::SendStfu, responder_id);
	responder.node.handle_stfu(initiator_id, &stfu);
	let stfu = get_event_msg!(responder, MessageSendEvent::SendStfu, initiator_id);
	initiator.node.handle_stfu(responder_id, &stfu);
	let honest_init =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportInit, responder_id);

	let crafted = crate::ln::msgs::TeleportInit {
		initiator_value_removal_sat: 99_000_000,
		..honest_init
	};
	responder.node.handle_teleport_init(initiator_id, &crafted);

	let msg_events = responder.node.get_and_clear_pending_msg_events();
	assert!(
		msg_events.iter().any(|e| matches!(e, MessageSendEvent::HandleError { .. })),
		"expected responder to close-on-error for excessive initiator removal, got: {msg_events:?}",
	);
	let _ = responder.node.get_and_clear_pending_events();
	check_added_monitors(responder, 1);
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
		.teleport_channel(&channel_id, &responder_id, new_funding_txo, removal_sat, 0)
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

/// [C1] A channel **serialized while a persistent teleport is in flight** (the new-scope
/// `commitment_signed` exchange has completed, so the channel is quiesced awaiting
/// `complete_teleport`/`teleport_complete`) must come back from a restart **still quiescent**, with
/// the `pending_teleport` intact, and resume the teleport to completion against the *continued*
/// commitment number.
///
/// Without the teleport guard in `FundedChannel::write`, the reload silently drops quiescence while
/// the persistent `pending_teleport` survives. Post-reconnect HTLC traffic could then advance the
/// commitment number, and a late promotion would emit `RenegotiatedFundingLocked` against stale
/// numbers — a cross-party commitment/monitor divergence on channel funds. This test pins all three
/// properties the fix restores:
/// - (a) the reloaded channel is **still quiescent** (a payment offered post-reconnect is held in
///   the holding cell rather than immediately turned into an on-wire `update_add`);
/// - (b) the `pending_teleport` **survives** (the teleport resumes and completes);
/// - (c) promotion stays gated on quiescence — the channel promotes against the **same (continued)**
///   commitment number, never an advanced one ([H1]).
#[test]
fn test_channel_teleport_persistent_state_survives_serialize_reload() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let (persister_0, persister_1);
	let (chain_monitor_0, chain_monitor_1);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let (node_0_reload, node_1_reload);
	let mut nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(11, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	// [H1] Continuity baseline, captured before the teleport.
	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);
	let responder_commitment_number_before = holder_commitment_number(responder, channel_id);

	// Drive the teleport through the new-scope `commitment_signed` exchange. The initiator is now
	// `AwaitingLocalComplete` and the responder `AwaitingRemoteComplete` — both PERSISTENT states,
	// both still quiesced, neither promoted yet.
	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);
	ack_teleport(initiator, responder, channel_id);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);

	// Serialize BOTH nodes (channelmanager + monitor) and reload them — i.e. a restart mid-teleport.
	let initiator_serialized = initiator.node.encode();
	let responder_serialized = responder.node.encode();
	let initiator_monitor = get_monitor!(initiator, channel_id).encode();
	let responder_monitor = get_monitor!(responder, channel_id).encode();

	reload_node!(
		nodes[0],
		&initiator_serialized,
		&[&initiator_monitor],
		persister_0,
		chain_monitor_0,
		node_0_reload
	);
	reload_node!(
		nodes[1],
		&responder_serialized,
		&[&responder_monitor],
		persister_1,
		chain_monitor_1,
		node_1_reload
	);
	let initiator = &nodes[0];
	let responder = &nodes[1];

	// The reloaded channels must still be on the OLD scope (no promotion happened across the
	// restart) and the [H1] commitment number must be unchanged.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[C1] the reloaded initiator's commitment number must not have advanced",
	);
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[C1] the reloaded responder's commitment number must not have advanced",
	);

	// On reconnect the reloaded responder (`AwaitingRemoteComplete`) retransmits its new-scope
	// `commitment_signed` (CS_R) — proving the retransmission survives a full RESTART, not just a live
	// disconnect. The reloaded initiator already processed CS_R before serialization (it is
	// `AwaitingLocalComplete`), so this is a DUPLICATE and must be tolerated as a no-op (no monitor
	// update, no disconnect).
	let responder_cs = teleport_reconnect_capturing_responder_cs(initiator, responder);
	let responder_cs =
		responder_cs.expect("reloaded responder must retransmit CS_R from AwaitingRemoteComplete");
	assert_eq!(responder_cs.funding_txid, Some(new_funding_txo.txid));
	initiator.node.handle_commitment_signed(responder_id, &responder_cs);
	check_added_monitors(initiator, 0);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	// A persistent teleport waits on a local `complete_teleport`, so reconnect must NOT trip the
	// awaiting-response disconnect timer.
	for _ in 0..=DISCONNECT_PEER_AWAITING_RESPONSE_TICKS {
		initiator.node.timer_tick_occurred();
		responder.node.timer_tick_occurred();
	}
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
	assert!(responder.node.get_and_clear_pending_msg_events().is_empty());

	// (a) STILL QUIESCENT: a payment offered now must be parked in the holding cell — a quiescent
	// channel does not emit a new `update_add`. Before the fix, the reload dropped quiescence and
	// this payment would immediately produce an on-wire `update_add`.
	let payment_amount = 1_000_000;
	let (route, payment_hash, payment_preimage, payment_secret) =
		get_route_and_payment_hash!(initiator, responder, payment_amount);
	let onion = RecipientOnionFields::secret_only(payment_secret, payment_amount);
	let payment_id = PaymentId(payment_hash.0);
	initiator.node.send_payment_with_route(route, payment_hash, onion, payment_id).unwrap();
	check_added_monitors(initiator, 0);
	assert!(
		initiator.node.get_and_clear_pending_msg_events().is_empty(),
		"[C1] reloaded channel must still be quiescent: the payment must be held, not sent",
	);

	// (b)+(c) The persistent teleport survived and resumes to completion. Promotion lands on the new
	// scope with the commitment number CONTINUED (never reset / advanced).
	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[C1]/[H1] responder must promote against the continued commitment number, not an advanced one",
	);

	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 2);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[C1]/[H1] initiator must promote against the continued commitment number, not an advanced one",
	);

	// The held payment is released by promotion (quiescence ended) and delivers on the new scope.
	let update_add = get_htlc_update_msgs(initiator, &responder_id);
	responder.node.handle_update_add_htlc(initiator_id, &update_add.update_add_htlcs[0]);
	do_commitment_signed_dance(responder, initiator, &update_add.commitment_signed, false, false);
	expect_and_process_pending_htlcs(responder, false);
	expect_payment_claimable!(responder, payment_hash, payment_secret, payment_amount);
	claim_payment(initiator, &[responder], payment_preimage);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// [I1] A disconnect in the **mid-CS-exchange window** — the responder has dequeued
/// `teleport_ack`+its new-scope `commitment_signed` (so it is
/// `AwaitingRemoteCommitmentSigned{is_initiator:false}`) and the initiator has sent its own
/// `commitment_signed` (so it is `AwaitingRemoteCommitmentSigned{is_initiator:true}`), but *neither*
/// has processed the other's `commitment_signed` and *neither* has promoted — must abort **cleanly
/// and symmetrically**: BOTH parties drop back to the OLD funding scope and the channel stays
/// usable (re-quiesce-able for a fresh teleport).
///
/// How the symmetric abort is achieved: the responder's `{is_initiator:false}` state is
/// **non-persistent** (it has not processed the initiator's `commitment_signed`, so a disconnect here
/// simply abandons the attempt — its reconnect `channel_reestablish` therefore advertises NO teleport
/// scope). The initiator's `{is_initiator:true}` state IS persistent (it must survive a disconnect in
/// the asymmetric window where the responder has already advanced to `AwaitingRemoteComplete`), but on
/// reconnect its reconcile gate sees the responder is no longer advertising the teleport scope and so
/// ABORTS locally — falling back to the old scope and exiting quiescence. Both ends thus converge on
/// the old scope. (Contrast `test_..._after_ack_preserves_quiescence`, where the responder DID reach
/// `AwaitingRemoteComplete`, re-advertises the scope, retransmits CS_R, and the teleport completes.)
#[test]
fn test_channel_teleport_disconnect_mid_commitment_exchange_aborts_symmetrically() {
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
	let replacement_funding_txo = test_outpoint(13, 0);

	start_teleport(initiator, responder, channel_id, test_outpoint(12, 0));
	let _ = get_event!(responder, Event::ChannelTeleport);

	// Drive to the mid-CS-exchange window WITHOUT either side processing the other's
	// `commitment_signed`:
	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();
	// Draining the responder's events advances it off `AwaitingTeleportAckSend` to
	// `AwaitingRemoteCommitmentSigned{is_initiator:false}` (non-persistent).
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 2, "{responder_events:?}");
	let teleport_ack = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendTeleportAck { msg, .. } => msg,
		event => panic!("Unexpected event {event:?}"),
	};
	// Hold (do NOT deliver) the responder's new-scope `commitment_signed`.
	match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::UpdateHTLCs { .. } => {},
		event => panic!("Unexpected event {event:?}"),
	};
	assert!(responder_events.is_empty());

	// The initiator processes `teleport_ack` and emits its own `commitment_signed`, landing in
	// `AwaitingRemoteCommitmentSigned{is_initiator:true}`.
	initiator.node.handle_teleport_ack(responder_id, &teleport_ack);
	// Drain (and hold) the initiator's `commitment_signed`. Neither CS has been delivered.
	let _initiator_commitment_signed =
		get_htlc_update_msgs(initiator, &responder_id).commitment_signed[0].clone();

	// Disconnect in this window.
	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	// Reconnect. With the symmetric-abort fix, BOTH sides treated this window as non-persistent, so
	// the teleport is abandoned and the channel is resolved back onto the OLD scope on reconnect.
	// (Before the fix the initiator would be stuck quiesced and `reconnect_nodes` would observe a
	// leftover quiescence/teleport state mismatch.)
	let mut reconnect_args = ReconnectArgs::new(initiator, responder);
	reconnect_args.send_channel_ready = (true, true);
	reconnect_args.send_announcement_sigs = (true, true);
	reconnect_nodes(reconnect_args);

	// Neither side should hold a lingering awaiting-response/teleport state that trips the
	// disconnect timer or emits stray messages.
	for _ in 0..=DISCONNECT_PEER_AWAITING_RESPONSE_TICKS {
		initiator.node.timer_tick_occurred();
		responder.node.timer_tick_occurred();
	}
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
	assert!(responder.node.get_and_clear_pending_msg_events().is_empty());

	// BOTH parties are back on the OLD funding scope — neither bricked.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);

	// The channel is fully usable: a normal payment flows...
	send_payment(initiator, &[responder], 1_000_000);

	// ...and it is re-quiesce-able — a fresh teleport can be started and acked end-to-end.
	start_teleport(initiator, responder, channel_id, replacement_funding_txo);
	match get_event!(responder, Event::ChannelTeleport) {
		Event::ChannelTeleport { new_funding_txo: ev_outpoint, .. } => {
			assert_eq!(ev_outpoint, replacement_funding_txo.into_bitcoin_outpoint());
		},
		_ => panic!(),
	}
	ack_teleport(initiator, responder, channel_id);
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);
}

/// [a]+[b] THE GAP this change closes. Drive the teleport into the asymmetric mid-CS window where the
/// responder reached the PERSISTENT `AwaitingRemoteComplete` but its new-scope `commitment_signed`
/// (CS_R) was never delivered, so the initiator is still in the PERSISTENT
/// `AwaitingRemoteCommitmentSigned{is_initiator:true}`. Disconnect there (dropping the in-flight
/// CS_R), reconnect, and assert:
///   [a] the responder RETRANSMITS CS_R on `channel_reestablish` (it is the production retransmission,
///       not any test shim, that carries the teleport forward);
///   [b] the kept initiator processes that CS_R, advances to `AwaitingLocalComplete`, and the teleport
///       COMPLETES in-place — both peers promote to the new scope, with [H1] commitment-number
///       continuity preserved and NO force-close.
#[test]
fn test_channel_teleport_responder_retransmits_cs_on_reconnect_kept_initiator_completes() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(21, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	// [H1] Continuity baseline.
	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);
	let responder_commitment_number_before = holder_commitment_number(responder, channel_id);

	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);

	// Reach the gap: responder is `AwaitingRemoteComplete`, initiator is still
	// `AwaitingRemoteCommitmentSigned{is_initiator:true}` (CS_R held, NOT delivered).
	let _held_cs = ack_teleport_into_gap(initiator, responder, channel_id);
	// Both still on the OLD scope; neither promoted.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);

	// Disconnect in the gap. The held CS_R is dropped (mirrors stock LDK dropping un-flushed message
	// events on `peer_disconnected`); the responder MUST regenerate it on reconnect.
	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);
	drop(_held_cs);

	// [a] Reconnect: the responder retransmits CS_R.
	let responder_cs = teleport_reconnect_capturing_responder_cs(initiator, responder);
	let responder_cs = responder_cs
		.expect("[a] responder must retransmit CS_R from AwaitingRemoteComplete on reconnect");
	assert_eq!(
		responder_cs.funding_txid,
		Some(new_funding_txo.txid),
		"[a] retransmitted CS_R must name the new (teleport) funding scope",
	);

	// [b] The kept initiator processes the retransmitted CS_R: this is a REAL (first) CS_R for it, so
	// it stages the new-scope monitor update and advances to `AwaitingLocalComplete`.
	initiator.node.handle_commitment_signed(responder_id, &responder_cs);
	check_added_monitors(initiator, 1);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	// The teleport completes IN-PLACE across the disconnect, driven entirely by production messages.
	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	// Responder promotes on `teleport_complete`; initiator still on old scope until complete_ack.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(
		holder_commitment_number(responder, channel_id),
		responder_commitment_number_before,
		"[H1] responder promotes against the continued commitment number",
	);

	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	// Just the promotion `RenegotiatedFundingLocked` here: unlike the happy path (where CS_R's
	// `RenegotiatedFunding` is still pending and applied together with the promotion, giving 2), we
	// already applied CS_R's monitor update above when the kept initiator processed the retransmission.
	check_added_monitors(initiator, 1);

	// Both peers promoted to the new scope.
	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_monitor_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[H1] initiator promotes against the continued commitment number, not a reset/advanced one",
	);

	// The channel is live on the new scope: a payment flows end-to-end.
	send_payment(initiator, &[responder], 1_000_000);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// [c] A duplicate / late CS_R must be tolerated once the initiator has already advanced. Reach the
/// gap, deliver CS_R so the initiator advances to `AwaitingLocalComplete`, then deliver the SAME CS_R
/// AGAIN (modelling the responder's unconditional reconnect retransmission landing on an initiator
/// that already processed the original). The duplicate must be a benign no-op: NO extra monitor
/// update, NO force-close/disconnect, and the teleport still completes normally afterward.
#[test]
fn test_channel_teleport_duplicate_cs_tolerated_when_initiator_already_advanced() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(22, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	let initiator_commitment_number_before = holder_commitment_number(initiator, channel_id);

	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);
	let held_cs = ack_teleport_into_gap(initiator, responder, channel_id);

	// Deliver CS_R once: the initiator advances to `AwaitingLocalComplete` (one monitor update).
	initiator.node.handle_commitment_signed(responder_id, &held_cs);
	check_added_monitors(initiator, 1);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	// Deliver the SAME CS_R again — a late/duplicate retransmission. It must be dropped: no monitor
	// update, and crucially NO `commitment_signed-while-quiescent` disconnect warning.
	initiator.node.handle_commitment_signed(responder_id, &held_cs);
	check_added_monitors(initiator, 0);
	assert!(
		initiator.node.get_and_clear_pending_msg_events().is_empty(),
		"a duplicate CS_R must not provoke any message (e.g. a disconnect warning)",
	);
	// Still on the old scope, commitment number unchanged — the duplicate changed nothing.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"a duplicate CS_R must not touch the commitment number",
	);

	// The teleport still completes normally from `AwaitingLocalComplete`.
	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);
	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	check_added_monitors(initiator, 1);

	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	assert_eq!(
		holder_commitment_number(initiator, channel_id),
		initiator_commitment_number_before,
		"[H1] promotion continues the commitment number even after a duplicate CS_R",
	);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// Asserts the responder is in the lingering, fully-promoted-but-not-yet-resolved
/// `AwaitingRemoteActivityAfterTeleportCompleteAckSend` state: it has sent `teleport_complete_ack`,
/// promoted `self.funding` to `new_funding_txo`, and CLEARED quiescence — and is now waiting for any
/// post-promotion message from the initiator to retire the lingering `pending_teleport`.
fn assert_responder_lingering_after_complete_ack<'a, 'b, 'c>(
	responder: &Node<'a, 'b, 'c>, channel_id: ChannelId, new_funding_txo: FundingOutPoint,
) {
	use crate::ln::channel::PendingTeleport;
	let per_peer_state = responder.node.per_peer_state.read().unwrap();
	for (_, peer_state_mutex) in per_peer_state.iter() {
		let peer_state = peer_state_mutex.lock().unwrap();
		if let Some(chan) = peer_state.channel_by_id.get(&channel_id).and_then(|c| c.as_funded()) {
			assert!(
				matches!(
					chan.pending_teleport(),
					Some(PendingTeleport::AwaitingRemoteActivityAfterTeleportCompleteAckSend {
						new_funding_txo: txo,
						..
					}) if *txo == new_funding_txo
				),
				"responder must be lingering in AwaitingRemoteActivityAfterTeleportCompleteAckSend \
				 with the promoted scope, was {:?}",
				chan.pending_teleport(),
			);
			// Already promoted: the live funding scope IS the new (pending-teleport) scope. (Read it
			// directly off the channel — calling `current_funding_txo` here would re-acquire the
			// `per_peer_state` lock we already hold.)
			assert_eq!(chan.funding.get_funding_txo(), Some(new_funding_txo));
			// Quiescence has been cleared on `teleport_complete_ack_sent`.
			assert!(
				!chan.is_quiescent(),
				"the lingering post-complete-ack state must NOT be quiescent",
			);
			return;
		}
	}
	panic!("channel {channel_id} not found");
}

/// Drives a teleport to FULL completion (both peers promote to `new_funding_txo`) and leaves the
/// responder in the lingering `AwaitingRemoteActivityAfterTeleportCompleteAckSend` state, awaiting
/// the initiator's first post-promotion traffic. Mirrors `test_channel_teleport_happy_path_*`'s
/// completion sequence; draining the responder's `SendTeleportCompleteAck` via
/// `get_and_clear_pending_msg_events` is what advances it onto the lingering state (and clears its
/// quiescence) — see `teleport_complete_ack_sent`.
fn complete_teleport_into_responder_lingering<'a, 'b, 'c>(
	initiator: &Node<'a, 'b, 'c>, responder: &Node<'a, 'b, 'c>, channel_id: ChannelId,
	new_funding_txo: FundingOutPoint,
) {
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();

	start_teleport(initiator, responder, channel_id, new_funding_txo);
	let _ = get_event!(responder, Event::ChannelTeleport);
	ack_teleport(initiator, responder, channel_id);

	initiator.node.complete_teleport(&channel_id, &responder_id).unwrap();
	let teleport_complete =
		get_event_msg!(initiator, MessageSendEvent::SendTeleportComplete, responder_id);
	responder.node.handle_teleport_complete(initiator_id, &teleport_complete);
	check_added_monitors(responder, 1);

	// Drain `SendTeleportCompleteAck`: this advances the responder off `AwaitingTeleportCompleteAckSend`
	// onto the lingering `AwaitingRemoteActivityAfterTeleportCompleteAckSend` (clearing quiescence).
	let teleport_complete_ack =
		get_event_msg!(responder, MessageSendEvent::SendTeleportCompleteAck, initiator_id);
	initiator.node.handle_teleport_complete_ack(responder_id, &teleport_complete_ack);
	// One monitor update: the promotion's `RenegotiatedFundingLocked`. (CS_R's `RenegotiatedFunding`
	// was already applied when the initiator processed CS_R inside `ack_teleport`; unlike the happy
	// path, there is no holding-cell payment that frees on promotion to add a second update.)
	check_added_monitors(initiator, 1);

	// Both peers are now on the new scope; the responder is lingering, awaiting post-promotion traffic.
	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_responder_lingering_after_complete_ack(responder, channel_id, new_funding_txo);
}

/// REGRESSION (review blind spot): a LEGITIMATE post-promotion `commitment_signed` from the initiator
/// must NOT be silently dropped while the responder lingers in
/// `AwaitingRemoteActivityAfterTeleportCompleteAckSend`.
///
/// After a teleport completes, BOTH peers have promoted `self.funding` to the new scope, but the
/// responder keeps a lingering `pending_teleport` until the initiator's first post-promotion message
/// proves it promoted too. In that window the responder's live funding txid EQUALS
/// `pending_teleport.new_funding_txo().txid`. The initiator (the funder) chooses `update_fee` +
/// `commitment_signed` as its first post-promotion traffic; `handle_update_fee` does NOT retire the
/// lingering teleport, so the `commitment_signed` arrives with the lingering state still set and
/// carrying `funding_txid == Some(new_scope)`.
///
/// The over-broad outer "duplicate teleport CS_R" drop matched purely on
/// `funding_txid == pending_teleport.new_funding_txo().txid` and SWALLOWED this legitimate CS — the
/// responder staged no monitor update and sent no RAA/CS, desyncing the channel. The narrowed drop
/// additionally requires the named scope to NOT be the current funding scope (it only fires for a
/// duplicate naming a not-yet-promoted pending scope), so this post-promotion CS now falls through to
/// the normal `commitment_signed` path and is processed.
#[test]
fn test_channel_teleport_post_promotion_commitment_signed_not_dropped_while_responder_lingers() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &[None, None]);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);
	let channel_id = create_announced_chan_between_nodes(&nodes, 0, 1).2;

	let initiator = &nodes[0];
	let responder = &nodes[1];
	let initiator_id = initiator.node.get_our_node_id();
	let responder_id = responder.node.get_our_node_id();
	let new_funding_txo = test_outpoint(24, 0);
	let original_funding_txo = current_funding_txo(initiator, channel_id);
	let original_funding_script = funding_watch_script(initiator, channel_id, original_funding_txo);

	complete_teleport_into_responder_lingering(initiator, responder, channel_id, new_funding_txo);

	// The initiator's FIRST post-promotion traffic is an `update_fee` + `commitment_signed` (the
	// funder bumps the feerate). `update_fee` does NOT clear the responder's lingering teleport.
	{
		let mut feerate_lock = chanmon_cfgs[0].fee_estimator.sat_per_kw.lock().unwrap();
		*feerate_lock += 250;
	}
	initiator.node.timer_tick_occurred();
	check_added_monitors(initiator, 1);
	let initiator_updates = get_htlc_update_msgs(initiator, &responder_id);
	let update_fee = initiator_updates.update_fee.expect("funder should emit an update_fee");
	let commitment_signed = initiator_updates.commitment_signed[0].clone();
	// The post-promotion CS names the NEW (now-current) scope — exactly the txid the lingering
	// `pending_teleport` carries, which is what the over-broad drop keyed on.
	assert_eq!(
		commitment_signed.funding_txid,
		Some(new_funding_txo.txid),
		"a post-promotion commitment_signed names the current (new) funding scope",
	);

	// Deliver `update_fee`: accepted, but the lingering teleport remains (handle_update_fee does not
	// retire it), so the responder is still in the over-broad drop's window.
	responder.node.handle_update_fee(initiator_id, &update_fee);
	assert_responder_lingering_after_complete_ack(responder, channel_id, new_funding_txo);

	// Deliver the post-promotion `commitment_signed`. It MUST be processed, not dropped:
	//  - the responder stages a monitor update, and
	//  - replies with `revoke_and_ack` (+ its own `commitment_signed`).
	// On the un-narrowed (buggy) drop this CS is swallowed: NO monitor update, NO reply -> the assert
	// below fails (and the channel is desynced).
	responder.node.handle_commitment_signed(initiator_id, &commitment_signed);
	// The CS is PROCESSED (not dropped): a monitor update is staged. On the buggy (un-narrowed) drop
	// this is 0 — the CS is silently swallowed.
	check_added_monitors(responder, 1);

	// Post-promotion traffic also retired the responder's lingering teleport (via
	// `note_counterparty_post_teleport_complete_ack_activity` on the successful CS handling).
	{
		let per_peer_state = responder.node.per_peer_state.read().unwrap();
		for (_, peer_state_mutex) in per_peer_state.iter() {
			let peer_state = peer_state_mutex.lock().unwrap();
			if let Some(chan) =
				peer_state.channel_by_id.get(&channel_id).and_then(|c| c.as_funded())
			{
				assert!(
					chan.pending_teleport().is_none(),
					"post-promotion CS must retire the lingering teleport, was {:?}",
					chan.pending_teleport(),
				);
			}
		}
	}

	// The responder replies to the post-promotion CS with `revoke_and_ack` + its own
	// `commitment_signed`. (It also retransmits a now-redundant `teleport_complete_ack`: that resend
	// is generated while resuming from the staged monitor update, in the brief window before the
	// lingering teleport is retired. It is a benign duplicate — the initiator has already promoted and
	// ignores it; we deliver it below to prove so.)
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 3, "{responder_events:?}");
	let responder_raa = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendRevokeAndACK { msg, .. } => msg,
		event => panic!("Unexpected event {event:?}"),
	};
	let responder_cs = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::UpdateHTLCs { updates, .. } => {
			assert_eq!(updates.commitment_signed.len(), 1);
			updates.commitment_signed[0].clone()
		},
		event => panic!("Unexpected event {event:?}"),
	};
	let redundant_complete_ack =
		match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
			MessageSendEvent::SendTeleportCompleteAck { msg, .. } => msg,
			event => panic!("Unexpected event {event:?}"),
		};
	assert!(responder_events.is_empty());

	// The redundant `teleport_complete_ack` is a benign no-op on the already-promoted initiator.
	initiator.node.handle_teleport_complete_ack(responder_id, &redundant_complete_ack);
	check_added_monitors(initiator, 0);
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());

	// Complete the commitment dance so the fee update commits on both sides — proving the channel is
	// fully in sync (not silently desynced by a dropped CS).
	initiator.node.handle_revoke_and_ack(responder_id, &responder_raa);
	check_added_monitors(initiator, 1);
	initiator.node.handle_commitment_signed(responder_id, &responder_cs);
	check_added_monitors(initiator, 1);
	let initiator_raa = get_event_msg!(initiator, MessageSendEvent::SendRevokeAndACK, responder_id);
	responder.node.handle_revoke_and_ack(initiator_id, &initiator_raa);
	check_added_monitors(responder, 1);

	// No stray messages pending, and a payment still flows end-to-end on the new scope.
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
	assert!(responder.node.get_and_clear_pending_msg_events().is_empty());
	assert_eq!(current_funding_txo(initiator, channel_id), new_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), new_funding_txo);
	send_payment(initiator, &[responder], 1_000_000);

	initiator
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script.clone());
	responder
		.chain_source
		.remove_watched_txn_and_outputs(original_funding_txo, original_funding_script);
}

/// [d] The reconnect ABORT path stays clean. Reach the asymmetric gap (initiator persistent
/// `AwaitingRemoteCommitmentSigned{is_initiator:true}`, CS_R undelivered), but the responder NEVER
/// reached `AwaitingRemoteComplete` — model the responder simply dropping the teleport (it forgets the
/// pending teleport, as a non-persistent `{is_initiator:false}` disconnect would). On reconnect the
/// responder's `channel_reestablish` therefore carries NO `teleport_funding_txid`, so the kept
/// initiator's reconcile gate must ABORT: drop the teleport, exit quiescence, and fall back to the old
/// scope — leaving a fully usable channel and NO force-close.
#[test]
fn test_channel_teleport_reconnect_aborts_when_peer_drops_teleport() {
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

	start_teleport(initiator, responder, channel_id, test_outpoint(23, 0));
	let _ = get_event!(responder, Event::ChannelTeleport);

	// Bring only the INITIATOR into the persistent mid-exchange state: it processes `teleport_ack`
	// and sends its `commitment_signed`, landing in `AwaitingRemoteCommitmentSigned{is_initiator:true}`.
	responder.node.ack_teleport(&channel_id, &initiator_id).unwrap();
	let mut responder_events = responder.node.get_and_clear_pending_msg_events();
	assert_eq!(responder_events.len(), 2, "{responder_events:?}");
	let teleport_ack = match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::SendTeleportAck { msg, .. } => msg,
		event => panic!("Unexpected event {event:?}"),
	};
	// Drop the responder's CS_R (never delivered) AND have the responder forget the teleport — the
	// non-persistent `{is_initiator:false}` window: on its own disconnect it abandons the attempt.
	match remove_first_msg_event_to_node(&initiator_id, &mut responder_events) {
		MessageSendEvent::UpdateHTLCs { .. } => {},
		event => panic!("Unexpected event {event:?}"),
	};
	initiator.node.handle_teleport_ack(responder_id, &teleport_ack);
	let _initiator_cs = get_htlc_update_msgs(initiator, &responder_id).commitment_signed[0].clone();

	initiator.node.peer_disconnected(responder_id);
	responder.node.peer_disconnected(initiator_id);

	// On reconnect the responder advertises NO teleport scope (its `{is_initiator:false}` state was
	// non-persistent and dropped on disconnect). The kept initiator's gate must abort to the old scope.
	let responder_cs = teleport_reconnect_capturing_responder_cs(initiator, responder);
	assert!(
		responder_cs.is_none(),
		"[d] responder must not retransmit CS_R when it never reached AwaitingRemoteComplete",
	);

	// Neither side holds a lingering quiescence/teleport state that trips the disconnect timer.
	for _ in 0..=DISCONNECT_PEER_AWAITING_RESPONSE_TICKS {
		initiator.node.timer_tick_occurred();
		responder.node.timer_tick_occurred();
	}
	assert!(initiator.node.get_and_clear_pending_msg_events().is_empty());
	assert!(responder.node.get_and_clear_pending_msg_events().is_empty());

	// Both ends are back on the OLD funding scope — neither bricked, no force-close.
	assert_eq!(current_funding_txo(initiator, channel_id), original_funding_txo);
	assert_eq!(current_funding_txo(responder, channel_id), original_funding_txo);

	// The channel is fully usable: a normal payment flows end-to-end.
	send_payment(initiator, &[responder], 1_000_000);
}
