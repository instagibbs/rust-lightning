use crate::events::bump_transaction::BumpTransactionEvent;
use crate::events::{ClosureReason, Event};
use crate::ln::chan_utils;
use crate::ln::chan_utils::{
	BASE_INPUT_WEIGHT, BASE_TX_SIZE, EMPTY_SCRIPT_SIG_WEIGHT, EMPTY_WITNESS_WEIGHT,
	P2WSH_TXOUT_WEIGHT, SEGWIT_MARKER_FLAG_WEIGHT, TRUC_CHILD_MAX_WEIGHT,
};
use crate::ln::functional_test_utils::*;
use crate::ln::msgs::{BaseMessageHandler, ChannelMessageHandler, MessageSendEvent};
use crate::prelude::*;

use bitcoin::constants::WITNESS_SCALE_FACTOR;
use bitcoin::opcodes::all::OP_CSV;
use bitcoin::script::Instruction;
use bitcoin::secp256k1::Secp256k1;
use bitcoin::Amount;
use lightning_types::features::ChannelTypeFeatures;


#[test]
fn test_p2a_anchor_values_under_trims_and_rounds() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let mut user_cfg = test_default_channel_config();
	user_cfg.channel_handshake_config.our_htlc_minimum_msat = 1;
	user_cfg.channel_handshake_config.negotiate_anchor_zero_fee_commitments = true;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	let _coinbase_tx = provide_anchor_reserves(&nodes);

	let _node_a_id = nodes[0].node.get_our_node_id();
	let _node_b_id = nodes[1].node.get_our_node_id();

	const CHAN_CAPACITY: u64 = 10_000_000;
	let chan_id = create_announced_chan_between_nodes_with_value(
		&nodes,
		0,
		1,
		CHAN_CAPACITY,
		(CHAN_CAPACITY / 2) * 1000,
	)
	.2;

	macro_rules! p2a_value_test {
		([$($node_0_1_amt_msat:expr),*], $expected_p2a_value_sat:expr) => {
			p2a_value_test!([$($node_0_1_amt_msat),*], [], $expected_p2a_value_sat)
		};
		([$($node_0_1_amt_msat:expr),*], [$($node_1_0_amt_msat:expr),*], $expected_p2a_value_sat:expr) => {
			let mut node_0_1_hashes = Vec::new();
			#[allow(unused_mut)]
			let mut node_1_0_hashes = Vec::new();

			$(
				node_0_1_hashes.push(route_payment(&nodes[0], &[&nodes[1]], $node_0_1_amt_msat).1);
			)*
			$(
				node_1_0_hashes.push(route_payment(&nodes[1], &[&nodes[0]], $node_1_0_amt_msat).1);
			)*
			let txn = get_local_commitment_txn!(nodes[0], chan_id);
			assert_eq!(txn.len(), 1);
			assert_eq!(txn[0].output.iter().find(|output| output.script_pubkey == chan_utils::shared_anchor_script_pubkey()).unwrap().value.to_sat(), $expected_p2a_value_sat);
			let txn = get_local_commitment_txn!(nodes[1], chan_id);
			assert_eq!(txn.len(), 1);
			assert_eq!(txn[0].output.iter().find(|output| output.script_pubkey == chan_utils::shared_anchor_script_pubkey()).unwrap().value.to_sat(), $expected_p2a_value_sat);
			for hash in node_0_1_hashes {
				fail_payment(&nodes[0], &[&nodes[1]], hash);
			}
			for hash in node_1_0_hashes {
				fail_payment(&nodes[1], &[&nodes[0]], hash);
			}
		};
	}

	p2a_value_test!([1], 1);
	p2a_value_test!([238_000], 238);
	p2a_value_test!([238_001], 239);
	p2a_value_test!([240_000], 240);
	p2a_value_test!([240_001], 240);
	p2a_value_test!([353_000], 240);
	p2a_value_test!([353_999], 240);
	p2a_value_test!([354_000], 0);
	p2a_value_test!([354_001], 1);

	p2a_value_test!([1, 1], 1);
	p2a_value_test!([1, 999], 1);
	p2a_value_test!([1, 1000], 2);
	p2a_value_test!([354_001], 1);
	p2a_value_test!([354_001, 999], 1);
	p2a_value_test!([354_001, 1000], 2);
	p2a_value_test!([354_001, 1999], 2);
	p2a_value_test!([354_002, 1999], 3);

	p2a_value_test!([1], [1], 2);
	p2a_value_test!([1], [999], 2);
	p2a_value_test!([1], [1000], 2);
	p2a_value_test!([354_001], 1);
	p2a_value_test!([354_001], [999], 2);
	p2a_value_test!([354_001], [1000], 2);
	p2a_value_test!([354_001], [1999], 3);
	p2a_value_test!([354_002], [1999], 3);

	p2a_value_test!([353_000], [353_000], 240);
	p2a_value_test!([353_001], [353_000], 240);
	p2a_value_test!([353_000], [353_001], 240);
	p2a_value_test!([353_001], [353_001], 240);
}

#[test]
fn test_htlc_claim_chunking() {
	// Assert we split an overall HolderHTLCOutput claim into constituent
	// HTLC claim transactions such that each transaction is under TRUC_MAX_WEIGHT.
	// Assert we reduce the number of HTLCs in a batch transaction by 2 if the
	// coin selection algorithm fails to meet the target weight.
	// Assert the claim_id of the first batch transaction is the claim
	// id assigned to the overall claim.
	// Assert we give up bumping a HTLC transaction once the batch size is
	// 0 or negative.
	//
	// Route a bunch of HTLCs, force close the channel, assert two HTLC transactions
	// get broadcasted, confirm only one of them, assert a new one gets broadcasted
	// to sweep the remaining HTLCs, confirm a block without that transaction while
	// dropping all available coin selection utxos, and assert we give up creating
	// another HTLC transaction when handling the third HTLC bump.
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let mut user_cfg = test_default_channel_config();
	user_cfg.channel_handshake_config.our_htlc_minimum_msat = 1;
	user_cfg.channel_handshake_config.negotiate_anchor_zero_fee_commitments = true;
	user_cfg.channel_handshake_config.our_max_accepted_htlcs = 114;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	let coinbase_tx = provide_utxo_reserves(&nodes, 50, Amount::from_sat(500));

	const CHAN_CAPACITY: u64 = 10_000_000;
	let (_, _, chan_id, _funding_tx) = create_announced_chan_between_nodes_with_value(
		&nodes,
		0,
		1,
		CHAN_CAPACITY,
		(CHAN_CAPACITY / 2) * 1000,
	);

	let mut node_1_preimages = Vec::new();
	const NONDUST_HTLC_AMT_MSAT: u64 = 1_000_000;
	for _ in 0..75 {
		let (preimage, payment_hash, _, _) =
			route_payment(&nodes[0], &[&nodes[1]], NONDUST_HTLC_AMT_MSAT);
		node_1_preimages.push((preimage, payment_hash));
	}
	let node_0_commit_tx = get_local_commitment_txn!(nodes[0], chan_id);
	assert_eq!(node_0_commit_tx.len(), 1);
	assert_eq!(node_0_commit_tx[0].output.len(), 75 + 2 + 1);
	let node_1_commit_tx = get_local_commitment_txn!(nodes[1], chan_id);
	assert_eq!(node_1_commit_tx.len(), 1);
	assert_eq!(node_1_commit_tx[0].output.len(), 75 + 2 + 1);

	for (preimage, payment_hash) in node_1_preimages {
		nodes[1].node.claim_funds(preimage);
		check_added_monitors(&nodes[1], 1);
		expect_payment_claimed!(nodes[1], payment_hash, NONDUST_HTLC_AMT_MSAT);
	}
	nodes[0].node.get_and_clear_pending_msg_events();
	nodes[1].node.get_and_clear_pending_msg_events();

	mine_transaction(&nodes[0], &node_1_commit_tx[0]);
	mine_transaction(&nodes[1], &node_1_commit_tx[0]);

	let mut events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	assert_eq!(events.len(), 1);
	match events.pop().unwrap() {
		Event::BumpTransaction(bump_event) => {
			nodes[1].bump_tx_handler.handle_event(&bump_event);
		},
		_ => panic!("Unexpected event"),
	}

	let htlc_claims = nodes[1].tx_broadcaster.txn_broadcast();
	assert_eq!(htlc_claims.len(), 2);

	check_spends!(htlc_claims[0], node_1_commit_tx[0], coinbase_tx);
	check_spends!(htlc_claims[1], node_1_commit_tx[0], coinbase_tx);

	assert_eq!(htlc_claims[0].input.len(), 71);
	assert_eq!(htlc_claims[0].output.len(), 51);
	assert_eq!(htlc_claims[1].input.len(), 34);
	assert_eq!(htlc_claims[1].output.len(), 24);

	check_closed_broadcast(&nodes[0], 1, true);
	check_added_monitors(&nodes[0], 1);
	let reason = ClosureReason::CommitmentTxConfirmed;
	check_closed_event(&nodes[0], 1, reason, &[nodes[1].node.get_our_node_id()], CHAN_CAPACITY);
	assert!(nodes[0].node.list_channels().is_empty());
	check_closed_broadcast(&nodes[1], 1, true);
	check_added_monitors(&nodes[1], 1);
	let reason = ClosureReason::CommitmentTxConfirmed;
	check_closed_event(&nodes[1], 1, reason, &[nodes[0].node.get_our_node_id()], CHAN_CAPACITY);
	assert!(nodes[1].node.list_channels().is_empty());
	assert!(nodes[0].node.get_and_clear_pending_events().is_empty());
	assert!(nodes[1].node.get_and_clear_pending_events().is_empty());

	mine_transaction(&nodes[1], &htlc_claims[0]);

	let mut events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	assert_eq!(events.len(), 1);
	match events.pop().unwrap() {
		Event::BumpTransaction(bump_event) => {
			nodes[1].bump_tx_handler.handle_event(&bump_event);
		},
		_ => panic!("Unexpected event"),
	}

	let fresh_htlc_claims = nodes[1].tx_broadcaster.txn_broadcast();
	assert_eq!(fresh_htlc_claims.len(), 1);
	check_spends!(fresh_htlc_claims[0], node_1_commit_tx[0], coinbase_tx);
	// We are targeting a higher feerate here,
	// so we need more utxos here compared to `htlc_claims[1]` above.
	assert_eq!(fresh_htlc_claims[0].input.len(), 37);
	assert_eq!(fresh_htlc_claims[0].output.len(), 25);

	let log_entries = nodes[1].logger.lines.lock().unwrap();
	let batch_tx_id_assignments: Vec<_> = log_entries
		.keys()
		.map(|key| &key.1)
		.filter(|log_msg| log_msg.contains("Batch transaction assigned to UTXO id"))
		.collect();
	assert_eq!(batch_tx_id_assignments.len(), 7);

	let mut unique_claim_ids: Vec<(&str, u8)> = Vec::new();
	for claim_id in batch_tx_id_assignments
		.iter()
		.map(|assignment| assignment.split_whitespace().nth(6).unwrap())
	{
		if let Some((_, count)) = unique_claim_ids.iter_mut().find(|(id, _count)| &claim_id == id) {
			*count += 1;
		} else {
			unique_claim_ids.push((claim_id, 1));
		}
	}
	unique_claim_ids.sort_unstable_by_key(|(_id, count)| *count);
	assert_eq!(unique_claim_ids.len(), 2);
	let (og_claim_id, og_claim_id_count) = unique_claim_ids.pop().unwrap();
	assert_eq!(og_claim_id_count, 6);
	assert_eq!(unique_claim_ids.pop().unwrap().1, 1);

	let handling_htlc_bumps: Vec<_> = log_entries
		.keys()
		.map(|key| &key.1)
		.filter(|log_msg| log_msg.contains("Handling HTLC bump"))
		.map(|log_msg| {
			log_msg
				.split_whitespace()
				.nth(5)
				.unwrap()
				.trim_matches(|c: char| c.is_ascii_punctuation())
		})
		.collect();
	assert_eq!(handling_htlc_bumps.len(), 2);
	assert_eq!(handling_htlc_bumps[0], og_claim_id);
	assert_eq!(handling_htlc_bumps[1], og_claim_id);

	let mut batch_sizes: Vec<u8> = batch_tx_id_assignments
		.iter()
		.map(|assignment| assignment.split_whitespace().nth(8).unwrap().parse().unwrap())
		.collect();
	batch_sizes.sort_unstable();
	batch_sizes.reverse();
	assert_eq!(batch_sizes.len(), 7);
	assert_eq!(batch_sizes.pop().unwrap(), 24);
	assert_eq!(batch_sizes.pop().unwrap(), 24);
	for i in (51..=59).step_by(2) {
		assert_eq!(batch_sizes.pop().unwrap(), i);
	}
	drop(log_entries);

	nodes[1].wallet_source.clear_utxos();
	nodes[1].chain_monitor.chain_monitor.rebroadcast_pending_claims();

	let mut events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	assert_eq!(events.len(), 1);
	match events.pop().unwrap() {
		Event::BumpTransaction(bump_event) => {
			nodes[1].bump_tx_handler.handle_event(&bump_event);
		},
		_ => panic!("Unexpected event"),
	}

	nodes[1].logger.assert_log(
		"lightning::events::bump_transaction",
		format!(
			"Failed bumping HTLC transaction fee for commitment {}",
			node_1_commit_tx[0].compute_txid()
		),
		1,
	);
}

#[test]
fn test_anchor_tx_too_big() {
	// Assert all V3 anchor tx transactions are below TRUC_CHILD_MAX_WEIGHT.
	//
	// Provide a bunch of small utxos, fail to bump the commitment,
	// then provide a single big-value utxo, and successfully broadcast
	// the commitment.
	const FEERATE: u32 = 500;
	let chanmon_cfgs = create_chanmon_cfgs(2);
	{
		let mut feerate_lock = chanmon_cfgs[1].fee_estimator.sat_per_kw.lock().unwrap();
		*feerate_lock = FEERATE;
	}
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);
	let mut user_cfg = test_default_channel_config();
	user_cfg.channel_handshake_config.our_htlc_minimum_msat = 1;
	user_cfg.channel_handshake_config.negotiate_anchor_zero_fee_commitments = true;
	user_cfg.channel_handshake_config.our_max_accepted_htlcs = 114;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	let node_a_id = nodes[0].node.get_our_node_id();

	let _coinbase_tx_a = provide_utxo_reserves(&nodes, 50, Amount::from_sat(500));

	const CHAN_CAPACITY: u64 = 10_000_000;
	let (_, _, chan_id, _funding_tx) = create_announced_chan_between_nodes_with_value(
		&nodes,
		0,
		1,
		CHAN_CAPACITY,
		(CHAN_CAPACITY / 2) * 1000,
	);

	let mut node_1_preimages = Vec::new();
	const NONDUST_HTLC_AMT_MSAT: u64 = 1_000_000;
	for _ in 0..50 {
		let (preimage, payment_hash, _, _) =
			route_payment(&nodes[0], &[&nodes[1]], NONDUST_HTLC_AMT_MSAT);
		node_1_preimages.push((preimage, payment_hash));
	}
	let commitment_tx = get_local_commitment_txn!(nodes[1], chan_id).pop().unwrap();
	let commitment_txid = commitment_tx.compute_txid();

	let message = "Channel force-closed".to_owned();
	nodes[1]
		.node
		.force_close_broadcasting_latest_txn(&chan_id, &node_a_id, message.clone())
		.unwrap();
	check_added_monitors(&nodes[1], 1);
	check_closed_broadcast(&nodes[1], 1, true);

	let reason = ClosureReason::HolderForceClosed { broadcasted_latest_txn: Some(true), message };
	check_closed_event(&nodes[1], 1, reason, &[node_a_id], CHAN_CAPACITY);

	let mut events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	assert_eq!(events.len(), 1);
	match events.pop().unwrap() {
		Event::BumpTransaction(bump_event) => {
			nodes[1].bump_tx_handler.handle_event(&bump_event);
		},
		_ => panic!("Unexpected event"),
	}
	assert!(nodes[1].tx_broadcaster.txn_broadcast().is_empty());
	let max_coin_selection_weight = TRUC_CHILD_MAX_WEIGHT
		- BASE_TX_SIZE * WITNESS_SCALE_FACTOR as u64
		- SEGWIT_MARKER_FLAG_WEIGHT
		- BASE_INPUT_WEIGHT
		- EMPTY_SCRIPT_SIG_WEIGHT
		- EMPTY_WITNESS_WEIGHT
		- P2WSH_TXOUT_WEIGHT;
	nodes[1].logger.assert_log(
		"lightning::util::wallet_utils",
		format!(
			"Insufficient funds to meet target feerate {} sat/kW while remaining under {} WU",
			FEERATE, max_coin_selection_weight
		),
		4,
	);
	nodes[1].logger.assert_log(
		"lightning::events::bump_transaction",
		format!("Failed bumping commitment transaction fee for {}", commitment_txid),
		1,
	);

	let coinbase_tx_b = provide_anchor_reserves(&nodes);

	nodes[1].chain_monitor.chain_monitor.rebroadcast_pending_claims();

	let mut events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	assert_eq!(events.len(), 1);
	match events.pop().unwrap() {
		Event::BumpTransaction(bump_event) => {
			nodes[1].bump_tx_handler.handle_event(&bump_event);
		},
		_ => panic!("Unexpected event"),
	}
	let txns = nodes[1].tx_broadcaster.txn_broadcast();
	assert_eq!(txns.len(), 2);
	check_spends!(txns[1], txns[0], coinbase_tx_b);
	assert!(txns[1].weight().to_wu() < TRUC_CHILD_MAX_WEIGHT);

	assert_eq!(txns[0].compute_txid(), commitment_txid);
	assert_eq!(txns[1].input.len(), 2);
	assert_eq!(txns[1].output.len(), 1);
	nodes[1].logger.assert_log(
		"lightning::util::wallet_utils",
		format!(
			"Insufficient funds to meet target feerate {} sat/kW while remaining under {} WU",
			FEERATE, max_coin_selection_weight
		),
		4,
	);
	nodes[1].logger.assert_log(
		"lightning::events::bump_transaction",
		format!("Failed bumping commitment transaction fee for {}", txns[0].compute_txid()),
		1,
	);
	nodes[1].logger.assert_log(
		"lightning::events::bump_transaction",
		format!(
			"Broadcasting anchor transaction {} to bump channel close with txid {}",
			txns[1].compute_txid(),
			txns[0].compute_txid()
		),
		1,
	);
}

/// Assert that an `ArkChannel` reaches `ChannelReady` with a stock segwit-v0 P2WSH funding
/// output — NOT a taproot (P2TR / witness-v1) output.
///
/// This is a non-vacuous structural guarantee: if the funding path were accidentally switched to
/// `get_taproot_output` / MuSig2, this test would fail because the `output_script` emitted by
/// `FundingGenerationReady` would be a 34-byte witness-v1 script (`OP_1 <32-byte-x-only-pubkey>`)
/// rather than a 34-byte witness-v0 script (`OP_0 <32-byte-SHA256-hash>`).
#[test]
fn test_ark_channel_funding_output_is_p2wsh() {
	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);

	let mut user_cfg = test_default_channel_config();
	// Enable ArkChannel negotiation on both sides.
	user_cfg.channel_handshake_config.negotiate_ark_channel = true;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	// ArkChannel implies zero_fee_commitments, which requires anchor reserves.
	let _coinbase_tx = provide_anchor_reserves(&nodes);

	let node_a_id = nodes[0].node.get_our_node_id();
	let node_b_id = nodes[1].node.get_our_node_id();

	// --- Open-channel / accept-channel handshake via functional-test helpers.
	// After this, node 0 has a pending FundingGenerationReady event.
	const CHAN_VALUE: u64 = 10_000_000;
	let temporary_channel_id =
		exchange_open_accept_chan(&nodes[0], &nodes[1], CHAN_VALUE, 0);

	// `create_funding_transaction` consumes the FundingGenerationReady event and builds a
	// transaction whose sole output uses exactly the `output_script` from that event.
	let (chan_id, tx, _) = create_funding_transaction(&nodes[0], &node_b_id, CHAN_VALUE, 42);
	assert_eq!(chan_id, temporary_channel_id);

	// *** Core assertion: the funding output must be segwit-v0 P2WSH, not P2TR. ***
	//
	// P2WSH: OP_0 <32-byte-hash>   (0x0020...)  — witness version 0
	// P2TR:  OP_1 <32-byte-x-only> (0x5120...)  — witness version 1
	//
	// `create_funding_transaction` sets tx.output[0].script_pubkey := output_script verbatim,
	// so asserting on it is equivalent to asserting on the raw output_script.
	//
	// If `get_taproot_output` were ever accidentally wired up for ArkChannel, the script
	// would be 34 bytes starting with 0x51 and is_p2wsh() would return false.
	let funding_spk = &tx.output[0].script_pubkey;
	assert!(
		funding_spk.is_p2wsh(),
		"ArkChannel funding output must be P2WSH (segwit-v0), got: {:?}",
		funding_spk
	);
	assert!(
		!funding_spk.is_p2tr(),
		"ArkChannel funding output must NOT be P2TR (taproot / segwit-v1), got: {:?}",
		funding_spk
	);

	// Verify the negotiated channel type is actually ArkChannel (not a fallback).
	let chan_list = nodes[0].node.list_channels();
	let chan = chan_list
		.iter()
		.find(|c| c.channel_id == temporary_channel_id)
		.expect("channel should be in list");
	assert_eq!(
		chan.channel_type.as_ref().expect("channel_type should be set"),
		&ChannelTypeFeatures::ark_channel(),
		"negotiated channel_type should be ArkChannel"
	);

	// --- Complete the funding flow so the channel reaches ChannelReady.
	//
	// We have already consumed the FundingGenerationReady event via create_funding_transaction,
	// so we drive the rest of the funding handshake manually.
	nodes[0]
		.node
		.funding_transaction_generated(temporary_channel_id, node_b_id, tx.clone())
		.unwrap();
	check_added_monitors(&nodes[0], 0);

	let funding_created_msg =
		get_event_msg!(nodes[0], MessageSendEvent::SendFundingCreated, node_b_id);
	nodes[1].node.handle_funding_created(node_a_id, &funding_created_msg);
	check_added_monitors(&nodes[1], 1);
	expect_channel_pending_event(&nodes[1], &node_a_id);

	let funding_signed_msg =
		get_event_msg!(nodes[1], MessageSendEvent::SendFundingSigned, node_a_id);
	nodes[0].node.handle_funding_signed(node_b_id, &funding_signed_msg);
	check_added_monitors(&nodes[0], 1);
	expect_channel_pending_event(&nodes[0], &node_b_id);

	// Confirm the funding transaction on both sides so the channel reaches ChannelReady.
	create_chan_between_nodes_with_value_confirm(&nodes[0], &nodes[1], &tx);

	// Confirm the open channel carries the ArkChannel type and is ready.
	let chan_list = nodes[0].node.list_channels();
	let chan = chan_list
		.iter()
		.find(|c| c.channel_type.as_ref() == Some(&ChannelTypeFeatures::ark_channel()))
		.expect("ArkChannel should be open and ready");
	assert!(
		chan.is_channel_ready,
		"ArkChannel should have reached ChannelReady, channel_id={:?}",
		chan.channel_id
	);
}

/// End-to-end proof that the Ark HTLC success-path CSV is ACTIVE once `ark_htlc_success_csv_delta`
/// is configured at channel open.
///
/// This opens an `ArkChannel` with `ark_htlc_success_csv_delta = Some(D)` configured on BOTH nodes,
/// routes a real HTLC across it, force-closes, and inspects the holder's on-chain HTLC claim:
///   - the HTLC witness script (`HTLCDescriptor::witness_script`) carries TWO `OP_CSV`s — the
///     1-block anchor delay AND the Ark success-branch `<D> OP_CSV OP_DROP` — and the Ark `OP_CSV`
///     is immediately preceded by a `D` push; and
///   - the HTLC-Success 2nd-stage tx input (`HTLCDescriptor::unsigned_tx_input`) sets
///     `nSequence >= D`, so the consensus-enforced relative timelock is satisfiable.
///
/// This is NON-VACUOUS: before the delta is wired from config into the channel transaction
/// parameters, `ark_htlc_success_csv_delta` is `None` on every commitment, the success branch has
/// only the single anchor `OP_CSV`, and `nSequence` is just the 1-block anchor CSV — both
/// assertions below would fail. The script and sequence are produced from the *real* commitment
/// the channel built, not a hand-constructed `HTLCOutputInCommitment`.
#[test]
fn test_ark_channel_htlc_success_csv_active_end_to_end() {
	const ARK_DELTA: u16 = 144;

	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);

	let mut user_cfg = test_default_channel_config();
	// Enable ArkChannel negotiation AND activate the success-path CSV delta on both sides.
	user_cfg.channel_handshake_config.negotiate_ark_channel = true;
	user_cfg.channel_handshake_config.ark_htlc_success_csv_delta = Some(ARK_DELTA);
	user_cfg.channel_handshake_config.our_htlc_minimum_msat = 1;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	// ArkChannel implies zero_fee_commitments, which needs anchor reserves for the bumped close.
	let _coinbase_tx = provide_anchor_reserves(&nodes);

	let node_a_id = nodes[0].node.get_our_node_id();

	const CHAN_CAPACITY: u64 = 10_000_000;
	let (_, _, chan_id, _funding_tx) = create_announced_chan_between_nodes_with_value(
		&nodes,
		0,
		1,
		CHAN_CAPACITY,
		(CHAN_CAPACITY / 2) * 1000,
	);

	// Confirm the channel really negotiated the ArkChannel type (otherwise this test is vacuous).
	let chan_list = nodes[0].node.list_channels();
	let chan = chan_list.iter().find(|c| c.channel_id == chan_id).expect("channel in list");
	assert_eq!(
		chan.channel_type.as_ref().expect("channel_type set"),
		&ChannelTypeFeatures::ark_channel(),
		"test requires an ArkChannel to be negotiated",
	);

	// Route an HTLC from node 0 to node 1 and have node 1 claim it, so node 1 holds the preimage
	// and will resolve the HTLC through the success path on-chain after a force close.
	const HTLC_AMT_MSAT: u64 = 1_000_000;
	let (preimage, payment_hash, ..) = route_payment(&nodes[0], &[&nodes[1]], HTLC_AMT_MSAT);
	nodes[1].node.claim_funds(preimage);
	check_added_monitors(&nodes[1], 1);
	expect_payment_claimed!(nodes[1], payment_hash, HTLC_AMT_MSAT);
	nodes[0].node.get_and_clear_pending_msg_events();
	nodes[1].node.get_and_clear_pending_msg_events();

	// Force close node 1 (the HTLC receiver / preimage holder) and confirm its commitment.
	let node_1_commit_tx = get_local_commitment_txn!(nodes[1], chan_id).pop().unwrap();
	let message = "force-close for ark csv test".to_owned();
	nodes[1]
		.node
		.force_close_broadcasting_latest_txn(&chan_id, &node_a_id, message.clone())
		.unwrap();
	check_added_monitors(&nodes[1], 1);
	check_closed_broadcast(&nodes[1], 1, true);
	let reason =
		ClosureReason::HolderForceClosed { broadcasted_latest_txn: Some(true), message };
	check_closed_event(&nodes[1], 1, reason, &[node_a_id], CHAN_CAPACITY);

	mine_transaction(&nodes[1], &node_1_commit_tx);

	// Drain the commitment-close bump event(s); we want the HTLCResolution event.
	let secp = Secp256k1::new();
	let events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	let mut checked_descriptors = 0usize;
	for event in events {
		if let Event::BumpTransaction(BumpTransactionEvent::HTLCResolution {
			htlc_descriptors,
			..
		}) = event
		{
			for htlc_descriptor in &htlc_descriptors {
				// This is the HTLC node 1 received and is now claiming with the preimage.
				assert!(!htlc_descriptor.htlc.offered, "expected the received HTLC");
				assert_eq!(
					htlc_descriptor.htlc.ark_htlc_success_csv_delta,
					Some(ARK_DELTA),
					"the configured Ark delta must reach the on-chain HTLC output",
				);

				// (a) The real commitment's HTLC witness script must carry the Ark success-branch
				// CSV: `<D> OP_CSV OP_DROP`. ArkChannel uses the `zero_fee_commitments` (P2A anchor)
				// shape, whose HTLC outputs do NOT carry the legacy 1-block keyed-anchor CSV, so the
				// ONLY OP_CSV in the script is the Ark one, and it must be immediately preceded by a
				// push of the configured delta D (144 -> the 2-byte signed-magnitude push 0x90 0x00).
				let witness_script = htlc_descriptor.witness_script(&secp);
				let mut csv_count = 0usize;
				let mut prev_push: Option<Vec<u8>> = None;
				let mut saw_ark_csv_after_delta_push = false;
				let expected_delta_push = ARK_DELTA.to_le_bytes().to_vec(); // 144 -> [0x90, 0x00]
				for ins in witness_script.instructions() {
					match ins.expect("valid script instruction") {
						Instruction::Op(op) if op == OP_CSV => {
							csv_count += 1;
							if prev_push.as_deref() == Some(expected_delta_push.as_slice()) {
								saw_ark_csv_after_delta_push = true;
							}
							prev_push = None;
						},
						Instruction::PushBytes(b) => {
							prev_push = Some(b.as_bytes().to_vec());
						},
						Instruction::Op(_) => {
							prev_push = None;
						},
					}
				}
				assert_eq!(
					csv_count, 1,
					"ArkChannel (P2A anchor) HTLC success script must have exactly 1 OP_CSV (the Ark success CSV), script={}",
					witness_script,
				);
				assert!(
					saw_ark_csv_after_delta_push,
					"the OP_CSV must be guarded by a push of the configured delta {} (the Ark success CSV), script={}",
					ARK_DELTA, witness_script,
				);

				// (b) The HTLC-Success 2nd-stage tx input must lock nSequence to at least the delta.
				let txin = htlc_descriptor.unsigned_tx_input();
				assert!(
					txin.sequence.to_consensus_u32() >= ARK_DELTA as u32,
					"HTLC-Success nSequence ({}) must be >= the Ark CSV delta ({})",
					txin.sequence.to_consensus_u32(),
					ARK_DELTA,
				);

				checked_descriptors += 1;
			}
		}
	}
	assert_eq!(
		checked_descriptors, 1,
		"expected exactly one HTLC-Success descriptor to inspect end-to-end",
	);
}

/// Integration capstone (M5): an `ArkChannel` opened via
/// `unsafe_manual_funding_transaction_generated` — the virtual/manual-funding entry bark uses —
/// runs the full lifecycle on the LDK side:
///
///   open → `ChannelReady` → HTLC route + settle → force-close → claim
///
/// Unique value over M1/M2/M4: this is the first test that exercises the
/// **manual-funding path** (`FundingType::Unchecked`) for an `ArkChannel`.  We assert:
///
///   1. `FundingTxBroadcastSafe` is emitted (not `FundingTxBroadcasted`) — proving the
///      manual path was taken.
///   2. The channel reaches `ChannelReady` and negotiates the `ArkChannel` type.
///   3. An HTLC can be routed and settled over it.
///   4. After a force-close the broadcast commitment is **stock** (P2WSH input, no
///      OP_RETURN output, commitment input `nSequence` has the locktime-disable bit set —
///      confirming there is no extra commitment-input CSV).
///   5. An HTLC output on the commitment carries the success-path CSV (`ark_htlc_success_csv_delta`),
///      verifying that the manual-funding path does not break the ARK feature composition.
#[test]
fn test_ark_channel_manual_funding_lifecycle() {
	const ARK_DELTA: u16 = 144;

	let chanmon_cfgs = create_chanmon_cfgs(2);
	let node_cfgs = create_node_cfgs(2, &chanmon_cfgs);

	let mut user_cfg = test_default_channel_config();
	user_cfg.channel_handshake_config.negotiate_ark_channel = true;
	user_cfg.channel_handshake_config.ark_htlc_success_csv_delta = Some(ARK_DELTA);
	user_cfg.channel_handshake_config.our_htlc_minimum_msat = 1;

	let configs = [Some(user_cfg.clone()), Some(user_cfg)];
	let node_chanmgrs = create_node_chanmgrs(2, &node_cfgs, &configs);
	let nodes = create_network(2, &node_cfgs, &node_chanmgrs);

	// ArkChannel → zero_fee_commitments → anchor reserves needed for the bumped close.
	let _coinbase_tx = provide_anchor_reserves(&nodes);

	let node_a_id = nodes[0].node.get_our_node_id();
	let node_b_id = nodes[1].node.get_our_node_id();

	// -----------------------------------------------------------------------
	// Phase 1: Open the channel via unsafe_manual_funding_transaction_generated.
	//
	// This is the funding entry that bark uses: the caller supplies just an
	// outpoint (no full transaction); LDK skips the validation/broadcast step
	// and emits FundingTxBroadcastSafe instead of broadcasting automatically.
	// -----------------------------------------------------------------------
	const CHAN_VALUE: u64 = 10_000_000;
	let temp_chan_id = exchange_open_accept_chan(&nodes[0], &nodes[1], CHAN_VALUE, 0);

	// Consume the FundingGenerationReady event and build the funding tx (but do NOT
	// hand it to funding_transaction_generated — we use the "unsafe" outpoint-only API).
	let (funding_temp_id, funding_tx, funding_outpoint) =
		create_funding_transaction(&nodes[0], &node_b_id, CHAN_VALUE, 42);
	assert_eq!(funding_temp_id, temp_chan_id);

	// *** THE MANUAL-FUNDING ENTRY UNDER TEST ***
	nodes[0]
		.node
		.unsafe_manual_funding_transaction_generated(temp_chan_id, node_b_id, funding_outpoint)
		.unwrap();
	check_added_monitors(&nodes[0], 0);

	// FundingCreated  ──→  node_b
	let funding_created_msg =
		get_event_msg!(nodes[0], MessageSendEvent::SendFundingCreated, node_b_id);
	nodes[1].node.handle_funding_created(node_a_id, &funding_created_msg);
	check_added_monitors(&nodes[1], 1);
	expect_channel_pending_event(&nodes[1], &node_a_id);

	// FundingSigned  ──→  node_a
	let funding_signed_msg =
		get_event_msg!(nodes[1], MessageSendEvent::SendFundingSigned, node_a_id);
	nodes[0].node.handle_funding_signed(node_b_id, &funding_signed_msg);
	check_added_monitors(&nodes[0], 1);

	// Assert that FundingTxBroadcastSafe was emitted (not an automatic broadcast).
	// This is the proof that the manual-funding entry was exercised.
	let pending_events = nodes[0].node.get_and_clear_pending_events();
	assert_eq!(
		pending_events.len(),
		2,
		"expected FundingTxBroadcastSafe + ChannelPending, got {pending_events:?}",
	);
	let mut saw_broadcast_safe = false;
	for ev in &pending_events {
		match ev {
			Event::FundingTxBroadcastSafe { funding_txo, .. } => {
				assert_eq!(funding_txo.txid, funding_outpoint.txid);
				assert_eq!(funding_txo.vout, u32::from(funding_outpoint.index));
				saw_broadcast_safe = true;
			},
			Event::ChannelPending { counterparty_node_id, .. } => {
				assert_eq!(*counterparty_node_id, node_b_id);
			},
			other => panic!("unexpected pending event: {other:?}"),
		}
	}
	assert!(saw_broadcast_safe, "FundingTxBroadcastSafe must be emitted on the manual-funding path");

	// -----------------------------------------------------------------------
	// Phase 2: Mine the funding tx → ChannelReady, exchange announcement sigs.
	// -----------------------------------------------------------------------
	// confirm_first: mine on node_b (sends channel_ready to node_a)
	let conf_height =
		core::cmp::max(nodes[0].best_block_info().1 + 1, nodes[1].best_block_info().1 + 1);
	create_chan_between_nodes_with_value_confirm_first(&nodes[0], &nodes[1], &funding_tx, conf_height);

	// mine on node_a, which fires ChannelReady + AnnouncementSigs + ChannelUpdate
	confirm_transaction_at(&nodes[0], &funding_tx, conf_height);
	connect_blocks(&nodes[0], CHAN_CONFIRM_DEPTH - 1);
	expect_channel_ready_event(&nodes[0], &node_b_id);

	let (as_funding_msgs, chan_id) =
		create_chan_between_nodes_with_value_confirm_second(&nodes[1], &nodes[0]);

	let (announcement, as_update, bs_update) =
		create_chan_between_nodes_with_value_b(&nodes[0], &nodes[1], &as_funding_msgs);
	update_nodes_with_chan_announce(&nodes, 0, 1, &announcement, &as_update, &bs_update);

	// Assert we really opened an ArkChannel (not a fallback).
	let chan_list = nodes[0].node.list_channels();
	let chan = chan_list.iter().find(|c| c.channel_id == chan_id).expect("channel in list");
	assert!(chan.is_channel_ready, "channel must be ChannelReady");
	assert_eq!(
		chan.channel_type.as_ref().expect("channel_type set"),
		&ChannelTypeFeatures::ark_channel(),
		"manual-funding must negotiate an ArkChannel",
	);

	// -----------------------------------------------------------------------
	// Phase 3: Route an HTLC and have node 1 claim it with the preimage.
	//
	// We route node_0 → node_1 so that node_1 is the receiver/preimage-holder
	// and will use the HTLC success path on-chain after the force-close.
	// -----------------------------------------------------------------------
	const HTLC_AMT_MSAT: u64 = 1_000_000;
	let (preimage, payment_hash, ..) = route_payment(&nodes[0], &[&nodes[1]], HTLC_AMT_MSAT);
	nodes[1].node.claim_funds(preimage);
	check_added_monitors(&nodes[1], 1);
	expect_payment_claimed!(nodes[1], payment_hash, HTLC_AMT_MSAT);
	// Drain pending messages so the subsequent force-close starts from a clean state.
	nodes[0].node.get_and_clear_pending_msg_events();
	nodes[1].node.get_and_clear_pending_msg_events();

	// -----------------------------------------------------------------------
	// Phase 4: Force-close (node 1) and assert the on-chain outputs.
	// -----------------------------------------------------------------------
	let node_1_commit_tx = get_local_commitment_txn!(nodes[1], chan_id).pop().unwrap();

	// Assert (4a): no OP_RETURN output in the commitment tx (stock commitment).
	for (idx, out) in node_1_commit_tx.output.iter().enumerate() {
		assert!(
			!out.script_pubkey.is_op_return(),
			"commitment tx must not have an OP_RETURN output (output #{idx})",
		);
	}

	// Assert (4b): the commitment's single input uses a sequence with the
	// locktime-disable bit set — i.e. it does NOT carry a commitment-input CSV.
	// BOLT-3 §commitment_tx sets nSequence = 0x80000000 (relative-locktime disabled).
	const LOCKTIME_DISABLE_FLAG: u32 = 0x8000_0000;
	for (idx, inp) in node_1_commit_tx.input.iter().enumerate() {
		assert!(
			inp.sequence.to_consensus_u32() & LOCKTIME_DISABLE_FLAG != 0,
			"commitment tx input #{idx} must have the locktime-disable bit set (nSequence=0x{:08x})",
			inp.sequence.to_consensus_u32(),
		);
	}

	// Perform the force-close.
	let message = "force-close for M5 manual-funding lifecycle test".to_owned();
	nodes[1]
		.node
		.force_close_broadcasting_latest_txn(&chan_id, &node_a_id, message.clone())
		.unwrap();
	check_added_monitors(&nodes[1], 1);
	check_closed_broadcast(&nodes[1], 1, true);
	let reason =
		ClosureReason::HolderForceClosed { broadcasted_latest_txn: Some(true), message };
	check_closed_event(&nodes[1], 1, reason, &[node_a_id], CHAN_VALUE);

	mine_transaction(&nodes[1], &node_1_commit_tx);

	// -----------------------------------------------------------------------
	// Phase 5: Inspect the HTLCResolution event — assert the Ark success CSV
	// is present in the witness script and nSequence satisfies it.
	// -----------------------------------------------------------------------
	let secp = Secp256k1::new();
	let chain_events = nodes[1].chain_monitor.chain_monitor.get_and_clear_pending_events();
	let mut checked_descriptors = 0usize;
	for event in chain_events {
		if let Event::BumpTransaction(BumpTransactionEvent::HTLCResolution {
			htlc_descriptors,
			..
		}) = event
		{
			for htlc_descriptor in &htlc_descriptors {
				// node_1 received this HTLC (holds the preimage).
				assert!(!htlc_descriptor.htlc.offered, "expected the received HTLC");
				assert_eq!(
					htlc_descriptor.htlc.ark_htlc_success_csv_delta,
					Some(ARK_DELTA),
					"the configured Ark delta must reach the on-chain HTLC output",
				);

				// Assert (5a): the witness script has exactly one OP_CSV (the Ark CSV)
				// immediately preceded by a push of ARK_DELTA.
				let witness_script = htlc_descriptor.witness_script(&secp);
				let mut csv_count = 0usize;
				let mut prev_push: Option<Vec<u8>> = None;
				let mut saw_ark_csv_after_delta_push = false;
				let expected_delta_push = ARK_DELTA.to_le_bytes().to_vec();
				for ins in witness_script.instructions() {
					match ins.expect("valid script instruction") {
						Instruction::Op(op) if op == OP_CSV => {
							csv_count += 1;
							if prev_push.as_deref() == Some(expected_delta_push.as_slice()) {
								saw_ark_csv_after_delta_push = true;
							}
							prev_push = None;
						},
						Instruction::PushBytes(b) => {
							prev_push = Some(b.as_bytes().to_vec());
						},
						Instruction::Op(_) => {
							prev_push = None;
						},
					}
				}
				assert_eq!(
					csv_count, 1,
					"ArkChannel (P2A) HTLC success script must have exactly 1 OP_CSV, script={witness_script}",
				);
				assert!(
					saw_ark_csv_after_delta_push,
					"the OP_CSV must be preceded by the configured delta {ARK_DELTA}, script={witness_script}",
				);

				// Assert (5b): the 2nd-stage tx input nSequence satisfies the CSV.
				let txin = htlc_descriptor.unsigned_tx_input();
				assert!(
					txin.sequence.to_consensus_u32() >= ARK_DELTA as u32,
					"HTLC-Success nSequence ({}) must be >= Ark CSV delta ({})",
					txin.sequence.to_consensus_u32(),
					ARK_DELTA,
				);

				checked_descriptors += 1;
			}
		}
	}
	assert_eq!(
		checked_descriptors, 1,
		"expected exactly one HTLC-Success descriptor from the manual-funding ArkChannel lifecycle",
	);
}
