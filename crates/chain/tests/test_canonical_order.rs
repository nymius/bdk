#![cfg(feature = "miniscript")]

mod common;

use bdk_chain::BlockId;
use bdk_testenv::{hash, local_chain};
use bitcoin::Txid;
use common::*;
use std::collections::HashMap;

/// Returns true if every parent appears before its child in `order`.
fn is_topological(order: &[Txid], edges: &[(Txid, Txid)]) -> bool {
    let canonical_position_map: HashMap<Txid, usize> = order
        .iter()
        .enumerate()
        .map(|(canonical_position, txid)| (*txid, canonical_position))
        .collect();
    edges
        .iter()
        .all(|(parent, child)| canonical_position_map[parent] < canonical_position_map[child])
}

/// Demonstrates that the current canonicalization produces an order that is neither topological
/// (parents before children) nor reverse-topological (children before parents).
///
/// The bug arises from two `mark_canonical` calls operating on overlapping ancestor sets:
///
/// 1. `mark_canonical(A)` - A is processed first (AssumedTxs stage). A has no in-graph parents, so
///    only A is added to `canonical_order`. State: `[A]`.
///
/// 2. `mark_canonical(D)` - D is processed later (SeenTxs stage). BFS walks D -> B -> C, then tries
///    to visit A but finds it already in `self.canonical` (`Entry::Occupied`) and skips it. B and C
///    are appended. State: `[A, D, B, C]`.
///
/// The resulting order `[A, D, B, C]` violates both conventions:
/// - Not topological: D (child of B and C) appears before B and C.
/// - Not reverse-topological: A (parent of B, C, D) appears before all of them.
///
/// This test is currently `#[ignore]`'d because it asserts the *desired* invariant (topological
/// order) which the current implementation does not satisfy. Once `mark_canonical` (or `finish()`)
/// is fixed to produce a valid topological order, remove the `#[ignore]`.
#[test]
#[ignore = "canonical order is not yet topological; see canonical_task.rs mark_canonical / finish"]
fn canonical_order_is_topological() {
    // Diamond-shaped DAG - no conflicts (B and C spend different outputs of A):
    //
    //     A          (assume_canonical, two outputs)
    //    / \
    //   B   C        (B spends A:0, C spends A:1)
    //    \ /
    //     D          (spends B:0 and C:0, last_seen = 1)
    let local_chain = local_chain![(0, hash!("genesis"))];
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "A",
            inputs: &[TxInTemplate::Bogus],
            outputs: &[
                TxOutTemplate::new(10_000, None),
                TxOutTemplate::new(10_000, None),
            ],
            anchors: &[],
            last_seen: None,
            assume_canonical: true,
        },
        TxTemplate {
            tx_name: "B",
            inputs: &[TxInTemplate::PrevTx("A", 0)],
            outputs: &[TxOutTemplate::new(9_000, None)],
            anchors: &[],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "C",
            inputs: &[TxInTemplate::PrevTx("A", 1)],
            outputs: &[TxOutTemplate::new(9_000, None)],
            anchors: &[],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "D",
            inputs: &[TxInTemplate::PrevTx("B", 0), TxInTemplate::PrevTx("C", 0)],
            outputs: &[TxOutTemplate::new(17_000, None)],
            anchors: &[],
            last_seen: Some(1),
            assume_canonical: false,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    assert_eq!(
        canonical_order.len(),
        4,
        "expected all 4 txs canonical, got: {:?}",
        canonical_order
    );

    let expected_edges = [
        (txid("A"), txid("B")),
        (txid("A"), txid("C")),
        (txid("B"), txid("D")),
        (txid("C"), txid("D")),
    ];

    assert!(
        is_topological(&canonical_order, &expected_edges),
        "canonical order is not topological (parents before children).\n\
         order: {:?}\n\
         A={}, B={}, C={}, D={}",
        canonical_order,
        txid("A"),
        txid("B"),
        txid("C"),
        txid("D"),
    );
}
