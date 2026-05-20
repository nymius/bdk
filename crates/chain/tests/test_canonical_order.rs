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

/// Demonstrates the same topological-order bug on a linear chain X -> Y -> Z.
///
/// The chain shape is specifically chosen because it is a failure mode of any inline ordering
/// scheme that assigns indices in visit order and bumps an existing entry's index on revisit -
/// the current code does not implement such a scheme, but this test pins down the required
/// invariant regardless of how the fix is approached.
///
/// Trace through the current code:
///
/// `params.assume_canonical = [X, Y]` is iterated in reverse (line 228 of canonical_task.rs),
/// so the AssumedTxs stage processes Y first:
///
/// 1. `mark_canonical(Y, Assumed)` - BFS from Y visits Y (depth 0), then walks up to X (depth 1,
///    Y's only parent). Both are inserted. `canonical_order = [Y, X]`.
///
/// 2. The AssumedTxs iterator next yields X, but `is_canonicalized(X)` is now true, so
///    `mark_canonical` is skipped entirely. X's position at index 1 is locked.
///
/// 3. SeenTxs stage runs `mark_canonical(Z, ObservedIn(Mempool(1)))`. BFS from Z visits Z (inserted
///    at index 2), then walks up to Y. Y is `Entry::Occupied` - the closure returns None, pruning
///    the walk. `canonical_order = [Y, X, Z]`.
///
/// The resulting order `[Y, X, Z]` is neither topological (X must precede Y) nor
/// reverse-topological (Z must precede Y).
///
/// `#[ignore]`'d for the same reason as `canonical_order_is_topological`: asserts the desired
/// invariant; removing the `#[ignore]` is the acceptance criterion for the fix.
#[test]
fn canonical_order_is_topological_on_chain_with_assumed_ancestor_and_seen_descendant() {
    // Linear chain - no conflicts:
    //
    //   X   (assume_canonical)
    //   |
    //   Y   (assume_canonical)
    //   |
    //   Z   (last_seen = 1)
    let local_chain = local_chain![(0, hash!("genesis"))];
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "X",
            inputs: &[TxInTemplate::Bogus],
            outputs: &[TxOutTemplate::new(10_000, None)],
            anchors: &[],
            last_seen: None,
            assume_canonical: true,
        },
        TxTemplate {
            tx_name: "Y",
            inputs: &[TxInTemplate::PrevTx("X", 0)],
            outputs: &[TxOutTemplate::new(9_000, None)],
            anchors: &[],
            last_seen: None,
            assume_canonical: true,
        },
        TxTemplate {
            tx_name: "Z",
            inputs: &[TxInTemplate::PrevTx("Y", 0)],
            outputs: &[TxOutTemplate::new(8_000, None)],
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
        3,
        "expected all 3 txs canonical, got: {:?}",
        canonical_order
    );

    let expected_edges = [(txid("X"), txid("Y")), (txid("Y"), txid("Z"))];

    assert!(
        is_topological(&canonical_order, &expected_edges),
        "canonical order is not topological (parents before children).\n\
         order: {:?}\n\
         X={}, Y={}, Z={}",
        canonical_order,
        txid("X"),
        txid("Y"),
        txid("Z"),
    );
}

/// Demonstrates the topological-order invariant on a graph where a child transaction has two
/// inputs both spending from the same parent.
///
/// Graph:
///
///   A   (root, two outputs)
///   |\
///   | \
///   B   (assume_canonical; inputs = [A:0, A:1])
///
/// Any topological-walk implementation must deduplicate parent txids when counting in-degree:
/// a child with N inputs from the same parent contributes a *single* DAG edge, not N. Counting
/// inputs directly inflates in-degree, leaving the child unreachable in algorithms like Kahn's
/// (the parent decrements once but the child needs N decrements to reach in-degree 0).
///
/// `#[ignore]`'d for the same reason as the other order tests: asserts the desired invariant;
/// removing the `#[ignore]` is the acceptance criterion for the fix.
#[test]
fn canonical_order_is_topological_with_two_inputs_from_same_parent_avoids_in_degree_inflation() {
    // A has two outputs; B spends both - two inputs, one canonical parent.
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
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "B",
            inputs: &[TxInTemplate::PrevTx("A", 0), TxInTemplate::PrevTx("A", 1)],
            outputs: &[TxOutTemplate::new(18_000, None)],
            anchors: &[],
            last_seen: None,
            assume_canonical: true,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    assert_eq!(
        canonical_order.len(),
        2,
        "expected both txs canonical, got: {:?}",
        canonical_order
    );

    let expected_edges = [(txid("A"), txid("B"))];

    assert!(
        is_topological(&canonical_order, &expected_edges),
        "canonical order is not topological (parents before children).\n\
         order: {:?}\n\
         A={}, B={}",
        canonical_order,
        txid("A"),
        txid("B"),
    );
}
