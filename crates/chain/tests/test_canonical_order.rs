#![cfg(feature = "miniscript")]

mod common;

use bdk_chain::local_chain::LocalChain;
use bdk_chain::tx_graph::TxGraph;
use bdk_chain::BlockId;
use bdk_testenv::{block_id, hash, local_chain};
use bitcoin::Txid;
use common::*;
use std::collections::HashSet;

/// Returns true if every in-graph parent of every transaction in `order` appears before
/// that transaction in `order`. Parents whose txid is not present in `tx_graph` (e.g. from
/// `TxInTemplate::Bogus` or coinbase inputs) are skipped.
fn is_topological<A>(order: &[Txid], tx_graph: &TxGraph<A>) -> bool {
    let mut seen: HashSet<Txid> = HashSet::new();
    for &txid in order {
        let tx = tx_graph.get_tx(txid).expect("tx in order must be in graph");
        for input in &tx.input {
            let parent = input.previous_output.txid;
            if tx_graph.get_tx(parent).is_some() && !seen.contains(&parent) {
                return false;
            }
        }
        seen.insert(txid);
    }
    true
}

/// Standard 7-block local chain used by the ported scenario tests.
fn test_chain() -> LocalChain {
    local_chain![
        (0, hash!("A")),
        (1, hash!("B")),
        (2, hash!("C")),
        (3, hash!("D")),
        (4, hash!("E")),
        (5, hash!("F")),
        (6, hash!("G"))
    ]
}

/// Diamond-shaped DAG with an assumed root:
///
///     A          (assume_canonical, two outputs)
///    / \
///   B   C        (B spends A:0, C spends A:1)
///    \ /
///     D          (spends B:0 and C:0, last_seen = 1)
///
/// The bug this test guards against: `mark_canonical(A)` inserts A first; later
/// `mark_canonical(D)` walks D -> B -> C but finds A already visited and skips it,
/// producing [A, D, B, C] - D before its parents B and C.
#[test]
fn canonical_order_is_topological() {
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

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    assert_eq!(
        canonical_order.len(),
        4,
        "expected all 4 txs canonical, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Linear chain mixing assumed and seen:
///
///   X   (assume_canonical)
///   |
///   Y   (assume_canonical)
///   |
///   Z   (last_seen = 1)
///
/// The bug this test guards against: assume_canonical iterates in reverse so Y is
/// processed first; BFS from Y inserts [Y, X]; later Z's BFS finds Y occupied and
/// produces [Y, X, Z] - X after Y, and Z after X but not after Y.
#[test]
fn canonical_order_is_topological_on_chain_with_assumed_ancestor_and_seen_descendant() {
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

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    assert_eq!(
        canonical_order.len(),
        3,
        "expected all 3 txs canonical, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Child with two inputs from the same parent:
///
///   A   (root, two outputs)
///   |\
///   | \
///   B   (assume_canonical; inputs = [A:0, A:1])
///
/// Guards against in-degree inflation: B has two inputs from A but A is a single
/// canonical parent. Counting inputs directly instead of deduplicating leaves B
/// unreachable (parent decrements in-degree once, child needs two decrements to
/// reach zero).
#[test]
fn canonical_order_is_topological_with_two_inputs_from_same_parent_avoids_in_degree_inflation() {
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

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    assert_eq!(
        canonical_order.len(),
        2,
        "expected both txs canonical, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Simple diamond with a shared root and merge point, all confirmed:
///
///   a0          (anchored at block 1)
///   |
///   b0   c0     (b0 spends a0; c0 is an independent root; both anchored)
///    \   /
///     d0         (spends b0:0 and c0:0, anchored at block 3)
#[test]
fn topological_diamond_all_confirmed() {
    let local_chain = test_chain();
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "a0",
            inputs: &[],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b0",
            inputs: &[TxInTemplate::PrevTx("a0", 0)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(2, "C")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c0",
            inputs: &[],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(3, "D")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "d0",
            inputs: &[TxInTemplate::PrevTx("b0", 0), TxInTemplate::PrevTx("c0", 0)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(3, "D")],
            last_seen: None,
            assume_canonical: false,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    let expected: HashSet<Txid> = ["a0", "b0", "c0", "d0"]
        .iter()
        .map(|name| txid(name))
        .collect();

    assert_eq!(
        HashSet::<Txid>::from_iter(canonical_order.iter().copied()),
        expected,
        "unexpected canonical set, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Two parallel chains from a shared root, merging into a single sink:
///
///   a0           (two outputs, anchored at block 1)
///   |  \
///   b0  b1       (b0 spends a0:0, b1 spends a0:1; each has two outputs)
///   |\ |
///   c0 c1        (c0 spends b0:0; c1 spends b1:0)
///      |
///      d0        (spends b0:1 and c1:0)
#[test]
fn topological_two_chains_merging() {
    let local_chain = test_chain();
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "a0",
            inputs: &[],
            outputs: &[
                TxOutTemplate::new(10000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
            ],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b0",
            inputs: &[TxInTemplate::PrevTx("a0", 0)],
            outputs: &[
                TxOutTemplate::new(10000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
            ],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c0",
            inputs: &[TxInTemplate::PrevTx("b0", 0)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b1",
            inputs: &[TxInTemplate::PrevTx("a0", 1)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c1",
            inputs: &[TxInTemplate::PrevTx("b1", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "d0",
            inputs: &[TxInTemplate::PrevTx("b0", 1), TxInTemplate::PrevTx("c1", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    let expected: HashSet<Txid> = ["a0", "b0", "c0", "b1", "c1", "d0"]
        .iter()
        .map(|name| txid(name))
        .collect();

    assert_eq!(
        HashSet::<Txid>::from_iter(canonical_order.iter().copied()),
        expected,
        "unexpected canonical set, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Three disconnected components in a single canonical set:
///
///   a0 -> b0 -> c0          (linear chain, anchored at blocks 1-3)
///   d0                      (isolated root, anchored at block 3)
///   e0 -> f0 \
///      \      -> g0         (diamond, f0 and f1 both spend e0; g0 spends both)
///       -> f1 /
///
/// g0 is unconfirmed (last_seen only). Tests that Kahn's handles multiple independent
/// components in a single pass and does not stall on the unconfirmed sink.
#[test]
fn topological_disconnected_components() {
    let local_chain = test_chain();
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "a0",
            inputs: &[],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b0",
            inputs: &[TxInTemplate::PrevTx("a0", 0)],
            outputs: &[
                TxOutTemplate::new(5000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
            ],
            anchors: &[block_id!(2, "C")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c0",
            inputs: &[TxInTemplate::PrevTx("b0", 0)],
            outputs: &[TxOutTemplate::new(2500, Some(0))],
            anchors: &[block_id!(3, "D")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "d0",
            inputs: &[],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(3, "D")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "e0",
            inputs: &[],
            outputs: &[
                TxOutTemplate::new(10000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
            ],
            anchors: &[block_id!(4, "E")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "f0",
            inputs: &[TxInTemplate::PrevTx("e0", 0)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(5, "F")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "f1",
            inputs: &[TxInTemplate::PrevTx("e0", 1)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(5, "F")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "g0",
            inputs: &[TxInTemplate::PrevTx("f0", 0), TxInTemplate::PrevTx("f1", 0)],
            outputs: &[TxOutTemplate::new(1000, Some(0))],
            anchors: &[],
            last_seen: Some(1000),
            assume_canonical: false,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    let expected: HashSet<Txid> = ["a0", "b0", "c0", "d0", "e0", "f0", "f1", "g0"]
        .iter()
        .map(|name| txid(name))
        .collect();

    assert_eq!(
        HashSet::<Txid>::from_iter(canonical_order.iter().copied()),
        expected,
        "unexpected canonical set, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}

/// Deep DAG with multi-parent nodes and two parallel sub-chains:
///
///      a0          (three outputs, anchored at block 1)
///     /|  \
///   e0 |   b1      (e0 spends a0:0; b1 spends a0:2)
///   |  |     \
///   f0 |      c1   (f0 spends e0:0; c1 spends b1:0)
///    \ |       \
///     b0        |  (b0 spends f0:0 and a0:1 - two parents)
///    /  \       |
///   c0   \      |
///         \    /
///          d0      (spends b0:1 and c1:0 - two parents)
#[test]
fn topological_multi_parent_deep() {
    let local_chain = test_chain();
    let chain_tip = local_chain.tip().block_id();

    let tx_templates = [
        TxTemplate {
            tx_name: "a0",
            inputs: &[],
            outputs: &[
                TxOutTemplate::new(10000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
                TxOutTemplate::new(10000, Some(2)),
            ],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "e0",
            inputs: &[TxInTemplate::PrevTx("a0", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "f0",
            inputs: &[TxInTemplate::PrevTx("e0", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b0",
            inputs: &[TxInTemplate::PrevTx("f0", 0), TxInTemplate::PrevTx("a0", 1)],
            outputs: &[
                TxOutTemplate::new(10000, Some(0)),
                TxOutTemplate::new(10000, Some(1)),
            ],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c0",
            inputs: &[TxInTemplate::PrevTx("b0", 0)],
            outputs: &[TxOutTemplate::new(5000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "b1",
            inputs: &[TxInTemplate::PrevTx("a0", 2)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "c1",
            inputs: &[TxInTemplate::PrevTx("b1", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
        TxTemplate {
            tx_name: "d0",
            inputs: &[TxInTemplate::PrevTx("b0", 1), TxInTemplate::PrevTx("c1", 0)],
            outputs: &[TxOutTemplate::new(10000, Some(0))],
            anchors: &[block_id!(1, "B")],
            last_seen: None,
            assume_canonical: false,
        },
    ];

    let env = init_graph::<BlockId>(&tx_templates);
    let txid = |name: &str| *env.txid_to_name.get(name).unwrap();

    let canonical_view =
        local_chain.canonical_view(&env.tx_graph, chain_tip, env.canonicalization_params);

    let canonical_order: Vec<Txid> = canonical_view.txs().map(|t| t.txid).collect();

    let expected: HashSet<Txid> = ["a0", "e0", "f0", "b0", "c0", "b1", "c1", "d0"]
        .iter()
        .map(|name| txid(name))
        .collect();

    assert_eq!(
        HashSet::<Txid>::from_iter(canonical_order.iter().copied()),
        expected,
        "unexpected canonical set, got: {:?}",
        canonical_order
    );

    assert!(
        is_topological(&canonical_order, &env.tx_graph),
        "canonical order is not topological (parents before children).\n\
         order: {:?}",
        canonical_order,
    );
}
