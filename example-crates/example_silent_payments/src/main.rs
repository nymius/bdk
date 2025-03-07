// 1. Generate silent payment code
// 2. Generate new key pair A
// 3. Get address from key pair A
// 4. Fund key pair A
// 5. Sync
// 6. Generate silent payment address from silent payment code
// 7. Send funds to silent payment code
// 8. Sync
// 9. Check funds are there

use std::collections::BTreeMap;
use std::io::{self, Write};
use std::thread::sleep;
use std::{error::Error, str::FromStr};

use std::{
    path::PathBuf,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc,
    },
    time::{Duration, Instant},
};

use bdk_bitcoind_rpc::{
    bitcoincore_rpc::{Auth, Client, RpcApi},
    Emitter,
};

use bip39::Mnemonic;
use bitcoin::bip32::{DerivationPath, Xpriv};
use bitcoin::script::{Script, ScriptBuf};
use rand::fill;
use secp256k1::silentpayments::{
    silentpayments_recipient_scan_outputs, silentpayments_sender_create_outputs,
    SilentpaymentsPublicData,
};
use secp256k1::Keypair;
use secp256k1::SecretKey;

// Import types from the silentpayments library
use rust_bip352::utils::code::{SilentPaymentCode, SilentPaymentHrp, VersionStrict};
use rust_bip352::utils::input::get_pubkey_from_input;
use rust_bip352::utils::outpoint::SilentPaymentOutpoint;

use serde_json::json;
use std::cmp;
use std::collections::HashMap;
use std::env;
use std::fmt;
use std::sync::Mutex;

use bdk_chain::bitcoin::{
    absolute, address::NetworkUnchecked, bip32, consensus, constants, hex::DisplayHex, relative,
    secp256k1::Secp256k1, transaction, Address, Amount, Network, NetworkKind, PrivateKey, Psbt,
    PublicKey, Sequence, Transaction, TxIn, TxOut,
};
use bdk_chain::miniscript::{
    descriptor::{DescriptorSecretKey, SinglePubKey},
    plan::{Assets, Plan},
    psbt::PsbtExt,
    Descriptor, DescriptorPublicKey,
};
use bdk_chain::ConfirmationBlockTime;
use bdk_chain::{
    collections::BTreeSet,
    indexed_tx_graph,
    indexer::keychain_txout::{self, KeychainTxOutIndex},
    local_chain::{self, LocalChain},
    spk_client::{FullScanRequest, SyncRequest},
    tx_graph, ChainOracle, ChainPosition, DescriptorExt, FullTxOut, IndexedTxGraph, Merge,
};
use bdk_coin_select::{
    metrics::LowestFee, Candidate, ChangePolicy, CoinSelector, DrainWeights, FeeRate, Target,
    TargetFee, TargetOutputs,
};
use bdk_file_store::Store;
use example_cli::anyhow::bail;
use example_cli::anyhow::Context;
use rand::prelude::*;

pub use anyhow;

const DB_MAGIC: &[u8] = b"bdk_example_silent_payment";
const DB_PATH: &str = ".bdk_example_silent_payment.db";
/// The mpsc channel bound for emissions from [`Emitter`].
const CHANNEL_BOUND: usize = 10;
/// Delay for printing status to stdout.
const STDOUT_PRINT_DELAY: Duration = Duration::from_secs(6);
/// Delay between mempool emissions.
const MEMPOOL_EMIT_DELAY: Duration = Duration::from_secs(30);
/// Delay for committing to persistence.
const DB_COMMIT_DELAY: Duration = Duration::from_secs(60);

#[derive(Debug, Clone)]
struct ScanTxHelperV2 {
    ins: Vec<(Vec<u8>, TxIn)>,
    outs: Vec<TxOut>,
}

impl fmt::Display for ScanTxHelperV2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for input in self.ins.iter().map(|x| x.1.clone()) {
            writeln!(f, "input: {:?}\n", input)?;
        }
        for output in self.outs.iter() {
            writeln!(f, "output: {:?}\n", output)?;
        }
        write!(f, "")
    }
}

#[derive(
    Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, serde::Deserialize, serde::Serialize,
)]
pub enum Keychain {
    External,
    Internal,
}

impl fmt::Display for Keychain {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Keychain::External => write!(f, "external"),
            Keychain::Internal => write!(f, "internal"),
        }
    }
}

/// Alias for a `IndexedTxGraph` with specific `Anchor` and `Indexer`.
pub type KeychainTxGraph = IndexedTxGraph<ConfirmationBlockTime, KeychainTxOutIndex<Keychain>>;

/// ChangeSet
#[derive(Default, Debug, Clone, PartialEq, serde::Deserialize, serde::Serialize)]
pub struct ChangeSet {
    /// Descriptor for recipient addresses.
    pub descriptor: Option<Descriptor<DescriptorPublicKey>>,
    /// Descriptor for change addresses.
    pub change_descriptor: Option<Descriptor<DescriptorPublicKey>>,
    /// Stores the network type of the transaction data.
    pub network: Option<Network>,
    /// Changes to the [`LocalChain`].
    pub local_chain: local_chain::ChangeSet,
    /// Changes to [`TxGraph`](tx_graph::TxGraph).
    pub tx_graph: tx_graph::ChangeSet<ConfirmationBlockTime>,
    /// Changes to [`KeychainTxOutIndex`].
    pub indexer: keychain_txout::ChangeSet,
}

impl Merge for ChangeSet {
    fn merge(&mut self, other: Self) {
        if other.descriptor.is_some() {
            self.descriptor = other.descriptor;
        }
        if other.change_descriptor.is_some() {
            self.change_descriptor = other.change_descriptor;
        }
        if other.network.is_some() {
            self.network = other.network;
        }
        Merge::merge(&mut self.local_chain, other.local_chain);
        Merge::merge(&mut self.tx_graph, other.tx_graph);
        Merge::merge(&mut self.indexer, other.indexer);
    }

    fn is_empty(&self) -> bool {
        self.descriptor.is_none()
            && self.change_descriptor.is_none()
            && self.network.is_none()
            && self.local_chain.is_empty()
            && self.tx_graph.is_empty()
            && self.indexer.is_empty()
    }
}

fn parse_silent_payment_keys() -> (SilentPaymentCode, SecretKey) {
    let silent_payment_string: &str = "sprt1qqw7zfpjcuwvq4zd3d4aealxq3d669s3kcde4wgr3zl5ugxs40twv2qccgvszutt7p796yg4h926kdnty66wxrfew26gu2gk5h5hcg4s2jqyascfz";
    let silent_payment_code =
        SilentPaymentCode::<VersionStrict, _>::try_from(silent_payment_string)
            .expect("should parse");

    let spend_key =
        PrivateKey::from_wif("cRFcZbp7cAeZGsnYKdgSZwH6drJ3XLnPSGcjLNCpRy28tpGtZR11").unwrap();
    let scan_key =
        PrivateKey::from_wif("cTiSJ8p2zpGSkWGkvYFWfKurgWvSi9hdvzw9GEws18kS2VRPNS24").unwrap();

    println!("Receiver address: {}", silent_payment_code);
    assert_eq!(format!("{silent_payment_code}"), silent_payment_string);
    (
        silent_payment_code.assume_checked(),
        secp256k1::SecretKey::from_slice(scan_key.inner.as_ref()).unwrap(),
    )
}

fn scan_tx(
    receiver: &SilentPaymentCode,
    secret_scan_key: &SecretKey,
    scan_tx_helper: ScanTxHelperV2,
) {
    let secp = secp256k1::Secp256k1::new();
    let (taproot_inputs, non_taproot_inputs): (
        Vec<(ScriptBuf, bitcoin::PublicKey)>,
        Vec<(ScriptBuf, bitcoin::PublicKey)>,
    ) = scan_tx_helper
        .ins
        .clone()
        .into_iter()
        .filter_map(|(prevout, txin)| {
            let prevout: ScriptBuf = Script::from_bytes(&prevout).into();
            get_pubkey_from_input(txin, prevout.clone())
                .unwrap()
                .map(|pubkey| (prevout, pubkey))
        })
        .partition(|(prevout, _)| prevout.is_p2tr());

    let smallest_outpoint: SilentPaymentOutpoint = scan_tx_helper
        .ins
        .into_iter()
        .map(|(_, x)| SilentPaymentOutpoint(x.previous_output))
        .min()
        .expect("minimum should exist");

    let taproot_inputs: Vec<secp256k1::XOnlyPublicKey> = taproot_inputs
        .iter()
        .map(|(_, pubkey)| {
            let secp256k1_pubkey =
                secp256k1::PublicKey::from_str(pubkey.to_string().as_ref()).unwrap();
            secp256k1::XOnlyPublicKey::from(secp256k1_pubkey)
        })
        .collect();

    let taproot_inputs_v2: Vec<&secp256k1::XOnlyPublicKey> = taproot_inputs.iter().collect();
    let non_taproot_inputs: Vec<secp256k1::PublicKey> = non_taproot_inputs
        .iter()
        .map(|x| secp256k1::PublicKey::from_slice(x.1.to_string().as_ref()).expect("should work"))
        .collect();
    let non_taproot_inputs_v2: Vec<&secp256k1::PublicKey> = non_taproot_inputs.iter().collect();

    let taproot_inputs_v2 = if taproot_inputs_v2.is_empty() {
        None
    } else {
        Some(&taproot_inputs_v2[..])
    };

    let non_taproot_inputs_v2 = if non_taproot_inputs_v2.is_empty() {
        None
    } else {
        Some(&non_taproot_inputs_v2[..])
    };

    let silent_payment_public_data = SilentpaymentsPublicData::create(
        &secp,
        &smallest_outpoint.as_byte_array(),
        taproot_inputs_v2,
        non_taproot_inputs_v2,
    )
    .unwrap();

    let xonly_outputs: Vec<secp256k1::XOnlyPublicKey> = scan_tx_helper
        .outs
        .iter()
        .filter_map(|txout| {
            if let Ok(res) =
                secp256k1::XOnlyPublicKey::from_slice(&txout.script_pubkey.as_bytes()[2..])
            {
                Some(res)
            } else {
                None
            }
        })
        .collect();

    let xonly_outputs_v2: Vec<&secp256k1::XOnlyPublicKey> = xonly_outputs.iter().collect();

    let silent_payments_found_outputs = silentpayments_recipient_scan_outputs(
        &secp,
        &xonly_outputs_v2,
        &secp256k1::SecretKey::from_slice(secret_scan_key.as_ref()).unwrap(),
        &silent_payment_public_data,
        &receiver.0.spend_pubkey,
        dummy_lookup_function,
        Option::<BTreeMap<PublicKey, [u8; 32]>>::None,
    )
    .unwrap();
    //let pubkeys_ref: Vec<&PublicKey> = input_pub_keys.iter().collect();
    for sp_found_output in silent_payments_found_outputs {
        println!("\nres: {:?}\n", sp_found_output);
    }
}

const NON_SP_EXTERNAL_DESCRIPTOR: &str = "tr([3794bb41]tprv8ZgxMBicQKsPdnaCtnmcGNFdbPsYasZC8UJpLchusVmFodRNuKB66PhkiPWrfDhyREzj4vXtT9VfCP8mFFgy1MRo5bL4W8Z9SF241Sx4kmq/86'/1'/0'/0/*)#dg6yxkuh";
const NON_SP_INTERNAL_DESCRIPTOR: &str = "tr([3794bb41]tprv8ZgxMBicQKsPdnaCtnmcGNFdbPsYasZC8UJpLchusVmFodRNuKB66PhkiPWrfDhyREzj4vXtT9VfCP8mFFgy1MRo5bL4W8Z9SF241Sx4kmq/86'/1'/0'/1/*)#uul9mrv0";

fn main() -> Result<(), Box<dyn Error>> {
    let network = bitcoin::Network::Regtest;
    let url = "http://127.0.0.1:18443";
    let rpc_client = Client::new(url, Auth::CookieFile("/tmp/.cookie".into()))?;

    let secp = Secp256k1::new();
    let (descriptor, keymap) =
        <Descriptor<DescriptorPublicKey>>::parse_descriptor(&secp, NON_SP_EXTERNAL_DESCRIPTOR)?;
    let (internal_descriptor, internal_keymap) =
        <Descriptor<DescriptorPublicKey>>::parse_descriptor(&secp, NON_SP_INTERNAL_DESCRIPTOR)?;

    let mut obj = serde_json::Map::new();
    obj.insert("public_external_descriptor".to_string(), json!(descriptor));
    obj.insert(
        "public_internal_descriptor".to_string(),
        json!(internal_descriptor),
    );
    obj.insert(
        "private_external_descriptor".to_string(),
        json!(descriptor.to_string_with_secret(&keymap)),
    );
    obj.insert(
        "private_internal_descriptor".to_string(),
        json!(internal_descriptor.to_string_with_secret(&internal_keymap)),
    );
    println!("{}", serde_json::to_string_pretty(&obj)?);

    let mut changeset = ChangeSet::default();

    // parse descriptors
    let secp = Secp256k1::new();
    let mut index = KeychainTxOutIndex::default();
    let _ = index.insert_descriptor(Keychain::External, descriptor.clone())?;
    changeset.descriptor = Some(descriptor.clone());

    let _ = index.insert_descriptor(Keychain::Internal, internal_descriptor.clone())?;
    changeset.change_descriptor = Some(internal_descriptor);

    // create new
    let (_, chain_changeset) =
        LocalChain::from_genesis_hash(constants::genesis_block(network).block_hash());
    changeset.network = Some(network);
    changeset.local_chain = chain_changeset;
    let mut db = Store::<ChangeSet>::create_new(DB_MAGIC, DB_PATH)?;
    println!("New database {DB_PATH}");
    db.append_changeset(&changeset)?;

    let chain = Mutex::new({
        let (mut chain, _) =
            LocalChain::from_genesis_hash(constants::genesis_block(network).block_hash());
        chain.apply_changeset(&changeset.local_chain)?;
        chain
    });

    let graph = Mutex::new({
        // insert descriptors and apply loaded changeset
        let mut index = KeychainTxOutIndex::default();
        if let Some(ref desc) = changeset.descriptor {
            index.insert_descriptor(Keychain::External, desc.clone())?;
        }
        if let Some(ref change_desc) = changeset.change_descriptor {
            index.insert_descriptor(Keychain::Internal, change_desc.clone())?;
        }
        let mut graph = KeychainTxGraph::new(index);
        graph.apply_changeset(indexed_tx_graph::ChangeSet {
            tx_graph: changeset.tx_graph,
            indexer: changeset.indexer,
        });
        graph
    });

    let db = Mutex::new(db);

    let ((spk_i, spk), index_changeset) =
        KeychainTxOutIndex::next_unused_spk(&mut index, Keychain::External).expect("Must exist");
    let db = &mut *db.lock().unwrap();
    db.append_changeset(&ChangeSet {
        indexer: index_changeset,
        ..Default::default()
    })?;
    let addr = Address::from_script(spk.as_script(), network)?;

    println!("[address @ {}] {}", spk_i, addr);

    let hashes = rpc_client.generate_to_address(101, &addr)?;

    //sleep(Duration::new(10, 0));

    //for hash in hashes.0 {
    //println!("{hash}");
    //}

    let chain_tip = chain.lock().unwrap().tip();
    let start_height = 0;
    let start = Instant::now();
    let mut emitter = Emitter::new(&rpc_client, chain_tip, start_height);
    let mut db_stage = ChangeSet::default();

    let mut last_db_commit = Instant::now();
    let mut last_print = Instant::now();

    while let Some(emission) = emitter.next_block()? {
        let height = emission.block_height();

        let mut chain = chain.lock().unwrap();
        let mut graph = graph.lock().unwrap();

        let chain_changeset = chain
            .apply_update(emission.checkpoint)
            .expect("must always apply as we receive blocks in order from emitter");
        let graph_changeset = graph.apply_block_relevant(&emission.block, height);
        db_stage.merge(ChangeSet {
            local_chain: chain_changeset,
            tx_graph: graph_changeset.tx_graph,
            indexer: graph_changeset.indexer,
            ..Default::default()
        });

        // commit staged db changes in intervals
        if last_db_commit.elapsed() >= DB_COMMIT_DELAY {
            last_db_commit = Instant::now();
            if let Some(changeset) = db_stage.take() {
                db.append_changeset(&changeset)?;
            }
            println!(
                "[{:>10}s] committed to db (took {}s)",
                start.elapsed().as_secs_f32(),
                last_db_commit.elapsed().as_secs_f32()
            );
        }

        // print synced-to height and current balance in intervals
        if last_print.elapsed() >= STDOUT_PRINT_DELAY {
            last_print = Instant::now();
            let synced_to = chain.tip();
            let balance = {
                graph.graph().balance(
                    &*chain,
                    synced_to.block_id(),
                    graph.index.outpoints().iter().cloned(),
                    |(k, _), _| k == &Keychain::Internal,
                )
            };
            println!(
                "[{:>10}s] synced to {} @ {} | total: {}",
                start.elapsed().as_secs_f32(),
                synced_to.hash(),
                synced_to.height(),
                balance.total()
            );
        }
    }

    let mempool_txs = emitter.mempool()?;
    let graph_changeset = graph
        .lock()
        .unwrap()
        .batch_insert_relevant_unconfirmed(mempool_txs);
    {
        db_stage.merge(ChangeSet {
            tx_graph: graph_changeset.tx_graph,
            indexer: graph_changeset.indexer,
            ..Default::default()
        });
        if let Some(changeset) = db_stage.take() {
            db.append_changeset(&changeset)?;
        }
    }

    {
        let mut graph = graph.lock().unwrap();
        //for tx in graph.graph().full_txs().map(|tx_node| tx_node.tx) {
        //println!("{tx:?}");
        //}
    }

    {
        let graph = &*graph.lock().unwrap();
        let chain = &*chain.lock().unwrap();
        fn print_balances<'a>(
            title_str: &'a str,
            items: impl IntoIterator<Item = (&'a str, Amount)>,
        ) {
            println!("{}:", title_str);
            for (name, amount) in items.into_iter() {
                println!("    {:<10} {:>12} sats", name, amount.to_sat())
            }
        }

        let balance = graph.graph().try_balance(
            chain,
            chain.get_chain_tip()?,
            graph.index.outpoints().iter().cloned(),
            |(k, _), _| k == &Keychain::Internal,
        )?;

        let confirmed_total = balance.confirmed + balance.immature;
        let unconfirmed_total = balance.untrusted_pending + balance.trusted_pending;

        print_balances(
            "confirmed",
            [
                ("total", confirmed_total),
                ("spendable", balance.confirmed),
                ("immature", balance.immature),
            ],
        );
        print_balances(
            "unconfirmed",
            [
                ("total", unconfirmed_total),
                ("trusted", balance.trusted_pending),
                ("untrusted", balance.untrusted_pending),
            ],
        );
    }

    let available_txouts = {
        let chain = &*chain.lock().unwrap();
        let mut graph = graph.lock().unwrap();
        let chain_tip = chain.get_chain_tip().unwrap();
        let outpoints = graph.index.outpoints().iter().cloned();
        // for tx in graph.graph().full_txs().map(|tx_node| tx_node.tx) {
        // println!("{tx:?}");
        // }

        graph
            .graph()
            .try_filter_chain_unspents(chain, chain_tip, outpoints)
            .unwrap()
            .filter(|(_, txout)| {
                if let ChainPosition::Confirmed { .. } = &txout.chain_position {
                    txout.is_confirmed_and_spendable(chain_tip.height)
                } else {
                    false
                }
            })
            .collect::<Vec<_>>()
    };

    {
        let chain = &*chain.lock().unwrap();
        let mut graph = graph.lock().unwrap();

        let ((kechain, spk_i), fulltxo) = &available_txouts[0];
        let txo_desc = graph
            .index
            .keychains()
            .find(|(keychain, _)| *keychain == *kechain)
            .expect("keychain must exist")
            .1
            .at_derivation_index(*spk_i)
            .expect("i can't be hardened");
        let pubkey = descriptor.at_derivation_index(*spk_i).unwrap();
        let secp_sp = secp256k1::Secp256k1::new();
        let bitcoin_secp = bitcoin::secp256k1::Secp256k1::new();
        let (bitcoin_privkey, sender_keypair) = if let DescriptorSecretKey::XPrv(privkey) =
            keymap.iter().collect::<Vec<_>>()[0].1
        {
            (
                privkey.xkey,
                Keypair::from_secret_key(
                    &secp_sp,
                    &secp256k1::SecretKey::from_slice(privkey.xkey.private_key.as_ref()).unwrap(),
                ),
            )
        } else {
            panic!("just break");
        };

        dbg!(fulltxo.txout.value);
        let sender_outpoint = SilentPaymentOutpoint(fulltxo.outpoint);
        let (silent_payment_code, _) = parse_silent_payment_keys();
        let tweaked_sp_pubkey = silentpayments_sender_create_outputs(
            &secp_sp,
            &mut [&silent_payment_code.create_recipient(0)],
            &sender_outpoint.as_byte_array(),
            Some(&[&sender_keypair]),
            None,
        )
        .unwrap();

        let bitcoin_sp_pubkey =
            bitcoin::XOnlyPublicKey::from_slice(&tweaked_sp_pubkey[0].serialize())?;

        let sp_final_address = Address::p2tr(
            &bitcoin_secp,
            bitcoin_sp_pubkey,
            None,
            bitcoin::Network::Regtest,
        );

        let mut assets = Assets::new();
        for (_, desc) in graph.index.keychains() {
            match desc {
                Descriptor::Wpkh(wpkh) => {
                    assets = assets.add(wpkh.clone().into_inner());
                }
                Descriptor::Tr(tr) => {
                    assets = assets.add(tr.internal_key().clone());
                }
                _ => (),
            }
        }

        let plan = txo_desc.plan(&assets).ok().unwrap();

        let unsigned_tx = Transaction {
            version: transaction::Version::TWO,
            lock_time: absolute::LockTime::from_height(chain.get_chain_tip()?.height)?,
            input: vec![TxIn {
                previous_output: fulltxo.outpoint,
                sequence: plan
                    .relative_timelock
                    .map_or(Sequence::ENABLE_RBF_NO_LOCKTIME, Sequence::from),
                ..Default::default()
            }],
            output: vec![TxOut {
                value: fulltxo.txout.value - Amount::from_sat(1000),
                script_pubkey: sp_final_address.into(),
            }],
        };

        let mut psbt = Psbt::from_unsigned_tx(unsigned_tx)?;
        let psbt_input = &mut psbt.inputs[0];
        plan.update_psbt_input(psbt_input);
        psbt_input.witness_utxo = Some(fulltxo.txout.clone());

        let sign_res = psbt.sign(&bitcoin_privkey, &bitcoin_secp);
        let _ = sign_res.map_err(|errors| anyhow::anyhow!("failed to sign PSBT {:?}", errors))?;

        let mut obj = serde_json::Map::new();
        obj.insert("psbt".to_string(), json!(psbt.to_string()));
        println!("{}", serde_json::to_string_pretty(&obj)?);

        psbt.finalize_mut(&Secp256k1::new())
            .map_err(|errors| anyhow::anyhow!("failed to finalize PSBT {errors:?}"))?;

        let tx = psbt.extract_tx()?;

        let txid = rpc_client.send_raw_transaction(&tx).unwrap();

        println!("txid: {}", txid);
        let hashes = rpc_client.generate_to_address(1, &addr)?;
    }

    {
        let (silent_payment_code, silent_payments_secret_key) = parse_silent_payment_keys();
        let chain = Mutex::new({
            let (mut chain, _) =
                LocalChain::from_genesis_hash(constants::genesis_block(network).block_hash());
            chain.apply_changeset(&changeset.local_chain)?;
            chain
        });
        let chain_tip = chain.lock().unwrap().tip();
        let start_height = 0;
        let mut emitter = Emitter::new(&rpc_client, chain_tip, start_height);

        while let Some(emission) = emitter.next_block()? {
            let block = emission.block.clone();
            // Iterate transactions ingoring coinbase transaction
            for tx in block.txdata.iter().skip(1) {
                let scan_tx_helper = ScanTxHelperV2 {
                    ins: tx
                        .input
                        .iter()
                        .map(|txin| {
                            let bitcoin::OutPoint { ref txid, vout } = txin.previous_output;
                            (
                                rpc_client.get_raw_transaction(txid, None).unwrap().output
                                    [vout as usize]
                                    .clone()
                                    .script_pubkey
                                    .into_bytes(),
                                txin.clone(),
                            )
                        })
                        .collect(),
                    outs: tx
                        .output
                        .clone()
                        .into_iter()
                        .filter(|output| output.script_pubkey.is_p2tr())
                        .collect(),
                };
                scan_tx(
                    &silent_payment_code,
                    &silent_payments_secret_key,
                    scan_tx_helper.clone(),
                );
                println!("helper: {:?}", scan_tx_helper);
            }
        }
    }
    Ok(())
}

pub type c_int = i32;
pub type c_uchar = u8;
pub type c_uint = u32;
pub type size_t = usize;

/// This might not match C's `c_char` exactly.
/// The way we use it makes it fine either way but this type shouldn't be used outside of the library.
pub type c_char = i8;

pub use core::ffi::c_void;
unsafe extern "C" fn dummy_lookup_function(_: *const c_uchar, _: *const c_void) -> *const c_uchar {
    let x = 5_u8;
    &x as *const c_uchar
}
