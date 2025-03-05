// 1. Generate silent payment code
// 2. Generate new key pair A
// 3. Get address from key pair A
// 4. Fund key pair A
// 5. Sync
// 6. Generate silent payment address from silent payment code
// 7. Send funds to silent payment code
// 8. Sync
// 9. Check funds are there

use std::io::{self, Write};
use std::thread::sleep;
use std::time::Duration;
use std::{error::Error, str::FromStr};

// Import necessary libraries and modules
use bip39::Mnemonic;
use bitcoin::bip32::{DerivationPath, Xpriv};
use corepc_client::client_sync::v28::Client;
use corepc_client::client_sync::Auth;
use rand::fill;
use secp256k1::silentpayments::silentpayments_sender_create_outputs;
use secp256k1::Keypair;
use secp256k1::SecretKey;

// Import types from the silentpayments library
use rust_bip352::utils::code::{SilentPaymentCode, SilentPaymentHrp, VersionStrict};
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

use bdk_electrum::{
    electrum_client::{self, ElectrumApi},
    BdkElectrumClient,
};

pub use anyhow;

const DB_MAGIC: &[u8] = b"bdk_example_silent_payment";
const DB_PATH: &str = ".bdk_example_silent_payment.db";

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

fn parse_keys() -> (SilentPaymentCode, SecretKey) {
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

fn main() -> Result<(), Box<dyn Error>> {
    let network = bitcoin::Network::Regtest;
    let client = Client::new_with_auth(
        "http://127.0.0.1:18443",
        Auth::CookieFile("/tmp/.cookie".into()),
    )?;

    let secp = Secp256k1::new();
    let mut seed = [0x00; 32];
    fill(&mut seed);

    let m = bip32::Xpriv::new_master(network, &seed)?;
    let fp = m.fingerprint(&secp);
    let path = if m.network.is_mainnet() {
        "86h/0h/0h"
    } else {
        "86h/1h/0h"
    };

    let descriptors: Vec<String> = [0, 1]
        .iter()
        .map(|i| format!("tr([{fp}]{m}/{path}/{i}/*)"))
        .collect();
    let external_desc = &descriptors[0];
    let internal_desc = &descriptors[1];
    let (descriptor, keymap) =
        <Descriptor<DescriptorPublicKey>>::parse_descriptor(&secp, external_desc)?;
    let (internal_descriptor, internal_keymap) =
        <Descriptor<DescriptorPublicKey>>::parse_descriptor(&secp, internal_desc)?;

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

    let hashes = client.generate_to_address(101, &addr)?;

    sleep(Duration::new(10, 0));

    //for hash in hashes.0 {
        //println!("{hash}");
    //}

    let config = electrum_client::Config::builder()
        .validate_domain(matches!(network, Network::Bitcoin))
        .build();

    let electrum_client = electrum_client::Client::from_config("tcp://127.0.0.1:60401", config)?;
    let bdk_electrum_client = BdkElectrumClient::new(electrum_client);

    // Tell the electrum client about the txs we've already got locally so it doesn't re-download them
    bdk_electrum_client.populate_tx_cache(
        graph
            .lock()
            .unwrap()
            .graph()
            .full_txs()
            .map(|tx_node| tx_node.tx),
    );

    let request = {
        let graph = &*graph.lock().unwrap();
        let chain = &*chain.lock().unwrap();

        FullScanRequest::builder()
            .chain_tip(chain.tip())
            .spks_for_keychain(
                Keychain::External,
                graph
                    .index
                    .unbounded_spk_iter(Keychain::External)
                    .into_iter()
                    .flatten(),
            )
            .spks_for_keychain(
                Keychain::Internal,
                graph
                    .index
                    .unbounded_spk_iter(Keychain::Internal)
                    .into_iter()
                    .flatten(),
            )
            .inspect({
                let mut once = BTreeSet::new();
                move |k, spk_i, _| {
                    if once.insert(k) {
                        eprint!("\nScanning {}: {} ", k, spk_i);
                    } else {
                        eprint!("{} ", spk_i);
                    }
                    io::stdout().flush().expect("must flush");
                }
            })
    };

    let res = bdk_electrum_client
        .full_scan::<_>(request, 1, 1, false)
        .context("scanning the blockchain")?;

    let db_changeset = {
        let mut chain = chain.lock().unwrap();
        let mut graph = graph.lock().unwrap();

        let chain_changeset =
            chain.apply_update(res.chain_update.expect("request has chain tip"))?;

        let mut indexed_tx_graph_changeset =
            indexed_tx_graph::ChangeSet::<ConfirmationBlockTime, _>::default();
        let keychain_changeset = graph.index.reveal_to_target_multi(&res.last_active_indices);
        indexed_tx_graph_changeset.merge(keychain_changeset.into());
        indexed_tx_graph_changeset.merge(graph.apply_update(res.tx_update));

        ChangeSet {
            local_chain: chain_changeset,
            tx_graph: indexed_tx_graph_changeset.tx_graph,
            indexer: indexed_tx_graph_changeset.indexer,
            ..Default::default()
        }
    };

    db.append_changeset(&db_changeset)?;

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
        let (silent_payment_code, _) = parse_keys();
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

        let send_raw_transaction = client.send_raw_transaction(&tx).unwrap();
        let txid = send_raw_transaction.txid().unwrap();

        println!("txid: {}", txid);
    }

    Ok(())
}
