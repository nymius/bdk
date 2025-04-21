use bdk_chain::{tx_graph, BlockId, CheckPoint, ConfirmationBlockTime, Indexer, TxGraph};
use bdk_silentpayments::receive::SpReceiveError;
use bitcoin::key::TweakedPublicKey;
use bitcoin::{ScriptBuf, Transaction};
use serde_json::json;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use std::env;
use std::str::FromStr;

use anyhow::{self, bail, Context};

use clap::{self, Args, Parser, Subcommand};

use bdk_silentpayments::{
    bitcoin::{
        bip32::DerivationPath,
        secp256k1::{PublicKey, Scalar, Secp256k1, SecretKey},
        Block, OutPoint, Psbt, TxOut, Txid,
    },
    encoding::SilentPaymentCode,
    receive::{Scanner, SpOut},
    send::XprivSilentPaymentSender,
};

use bdk_bitcoind_rpc::{
    bitcoincore_rpc::{Auth, Client, RpcApi},
    Emitter,
};

use miniscript::{descriptor::DescriptorSecretKey, Descriptor};

#[allow(dead_code)]
const SILENT_PAYMENT_SPEND_WIF: &str = "cRFcZbp7cAeZGsnYKdgSZwH6drJ3XLnPSGcjLNCpRy28tpGtZR11";
#[allow(dead_code)]
const SILENT_PAYMENT_SCAN_WIF: &str = "cTiSJ8p2zpGSkWGkvYFWfKurgWvSi9hdvzw9GEws18kS2VRPNS24";
#[allow(dead_code)]
const SILENT_PAYMENT_SPEND_SECRETKEY: &str =
    "6d87b87889341032b6509470233601a722834808def6454450bf42a9af22d263";
const SILENT_PAYMENT_SCAN_SECRETKEY: &str =
    "b700f356a63cbab8da1fb7b3e5cbbfbb4e56d83c8b7271d0bc6f92882f70aa85";
const SILENT_PAYMENT_ENCODED: &str = "sprt1qqw7zfpjcuwvq4zd3d4aealxq3d669s3kcde4wgr3zl5ugxs40twv2qccgvszutt7p796yg4h926kdnty66wxrfew26gu2gk5h5hcg4s2jqyascfz";

pub struct SpIndexer<T, A> {
    prevout_source: T,
    pub scanner: Scanner,
    // NOTE: Redundancy of the OutPoint here is to have a fast way to query particular SpOuts
    // associated with a particular Outpoint.
    // NOTE: Do not create SpIndex::spouts method which include OutPoint inside iterator because there is
    // no reason to have the outpoint twice here (one in the tuple and another inside the SpOut)
    // and a DoubleEndedIterator can also be obtained using the BTreeMap::values method
    pub indexes: SpIndexes,
    pub tx_graph: TxGraph<A>,
}

pub struct SpIndexes {
    pub spouts: BTreeMap<OutPoint, SpOut>,
    pub txid_to_shared_secret: BTreeMap<Txid, PublicKey>,
    pub label_to_output: BTreeSet<(Option<u32>, SpOut)>,
    pub label_to_tweak: BTreeMap<u32, Scalar>,
}

pub trait PrevoutSource {
    fn get_tx_prevouts(&self, tx: &Transaction) -> Vec<TxOut>;
}

impl<A: bdk_chain::Anchor, T: PrevoutSource> SpIndexer<T, A> {
    pub fn new(prevout_source: T, scanner: Scanner) -> Self {
        Self {
            prevout_source,
            scanner,
            indexes: SpIndexes {
                spouts: BTreeMap::default(),
                label_to_output: BTreeSet::default(),
                label_to_tweak: BTreeMap::default(),
                txid_to_shared_secret: BTreeMap::default(),
            },
            tx_graph: TxGraph::default(),
        }
    }

    fn is_tx_relevant(&self, tx: &Transaction) -> bool {
        let prevouts = self.prevout_source.get_tx_prevouts(tx);
        let input_matches = tx
            .input
            .iter()
            .any(|input| self.indexes.spouts.contains_key(&input.previous_output));
        let ecdh_shared_secret = self
            .scanner
            .compute_shared_secret(tx, &prevouts)
            .expect("infallible");
        if let Ok(spouts) = self
            .scanner
            .scan_txouts(tx, ecdh_shared_secret)
            .collect::<Result<Vec<SpOut>, _>>()
        {
            input_matches || !spouts.is_empty()
        } else {
            input_matches
        }
    }

    fn index_tx(&mut self, tx: &Transaction) -> Result<(), SpReceiveError> {
        let prevouts = self.prevout_source.get_tx_prevouts(tx);
        let ecdh_shared_secret = self
            .scanner
            .compute_shared_secret(tx, &prevouts)
            .expect("infallible");
        for spout_found in self.scanner.scan_txouts(tx, ecdh_shared_secret) {
            if let Ok(spout) = spout_found {
                if !self
                    .indexes
                    .txid_to_shared_secret
                    .contains_key(&tx.compute_txid())
                {
                    self.indexes
                        .txid_to_shared_secret
                        .insert(tx.compute_txid(), ecdh_shared_secret);
                    self.tx_graph.insert_tx(tx.clone());
                }
                self.indexes.spouts.insert(spout.outpoint, spout.clone());
            }
        }
        Ok(())
    }
}

impl SpIndexes {
    pub fn txouts_in_tx(&self, txid: Txid) -> impl DoubleEndedIterator<Item = &SpOut> {
        self.spouts
            .range(OutPoint::new(txid, u32::MIN)..=OutPoint::new(txid, u32::MAX))
            .map(|(_op, spout)| spout)
    }

    pub fn txout(&self, outpoint: OutPoint) -> Option<TxOut> {
        self.spouts.get(&outpoint).map(Into::into)
    }
}

#[derive(Args, Debug, Clone)]
pub struct RpcArgs {
    /// RPC URL
    #[clap(env = "RPC_URL", long, default_value = "127.0.0.1:8332")]
    url: String,
    /// RPC auth username
    #[clap(env = "RPC_USER", long)]
    rpc_user: Option<String>,
    /// RPC auth password
    #[clap(env = "RPC_PASS", long)]
    rpc_password: Option<String>,
}

struct Custom(Client);

impl PrevoutSource for Custom {
    fn get_tx_prevouts(&self, tx: &Transaction) -> Vec<TxOut> {
        let mut prevouts = <Vec<TxOut>>::new();
        let outpoint_refs = tx.input.iter().map(|x| x.previous_output);
        for OutPoint { txid, vout } in outpoint_refs {
            let prev_tx = self
                .0
                .get_raw_transaction_info(&txid, None)
                .expect("reckless")
                .transaction()
                .expect("reckless");
            let prevout = prev_tx.tx_out(vout as usize).expect("reckless").clone();
            prevouts.push(prevout);
        }
        prevouts
    }
}

impl RpcArgs {
    fn new_client(&self) -> anyhow::Result<Client> {
        Ok(Client::new(
            &self.url,
            match (&self.rpc_user, &self.rpc_password) {
                (None, None) => Auth::None,
                (Some(user), Some(pass)) => Auth::UserPass(user.clone(), pass.clone()),
                (Some(_), None) => panic!("rpc auth: missing rpc_pass"),
                (None, Some(_)) => panic!("rpc auth: missing rpc_user"),
            },
        )?)
    }
}

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
pub struct SpArgs {
    #[clap(subcommand)]
    pub command: SilentPaymentCommands,
}

#[derive(Subcommand, Debug, Clone)]
pub enum SilentPaymentCommands {
    /// Replace PSBT single taproot output with a silent payment derived taproot output
    ToSilentPayment {
        /// Silent payment code from which you want to derive the script pub key
        #[clap(default_value = SILENT_PAYMENT_ENCODED)]
        silent_payment_code: String,
        /// The original PSBT you are trying to replace outputs from
        #[clap(long)]
        psbt: String,
        /// Private descriptor you need to get the private keys to create the silent payment script
        /// pubkey
        #[clap(long)]
        descriptor: Option<String>,
        /// Debug print the PSBT
        #[clap(long, short)]
        debug: bool,
    },

    /// Use bitcoind RPC to scan the blockchain looking for silent payment outputs belonging to the
    /// provided silent payment code
    Scan {
        /// The scan key needed to generate the shared secret in combination with tx inputs
        #[clap(long, default_value = SILENT_PAYMENT_SCAN_SECRETKEY)]
        scan_sk: SecretKey,
        /// Silent payment code to get the spend pub key from to derive the full script pubkey
        #[clap(default_value = SILENT_PAYMENT_ENCODED)]
        silent_payment_code: String,
        /// The RPC parameters to communicate with bitcoind RPC
        #[clap(flatten)]
        rpc_args: RpcArgs,
    },
}

fn main() -> anyhow::Result<()> {
    let args = SpArgs::parse();

    match args.command {
        SilentPaymentCommands::ToSilentPayment {
            silent_payment_code,
            psbt,
            descriptor,
            debug,
        } => {
            let mut psbt = Psbt::from_str(psbt.as_str())?;

            let single_external_txout = psbt
                .unsigned_tx
                .output
                .first()
                .expect("send to multiple addresses not implemented yet")
                .clone();

            if !single_external_txout.script_pubkey.is_p2tr() {
                bail!("can only replace p2tr outputs");
            }

            let desc_str = match descriptor {
                Some(s) => s,
                None => env::var("DESCRIPTOR").context("unable to sign")?,
            };

            let secp = Secp256k1::new();
            let (_, keymap) = Descriptor::parse_descriptor(&secp, &desc_str)?;
            if keymap.is_empty() {
                bail!("unable to sign")
            }

            let master_privkey = match keymap.iter().next().expect("not empty") {
                (_, DescriptorSecretKey::XPrv(privkey)) => privkey.xkey,
                _ => unimplemented!("multi xkey signer"),
            };

            let sp_sender = XprivSilentPaymentSender::new(master_privkey);

            let silent_payment_code = SilentPaymentCode::try_from(silent_payment_code.as_str())?;

            let mut outputs_and_derivation_paths = <Vec<(OutPoint, DerivationPath)>>::new();
            for (psbt_input, txin) in psbt.inputs.iter().zip(psbt.unsigned_tx.input.clone()) {
                for (fingerprint, path) in psbt_input
                    .bip32_derivation
                    .values()
                    .chain(psbt_input.tap_key_origins.values().map(|x| &x.1))
                {
                    if *fingerprint == master_privkey.fingerprint(&secp) {
                        outputs_and_derivation_paths.push((txin.previous_output, path.clone()));
                        break;
                    }
                }
            }

            let sp_script_pubkeys =
                sp_sender.send_to(&outputs_and_derivation_paths, &[silent_payment_code])?;

            let txout = TxOut {
                value: single_external_txout.value,
                script_pubkey: sp_script_pubkeys
                    .first()
                    .expect("only provided one silent payment code")
                    .clone(),
            };

            psbt.unsigned_tx.output = psbt
                .unsigned_tx
                .output
                .into_iter()
                .map(|x| {
                    if x.script_pubkey == single_external_txout.script_pubkey {
                        txout.clone()
                    } else {
                        x
                    }
                })
                .collect();

            if debug {
                dbg!(psbt);
            } else {
                // print base64 encoded psbt
                let fee = psbt.fee()?.to_sat();
                let mut obj = serde_json::Map::new();
                obj.insert("psbt".to_string(), json!(psbt.to_string()));
                obj.insert("fee".to_string(), json!(fee));
                println!("{}", serde_json::to_string_pretty(&obj)?);
            };
        }
        SilentPaymentCommands::Scan {
            scan_sk,
            silent_payment_code,
            rpc_args,
        } => {
            let silent_payment_code = SilentPaymentCode::try_from(silent_payment_code.as_str())?;

            let rpc_client = rpc_args.new_client()?;
            let rpc_client_v2 = rpc_args.new_client()?;
            let custom_client = Custom(rpc_client_v2);
            let chain_tip = CheckPoint::new(BlockId {
                height: 0u32,
                hash: rpc_client.get_block_hash(0)?,
            });
            let label_lookup = HashMap::<PublicKey, (Scalar, u32)>::new();
            let scanner = Scanner::new(scan_sk, silent_payment_code.spend, label_lookup);
            let mut sp_indexer = SpIndex::new(custom_client, scanner);

            let mut emitter = Emitter::new(&rpc_client, chain_tip, 0);
            while let Some(emission) = emitter.next_block()? {
                let _height = emission.block_height();
                let Block {
                    header: _header,
                    txdata,
                } = emission.block;
                for tx in txdata.iter().skip(1) {
                    if !tx.output.iter().any(|x| x.script_pubkey.is_p2tr()) {
                        continue;
                    }
                    sp_indexer.index_tx(tx);
                }
            }
            let spouts = sp_indexer
                .spouts
                .values()
                .map(|x| x.outpoint.txid)
                .collect::<Vec<_>>();
            let mut obj = serde_json::Map::new();
            obj.insert("silent_payments_found".to_string(), json!(&spouts));
            println!("{}", serde_json::to_string_pretty(&obj)?);

            let _mempool_txs = emitter.mempool()?;
        }
    };

    Ok(())
}
