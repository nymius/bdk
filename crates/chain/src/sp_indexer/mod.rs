//! Indexing of [BIP 352] Silent Payments outputs.
//!
//! [`SpTxIndex`] scans transactions for outputs sent to a [BIP 352] silent payment
//! recipient. Only P2TR outputs are scanned.
//!
//! Because the silent payment scan requires data derived from a transaction's inputs, the
//! caller must pre-load a [`PrevoutsSummary`] per transaction via
//! [`SpTxIndex::index_prevouts_summary`] before indexing it with the [`Indexer`] methods.
//! Transactions whose summary was not pre-loaded are skipped.
//!
//! [BIP 352]: https://bips.xyz/352
//! [`Indexer`]: crate::Indexer
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use bdk_core::Merge;
use bitcoin::{OutPoint, Transaction, TxOut, Txid};
use bitcoin_silent_payments::secp256k1::{
    silentpayments::recipient::PrevoutsSummary, XOnlyPublicKey,
};
use sp_keychain_index::SpKeychainIndex;

/// Index of outputs received to a silent payment recipient.
pub mod sp_keychain_index;

/// A changeset of newly indexed silent payment data.
///
/// Produced by the [`Indexer`] methods and [`SpTxIndex::index_prevouts_summary`]; apply it
/// to a [`SpTxIndex`] with [`Indexer::apply_changeset`].
///
/// [`Indexer`]: crate::Indexer
/// [`Indexer::apply_changeset`]: crate::Indexer::apply_changeset
#[derive(Clone, Debug, Default, PartialEq)]
#[must_use]
pub struct ChangeSet {
    /// Changes to the underlying [`SpKeychainIndex`].
    pub keychain: sp_keychain_index::ChangeSet,
}

impl Merge for ChangeSet {
    fn merge(&mut self, other: Self) {
        self.keychain.merge(other.keychain);
    }

    fn is_empty(&self) -> bool {
        self.keychain.is_empty()
    }
}

impl From<SpTxIndex> for ChangeSet {
    fn from(value: SpTxIndex) -> Self {
        Self {
            keychain: value.keychain.into(),
        }
    }
}

/// An index for Silent Payments transactions.
#[derive(Clone, Debug, PartialEq)]
pub struct SpTxIndex {
    /// Maps txids to their prevouts summaries needed for Silent Payments scanning.
    pub txid_to_prevouts_summary: BTreeMap<Txid, PrevoutsSummary>,
    /// The underlying keychain index for tracking spouts.
    pub keychain: SpKeychainIndex,
}

impl SpTxIndex {
    /// Index a transaction's prevouts summary.
    ///
    /// This method is used to pre-load transaction summaries that are needed for
    /// Silent Payments indexing. Summaries must be pre-loaded via this method
    /// before calling `index_tx` from the Indexer trait.
    pub fn index_prevouts_summary(&mut self, txid: Txid, prevouts_summary: PrevoutsSummary) {
        self.txid_to_prevouts_summary.insert(txid, prevouts_summary);
    }

    /// Index a transaction with its prevouts summary.
    fn index_tx_with_summary(
        &mut self,
        tx: &Transaction,
        prevouts_summary: &PrevoutsSummary,
    ) -> ChangeSet {
        let mut changeset = ChangeSet::default();

        let mut tx_xonly_vouts: Vec<u32> = vec![];
        let mut tx_xonlys: Vec<XOnlyPublicKey> = vec![];
        for (txout, vout) in tx.output.iter().zip(0u32..) {
            let spk_bytes = txout.script_pubkey.as_bytes();
            if spk_bytes.len() == 34 && spk_bytes[0] == 0x51 && spk_bytes[1] == 0x20 {
                let mut xonly_pubkey = [0u8; 32];
                xonly_pubkey.clone_from_slice(&spk_bytes[2..34]);
                if let Ok(xonly) = XOnlyPublicKey::from_byte_array(xonly_pubkey) {
                    tx_xonly_vouts.push(vout);
                    tx_xonlys.push(xonly);
                }
            }
        }

        let maybe_found_outputs = self
            .keychain
            .rx
            .scan(prevouts_summary, tx_xonlys.as_slice());

        match maybe_found_outputs {
            Ok(found_outputs) if !found_outputs.is_empty() => {
                let txid = tx.compute_txid();
                self.txid_to_prevouts_summary
                    .insert(txid, *prevouts_summary);

                for (idx, tx_xonly) in tx_xonlys.iter().enumerate() {
                    if let Some((_xonly, sp_meta)) = found_outputs
                        .iter()
                        .find(|(xonly, _sp_meta)| tx_xonly == xonly)
                    {
                        let vout = tx_xonly_vouts[idx];
                        let outpoint = OutPoint { txid, vout };
                        let txout = tx
                            .tx_out(vout as usize)
                            .expect("computed from tx itself, cannot be outside boundaries");
                        let changes = self.keychain.index_spout(outpoint, txout.clone(), *sp_meta);
                        changeset.keychain.merge(changes);
                    }
                }
            }
            _ => (),
        }

        changeset
    }
}

// Implement the Indexer trait for SpTxIndex
impl crate::indexer::Indexer for SpTxIndex {
    type ChangeSet = ChangeSet;

    /// Silent payments cannot index a floating `TxOut`: BIP-352 scanning derives the
    /// output key from the transaction's inputs via a `PrevoutsSummary`, which is only
    /// available through `index_tx` after a summary is pre-loaded with
    /// `index_prevouts_summary`. This method intentionally returns an empty `ChangeSet`.
    fn index_txout(&mut self, _outpoint: OutPoint, _txout: &TxOut) -> Self::ChangeSet {
        ChangeSet::default()
    }

    fn index_tx(&mut self, tx: &Transaction) -> Self::ChangeSet {
        let txid = tx.compute_txid();
        if let Some(prevouts_summary) = self.txid_to_prevouts_summary.get(&txid).cloned() {
            self.index_tx_with_summary(tx, &prevouts_summary)
        } else {
            ChangeSet::default()
        }
    }

    fn apply_changeset(&mut self, changeset: Self::ChangeSet) {
        self.keychain.apply_changeset(changeset.keychain);
    }

    fn initial_changeset(&self) -> Self::ChangeSet {
        ChangeSet {
            keychain: self.keychain.initial_changeset(),
        }
    }

    /// Check if a transaction is relevant to the index.
    fn is_tx_relevant(&self, tx: &Transaction) -> bool {
        let txid = tx.compute_txid();
        let input_matches = tx
            .input
            .iter()
            .any(|input| self.keychain.spouts.contains_key(&input.previous_output));
        let output_matches = tx
            .output
            .iter()
            .zip(0u32..)
            .filter_map(|(txout, vout)| {
                if txout.script_pubkey.is_p2tr() {
                    Some(OutPoint { txid, vout })
                } else {
                    None
                }
            })
            .any(|outpoint| self.keychain.spouts.contains_key(&outpoint));

        input_matches || output_matches
    }
}
