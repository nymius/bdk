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
    /// Map of txids to the [`PrevoutsSummary`] needed to scan each transaction.
    pub txid_to_prevouts_summary: BTreeMap<Txid, PrevoutsSummary>,
    /// Changes to the underlying [`SpKeychainIndex`].
    pub keychain: sp_keychain_index::ChangeSet,
}

impl Merge for ChangeSet {
    fn merge(&mut self, other: Self) {
        // We use `extend` instead of `BTreeMap::append` due to performance issues with `append`.
        // Refer to https://github.com/rust-lang/rust/issues/34666#issuecomment-675658420
        self.txid_to_prevouts_summary
            .extend(other.txid_to_prevouts_summary);
        self.keychain.merge(other.keychain);
    }

    fn is_empty(&self) -> bool {
        self.txid_to_prevouts_summary.is_empty() && self.keychain.is_empty()
    }
}

impl From<SpTxIndex> for ChangeSet {
    fn from(value: SpTxIndex) -> Self {
        Self {
            txid_to_prevouts_summary: value.txid_to_prevouts_summary.clone(),
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
    /// before calling `index_tx` or `index_txout` from the Indexer trait.
    pub fn index_prevouts_summary(
        &self,
        txid: Txid,
        prevouts_summary: PrevoutsSummary,
    ) -> ChangeSet {
        let mut changeset = ChangeSet::default();
        changeset
            .txid_to_prevouts_summary
            .insert(txid, prevouts_summary);
        changeset
    }

    /// Index a txout with its prevouts summary.
    fn index_txout_with_summary(
        &self,
        outpoint: &OutPoint,
        txout: &TxOut,
        prevouts_summary: &PrevoutsSummary,
    ) -> ChangeSet {
        let mut changeset = ChangeSet::default();

        let spk_bytes = txout.script_pubkey.as_bytes();
        if spk_bytes.len() == 34 && spk_bytes[0] == 0x51 && spk_bytes[1] == 0x20 {
            let mut xonly_pubkey = [0u8; 32];
            xonly_pubkey.clone_from_slice(&spk_bytes[2..34]);
            let xonly = [XOnlyPublicKey::from_byte_array(xonly_pubkey).expect("p2tr output")];
            let maybe_found_outputs = self.keychain.rx.scan(prevouts_summary, &xonly);
            match maybe_found_outputs {
                Ok(ref found_outputs) if let Some((_, sp_meta)) = found_outputs.iter().next() => {
                    changeset
                        .txid_to_prevouts_summary
                        .insert(outpoint.txid, *prevouts_summary);
                    let changes = self
                        .keychain
                        .index_spout(*outpoint, txout.clone(), *sp_meta);
                    changeset.keychain.merge(changes);
                }
                _ => (),
            }
        }

        changeset
    }

    /// Index a transaction with its prevouts summary.
    fn index_tx_with_summary(
        &self,
        tx: &Transaction,
        prevouts_summary: &PrevoutsSummary,
    ) -> ChangeSet {
        let mut changeset = ChangeSet::default();

        let tx_outputs: BTreeMap<XOnlyPublicKey, (u32, TxOut)> = tx
            .output
            .iter()
            .zip(0u32..)
            .filter_map(|(txout, idx)| {
                let spk_bytes = txout.script_pubkey.as_bytes();
                if spk_bytes.len() == 34 && spk_bytes[0] == 0x51 && spk_bytes[1] == 0x20 {
                    let mut xonly_pubkey = [0u8; 32];
                    xonly_pubkey.clone_from_slice(&spk_bytes[2..34]);
                    Some((
                        XOnlyPublicKey::from_byte_array(xonly_pubkey).expect("p2tr output"),
                        (idx, txout.clone()),
                    ))
                } else {
                    None
                }
            })
            .collect();

        let tx_outputs_ref: Vec<XOnlyPublicKey> = tx_outputs.keys().copied().collect();
        let maybe_found_outputs = self
            .keychain
            .rx
            .scan(prevouts_summary, tx_outputs_ref.as_slice());

        match maybe_found_outputs {
            Ok(found_outputs) if !found_outputs.is_empty() => {
                let txid = tx.compute_txid();
                changeset
                    .txid_to_prevouts_summary
                    .insert(txid, *prevouts_summary);

                for (xonly, sp_meta) in found_outputs {
                    let (vout, txout) = tx_outputs.get(&xonly).expect("should be listed");
                    let outpoint = OutPoint { txid, vout: *vout };
                    let changes = self.keychain.index_spout(outpoint, txout.clone(), sp_meta);
                    changeset.keychain.merge(changes);
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

    fn index_txout(&mut self, outpoint: OutPoint, txout: &TxOut) -> Self::ChangeSet {
        if let Some(prevouts_summary) = self.txid_to_prevouts_summary.get(&outpoint.txid).cloned() {
            self.index_txout_with_summary(&outpoint, txout, &prevouts_summary)
        } else {
            ChangeSet::default()
        }
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
        self.txid_to_prevouts_summary
            .extend(changeset.txid_to_prevouts_summary);
        self.keychain.apply_changeset(changeset.keychain);
    }

    fn initial_changeset(&self) -> Self::ChangeSet {
        ChangeSet {
            txid_to_prevouts_summary: self.txid_to_prevouts_summary.clone(),
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
