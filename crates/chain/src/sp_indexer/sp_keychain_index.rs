use alloc::collections::BTreeMap;
use bdk_core::Merge;
use bitcoin::{OutPoint, ScriptBuf, TxOut, Txid};
use bitcoin_silent_payments::receive::SpMeta;
use bitcoin_silent_payments::receive::SpRx;

type SpOut = (SpMeta, TxOut);

/// Index of outputs received to a [BIP 352] silent payment recipient.
///
/// Discovered outputs ("spouts") are recorded with both directions of lookup: from the P2TR
/// script pubkey to the outpoint, and from the outpoint to the scanned metadata and [`TxOut`].
///
/// [BIP 352]: https://bips.xyz/352
#[derive(Clone, Debug, PartialEq)]
pub struct SpKeychainIndex {
    /// The silent payment recipient used to scan for outputs.
    pub rx: SpRx,
    /// Lookup from a discovered P2TR script pubkey to the outpoint carrying it.
    pub spk_to_spout: BTreeMap<ScriptBuf, OutPoint>,
    /// Lookup from an outpoint to the silent payment metadata and [`TxOut`] discovered there.
    pub spouts: BTreeMap<OutPoint, SpOut>,
}

impl SpKeychainIndex {
    /// Create a new, empty index for the silent payment recipient `rx`.
    pub fn new(rx: SpRx) -> Self {
        Self {
            rx,
            spk_to_spout: BTreeMap::default(),
            spouts: BTreeMap::default(),
        }
    }

    /// Get the silent payment output associated with the P2TR script pubkey `tr_spk`, if any.
    pub fn by_script(&self, tr_spk: &ScriptBuf) -> Option<&SpOut> {
        self.spk_to_spout
            .get(tr_spk)
            .and_then(|outpoint| self.spouts.get(outpoint))
    }

    /// Iterate over silent payment outputs tagged with label `m`.
    ///
    /// Pass `None` to iterate over unlabeled outputs.
    pub fn by_label(&self, m: Option<u32>) -> impl Iterator<Item = &SpOut> {
        self.spouts
            .values()
            .filter(move |(spmeta, _)| spmeta.label == m)
    }

    /// Iterate over the silent payment outputs created by the transaction with the given `txid`.
    pub fn txouts_in_tx(&self, txid: Txid) -> impl DoubleEndedIterator<Item = &SpOut> {
        self.spouts
            .range(
                OutPoint {
                    txid,
                    vout: u32::MIN,
                }..=OutPoint {
                    txid,
                    vout: u32::MAX,
                },
            )
            .map(|(_op, spout)| spout)
    }

    /// Record a newly discovered silent payment output.
    pub(super) fn index_spout(
        &self,
        outpoint: OutPoint,
        txout: TxOut,
        spmeta: SpMeta,
    ) -> ChangeSet {
        let mut changeset = ChangeSet {
            rx: Some(self.rx.clone()),
            ..Default::default()
        };
        changeset
            .spk_to_spout
            .insert(txout.script_pubkey.clone(), outpoint);
        changeset.spouts.insert(outpoint, (spmeta, txout));
        changeset
    }

    /// Apply a [`ChangeSet`] to the index.
    ///
    /// A changeset without an [`SpRx`] receiver is ignored. Otherwise, nothing is applied if
    /// the receiver's keyset does not match the index's keyset, or if any script pubkey
    /// mapping is missing its silent payment output.
    pub fn apply_changeset(&mut self, changeset: ChangeSet) {
        let rx = if let Some(ref rx) = changeset.rx {
            rx
        } else {
            return;
        };

        if self.rx.keys != rx.keys {
            return;
        }

        if !changeset
            .spk_to_spout
            .values()
            .all(|v| changeset.spouts.contains_key(v))
        {
            return;
        }

        self.spk_to_spout.extend(changeset.spk_to_spout);
        self.spouts.extend(changeset.spouts);

        for label_num in rx.dump_tweaks() {
            let _ = self.rx.tweak(label_num);
        }
    }

    /// Get a [`ChangeSet`] representing the full state of the index.
    pub fn initial_changeset(&self) -> ChangeSet {
        ChangeSet {
            rx: Some(self.rx.clone()),
            spk_to_spout: self.spk_to_spout.clone(),
            spouts: self.spouts.clone(),
        }
    }
}

/// Error returned when a [`ChangeSet`] is inconsistent with a [`SpKeychainIndex`].
#[derive(Debug)]
pub enum ChangeSetError {
    /// The changeset's silent payment keyset does not match the index's keyset.
    KeysetDoesNotMatch,
    /// A script pubkey mapping has no matching silent payment output in the changeset.
    MissingSpoutForSpk,
}

impl core::fmt::Display for ChangeSetError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            ChangeSetError::KeysetDoesNotMatch => {
                write!(f, "the keyset does not match with the index keyset")
            }
            ChangeSetError::MissingSpoutForSpk => {
                write!(f, "missing silent payment data for script pubkey")
            }
        }
    }
}

impl core::error::Error for ChangeSetError {}

/// A changeset of newly discovered silent payment data for a [`SpKeychainIndex`].
#[derive(Clone, Debug, Default, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
#[must_use]
pub struct ChangeSet {
    /// The updated silent payment receiver state, if changed.
    pub rx: Option<SpRx>,
    /// New script pubkey to outpoint mappings.
    pub spk_to_spout: BTreeMap<ScriptBuf, OutPoint>,
    /// New silent payment outputs by outpoint.
    pub spouts: BTreeMap<OutPoint, SpOut>,
}

impl ChangeSet {
    /// Set the silent payment receiver state recorded by this changeset.
    pub fn insert_sp_rx(&mut self, rx: &SpRx) {
        self.rx = Some(rx.clone());
    }
}

impl Merge for ChangeSet {
    fn merge(&mut self, other: Self) {
        match (self.rx.as_mut(), other.rx.as_ref()) {
            (Some(self_rx), Some(other_rx)) => {
                for label_num in other_rx.dump_tweaks() {
                    let _ = self_rx.tweak(label_num);
                }
            }
            (None, Some(other_rx)) => self.rx = Some(other_rx.clone()),
            _ => (),
        }
        // We use `extend` instead of `BTreeMap::append` due to performance issues with `append`.
        // Refer to https://github.com/rust-lang/rust/issues/34666#issuecomment-675658420
        self.spk_to_spout.extend(other.spk_to_spout);
        self.spouts.extend(other.spouts);
    }

    fn is_empty(&self) -> bool {
        self.rx.is_none() && self.spk_to_spout.is_empty() && self.spouts.is_empty()
    }
}

impl From<SpKeychainIndex> for ChangeSet {
    fn from(value: SpKeychainIndex) -> Self {
        Self {
            rx: Some(value.rx),
            spk_to_spout: value.spk_to_spout,
            spouts: value.spouts,
        }
    }
}

impl TryFrom<ChangeSet> for SpKeychainIndex {
    type Error = ();

    fn try_from(value: ChangeSet) -> Result<Self, Self::Error> {
        let rx = if let Some(ref rx) = value.rx {
            rx
        } else {
            return Err(());
        };

        if !value
            .spk_to_spout
            .values()
            .all(|v| value.spouts.contains_key(v))
        {
            return Err(());
        }

        let mut sp_keychain_index = SpKeychainIndex::new(rx.clone());
        sp_keychain_index.apply_changeset(value);
        Ok(sp_keychain_index)
    }
}
