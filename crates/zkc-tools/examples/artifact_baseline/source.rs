//! Refuse any algorithm change rather than pretending to interpret arbitrary source.
use crate::{Result, codec::*, ensure};
use serde_json::Value;
use std::path::Path;
pub struct Source {
    pub source: Value,
    pub descriptor: Value,
    pub n: Option<usize>,
    pub source_hash: String,
    pub descriptor_hash: String,
}
impl Source {
    pub fn load(source: &Path, descriptor: &Path) -> Result<Self> {
        let s = read(source, 1 << 20)?;
        let d = read(descriptor, 1 << 20)?;
        let source: Value = serde_json::from_slice(&s)?;
        let descriptor: Value = serde_json::from_slice(&d)?;
        let mut normalized = source.clone();
        ensure(source[0] == "zkc.protocol/1", "unsupported-source-format")?;
        let n = if source[4][0][1] == "sumcheck" {
            let n = string(&source[4][0][3][0][1])?;
            let rank: usize = n.parse()?;
            ensure(
                (1..=12).contains(&rank) && rank.to_string() == n && source[4][2][3][0][1] == n,
                "source-rank",
            )?;
            normalized[4][0][3][0][1] = Value::String("3".into());
            normalized[4][2][3][0][1] = Value::String("3".into());
            Some(rank)
        } else {
            None
        };
        let (sh, dh) = if n.is_some() {
            (
                "fc5b70bb9ca38736fe65e5c3b31fc3bb4be5e69d66f5b1dd38b3df871d1cd7b0",
                "1cc29d317a1d977d3fa81c808d80e9a88dc9429f1eecd77749c1eeb3b85e171a",
            )
        } else {
            (
                "29fec74a21365f58175135c02de404c019b9a97a15ad1285e1ca61bd13d476e5",
                "32d0048ec024f263effba23fcf5b2888d2ca8f7f92753819d8798b83a152595f",
            )
        };
        ensure(
            hash(&serde_json::to_vec(&normalized)?) == sh,
            "unsupported-source",
        )?;
        ensure(
            hash(&serde_json::to_vec(&descriptor)?) == dh,
            "unsupported-descriptor",
        )?;
        Ok(Self {
            source,
            descriptor,
            n,
            source_hash: hash(&s),
            descriptor_hash: hash(&d),
        })
    }
}

/// Fixed receive policy of the pinned two-factor algorithm, in canonical order.
/// These source sites are independent of generated function/SSA names.
pub fn receive_setups() -> Value {
    serde_json::json!([
        ["interactive", "V", "root_f", "vk"],
        ["interactive", "V", "root_g", "vk"],
        ["opening", "V", "proof_message", "vk"]
    ])
}
