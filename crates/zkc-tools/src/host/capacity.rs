//! Application-selected operational ceilings, separate from proof semantics.
use super::{admission::LoadLimits, inputs::*};
use serde_json::{Value as Json, json};
use zkc_backends::Policy;
use zkc_runtime::interactive::{Limits, ValueBudget, WorkBudget};

/// A host may raise the default collection count within installed hard limits,
/// or lower byte/work ceilings. Neither proof nor deployment data grants this
/// authority. Setup and provider-specific ceilings keep their existing owners.
#[derive(Clone, Copy, Debug)]
pub struct NativeCapacity {
    /// Maximum elements in one numeric collection.
    pub elements: usize,
    /// Maximum group elements in one collection.
    pub groups: usize,
    /// Bytes in one canonical wire frame.
    pub wire_bytes: usize,
    /// Retained bytes in one native value.
    pub value_bytes: usize,
    /// Instructions and loop iterations per runner (cumulative for proof retries).
    pub work: WorkBudget,
    /// Live retained payload and cumulative allocation charge, in bytes.
    pub values: ValueBudget,
}
impl Default for NativeCapacity {
    fn default() -> Self {
        let p = Policy::default();
        Self {
            elements: p.max_table_elements,
            groups: p.max_groups,
            wire_bytes: p.max_wire_bytes,
            value_bytes: p.max_value_bytes,
            work: WorkBudget::default(),
            values: ValueBudget::default(),
        }
    }
}
impl NativeCapacity {
    /// Installed hard ceilings; defaults may be lower. These do not bound peak RSS.
    pub const HARD_MAX: Self = Self {
        elements: 1 << 20,
        groups: 32768,
        wire_bytes: INPUT_LIMIT,
        value_bytes: Limits::VALUE_BYTES,
        work: WorkBudget {
            instructions: Limits::INSTRUCTIONS,
            iterations: Limits::ITERATIONS,
        },
        values: ValueBudget {
            live_bytes: Limits::VALUE_BYTES,
            total_bytes: Limits::TOTAL_VALUE_BYTES,
        },
    };
    pub fn validate(&self) -> Result<()> {
        if self.elements > Self::HARD_MAX.elements
            || self.groups > Self::HARD_MAX.groups
            || self.wire_bytes > Self::HARD_MAX.wire_bytes
            || self.value_bytes > Self::HARD_MAX.value_bytes
            || self.work.instructions > Self::HARD_MAX.work.instructions
            || self.work.iterations > Self::HARD_MAX.work.iterations
            || self.values.live_bytes > Self::HARD_MAX.values.live_bytes
            || self.values.total_bytes > Self::HARD_MAX.values.total_bytes
        {
            return Err("native-capacity-limit".into());
        }
        Ok(())
    }
    pub(crate) fn backend(&self) -> Policy {
        Policy {
            max_table_elements: self.elements,
            max_groups: self.groups,
            max_wire_bytes: self.wire_bytes,
            max_value_bytes: self.value_bytes,
            ..Policy::default()
        }
    }
    pub(crate) fn loading(&self) -> LoadLimits {
        LoadLimits {
            bytes: self.values.live_bytes.min(self.values.total_bytes),
            work: self.values.total_bytes,
            ..LoadLimits::default()
        }
    }
    /// Stable report record. This quota record is deliberately absent from the
    /// semantic binding root; changing a quota cannot change successful values.
    pub fn record(&self) -> Json {
        json!([
            "zkc.native-capacity/2",
            self.elements.to_string(),
            self.groups.to_string(),
            self.wire_bytes.to_string(),
            self.value_bytes.to_string(),
            [
                self.work.instructions.to_string(),
                self.work.iterations.to_string()
            ],
            [
                self.values.live_bytes.to_string(),
                self.values.total_bytes.to_string()
            ]
        ])
    }
    /// Parse the application's bounded quota file. Unknown fields are refused.
    pub fn parse(bytes: &[u8]) -> Result<Self> {
        let value = parse(bytes, 4096)?;
        let row = array(&value, 7)?;
        if text(&row[0])? != "zkc.native-capacity/2" {
            return Err("native-capacity-format".into());
        }
        let size =
            |v| usize::try_from(natural(v)?).map_err(|_| String::from("native-capacity-limit"));
        let work = array(&row[5], 2)?;
        let values = array(&row[6], 2)?;
        let result = Self {
            elements: size(&row[1])?,
            groups: size(&row[2])?,
            wire_bytes: size(&row[3])?,
            value_bytes: size(&row[4])?,
            work: WorkBudget {
                instructions: natural(&work[0])?,
                iterations: natural(&work[1])?,
            },
            values: ValueBudget {
                live_bytes: size(&values[0])?,
                total_bytes: size(&values[1])?,
            },
        };
        result.validate()?;
        Ok(result)
    }
    pub(crate) fn wire(&self, value: &Json) -> Result<Vec<u8>> {
        // Check the knowable binary length before allocating its hex decoding.
        self.check_wire(text(value)?.len() / 2)?;
        unhex(value)
    }
    pub(crate) fn check_wire(&self, bytes: usize) -> Result<()> {
        if bytes > self.wire_bytes {
            return Err("native-capacity-wire".into());
        }
        Ok(())
    }
}
