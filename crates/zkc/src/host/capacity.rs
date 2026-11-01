//! Application-selected operational ceilings, separate from proof semantics.
use super::admission::LoadLimits;
use crate::io::bytes::*;
use serde_json::{Value as Json, json};
use zkc_cpu::{CpuBackend, Policy};
use zkc_runtime::vm::{Limits, ValueBudget, WorkBudget};

/// One Host work allowance outside the VM ledgers: the value used when the
/// application selects none, and the most an application may authorize.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Allowance {
    pub default: u64,
    pub maximum: u64,
}
impl Allowance {
    /// Check an application selection without clamping it.
    pub fn admits(self, value: u64) -> bool {
        value <= self.maximum
    }
}
/// The Host policy owner of every native work allowance that is not an
/// instruction, iteration or retained-value budget. Run, proof and Function
/// entries read their defaults and maxima from here; each child of a Function
/// invocation receives what remains of the parent's selected allowance.
pub struct Allowances;
impl Allowances {
    /// Ring expression substitution work per role.
    pub const RING_WORK: Allowance = Allowance {
        default: zkc_cpu::ring::DEFAULT_WORK_LIMIT,
        maximum: zkc_cpu::ring::DEFAULT_WORK_LIMIT,
    };
    /// Nested sequence traversal work per role: three units per examined node
    /// and call, a retained validated root counting as one node.
    pub const SEQUENCE_WORK: Allowance = Allowance {
        default: 16_777_216,
        maximum: 16_777_216,
    };
    /// External construction primitive work per role: one unit per hash call,
    /// hashed byte, permutation, observe or sample.
    pub const EXTERNAL_WORK: Allowance = Allowance {
        default: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
        maximum: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
    };
    /// Draws granted to one managed service or transcript invocation.
    pub const SERVICE_DRAWS: Allowance = Allowance {
        default: 1_000_000,
        maximum: 1_000_000,
    };
}

/// A host may raise the default collection counts and instruction and
/// iteration budgets within installed hard limits, or lower byte and logical
/// work ceilings. Neither proof nor deployment data grants this authority.
/// Setup and provider-specific ceilings keep their existing owners.
#[derive(Clone, Copy, Debug)]
pub struct Capacity {
    /// Maximum elements in one numeric collection.
    pub elements: usize,
    /// Maximum group elements in one collection.
    pub groups: usize,
    /// Bytes in one canonical wire frame.
    pub wire_bytes: usize,
    /// Retained bytes in one native value.
    pub value_bytes: usize,
    /// Instructions, loop iterations and logical work bytes per runner
    /// (cumulative for proof retries).
    pub work: WorkBudget,
    /// Live retained payload and cumulative fresh allocation, in bytes.
    pub values: ValueBudget,
}
impl Default for Capacity {
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
impl Capacity {
    /// Installed hard ceilings; defaults may be lower. These do not bound peak RSS.
    pub const HARD_MAX: Self = Self {
        elements: 1 << 20,
        groups: 32768,
        wire_bytes: INPUT_LIMIT,
        value_bytes: Limits::VALUE_BYTES,
        work: WorkBudget {
            instructions: Limits::MAX_INSTRUCTIONS,
            iterations: Limits::MAX_ITERATIONS,
            logical_bytes: Limits::LOGICAL_BYTES,
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
            || self.work.logical_bytes > Self::HARD_MAX.work.logical_bytes
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
            "zkc.native-capacity/0",
            self.elements.to_string(),
            self.groups.to_string(),
            self.wire_bytes.to_string(),
            self.value_bytes.to_string(),
            [
                self.work.instructions.to_string(),
                self.work.iterations.to_string(),
                self.work.logical_bytes.to_string()
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
        if text(&row[0])? != "zkc.native-capacity/0" {
            return Err("native-capacity-format".into());
        }
        let size =
            |v| usize::try_from(natural(v)?).map_err(|_| String::from("native-capacity-limit"));
        let work = array(&row[5], 3)?;
        let values = array(&row[6], 2)?;
        let result = Self {
            elements: size(&row[1])?,
            groups: size(&row[2])?,
            wire_bytes: size(&row[3])?,
            value_bytes: size(&row[4])?,
            work: WorkBudget {
                instructions: natural(&work[0])?,
                iterations: natural(&work[1])?,
                logical_bytes: natural(&work[2])?,
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

#[cfg(test)]
mod tests {
    use super::*;
    fn record(instructions: u64, iterations: u64) -> Vec<u8> {
        let mut capacity = Capacity::default();
        capacity.work.instructions = instructions;
        capacity.work.iterations = iterations;
        capacity.record().to_string().into_bytes()
    }
    #[test]
    fn work_defaults_are_separate_from_their_hard_maxima() {
        let defaults = Capacity::default().work;
        assert_eq!(defaults, WorkBudget::default());
        assert_eq!(defaults.instructions, Limits::INSTRUCTIONS);
        assert_eq!(defaults.iterations, Limits::ITERATIONS);
        assert_eq!(
            Capacity::HARD_MAX.work.instructions,
            Limits::MAX_INSTRUCTIONS
        );
        assert_eq!(Capacity::HARD_MAX.work.iterations, Limits::MAX_ITERATIONS);
        const {
            assert!(Limits::INSTRUCTIONS < Limits::MAX_INSTRUCTIONS);
            assert!(Limits::ITERATIONS < Limits::MAX_ITERATIONS);
        }
        for (instructions, iterations) in [
            (2 * Limits::INSTRUCTIONS, 2 * Limits::ITERATIONS),
            (Limits::MAX_INSTRUCTIONS, Limits::MAX_ITERATIONS),
        ] {
            let parsed = Capacity::parse(&record(instructions, iterations)).unwrap();
            assert_eq!(parsed.work.instructions, instructions);
            assert_eq!(parsed.work.iterations, iterations);
        }
        for (instructions, iterations) in [
            (Limits::MAX_INSTRUCTIONS + 1, Limits::ITERATIONS),
            (Limits::INSTRUCTIONS, Limits::MAX_ITERATIONS + 1),
        ] {
            assert_eq!(
                Capacity::parse(&record(instructions, iterations)).unwrap_err(),
                "native-capacity-limit"
            );
        }
    }
}
