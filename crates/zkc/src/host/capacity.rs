//! Application-selected operational ceilings, separate from proof semantics.
use super::admission::LoadLimits;
use crate::io::bytes::*;
use serde_json::{Value as Json, json};
use zkc_cpu::{CpuBackend, Policy};
use zkc_runtime::vm::{ExecutionLedger, Limits, LiveReservation, ValueBudget, WorkBudget};

/// The extent over which one allowance counts. Allowances with equal numbers
/// but different scopes or units remain separate selections.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    /// One admitted Entry across all of its calls, including the calls a
    /// Function makes to it.
    Entry,
    /// One Entry invocation, from input preparation through output
    /// publication: the invocation accounting root, and the instruction meter
    /// that a Function's interpreter and reached children pool there.
    Invocation,
    /// One participant runner, cumulative across the attempts of one proof
    /// call.
    Runner,
    /// One proof attempt.
    Attempt,
    /// One individual operation: a value, collection, frame, message, service,
    /// admission algorithm or call.
    Operation,
}
/// One Host policy allowance: what it counts, where it counts, the value used
/// when the application selects none, and the most an application may
/// authorize. A selection above the maximum is refused, never clamped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Allowance {
    pub unit: &'static str,
    pub scope: Scope,
    pub default: u64,
    pub maximum: u64,
}
impl Allowance {
    /// Check an application selection without clamping it.
    pub fn admits(self, value: u64) -> bool {
        value <= self.maximum
    }
}
/// The Host policy owner of every native allowance beside the per-operation
/// and per-runner fields of the [`Capacity`] record: the invocation root's
/// [`InvocationLimits`], the supplied material's [`MaterialLimits`], loading
/// work, and the work allowances below. Run, proof and Function entries read
/// their defaults and maxima from here; each child of a Function invocation
/// receives what remains of the parent's selected cumulative allowance.
pub struct Allowances;
impl Allowances {
    /// Ring expression substitution work per role.
    pub const RING_WORK: Allowance = Allowance {
        unit: "Ring expression substitution work units",
        scope: Scope::Runner,
        default: zkc_cpu::ring::DEFAULT_WORK_LIMIT,
        maximum: zkc_cpu::ring::DEFAULT_WORK_LIMIT,
    };
    /// Nested sequence traversal work per role: three units per examined node
    /// and call, a retained validated root counting as one node.
    pub const SEQUENCE_WORK: Allowance = Allowance {
        unit: "sequence traversal work units",
        scope: Scope::Runner,
        default: zkc_cpu::Sequence::DEFAULT_WORK_LIMIT,
        maximum: zkc_cpu::Sequence::DEFAULT_WORK_LIMIT,
    };
    /// External construction primitive work per role: one unit per hash call,
    /// hashed byte, permutation, observe or sample.
    pub const EXTERNAL_WORK: Allowance = Allowance {
        unit: "external primitive work units",
        scope: Scope::Runner,
        default: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
        maximum: CpuBackend::DEFAULT_EXTERNAL_WORK_LIMIT,
    };
    /// Draws granted to one managed service or transcript invocation.
    pub const SERVICE_DRAWS: Allowance = Allowance {
        unit: "draws",
        scope: Scope::Operation,
        default: 1_000_000,
        maximum: 1_000_000,
    };
    /// Cumulative work of one interface admission algorithm: schema
    /// validation, or supply reconstruction with public selection indexing.
    pub const INTERFACE_WORK: Allowance = Allowance {
        unit: "interface admission work units",
        scope: Scope::Operation,
        default: crate::entry::InterfaceLimits::DEFAULT.work as u64,
        maximum: crate::entry::InterfaceLimits::MAXIMUM.work as u64,
    };
    /// Retained descriptor bytes of the interface schema summaries, of each
    /// reconstructed supply plan and of a Function's native descriptor cache.
    pub const INTERFACE_DESCRIPTORS: Allowance = Allowance {
        unit: "retained descriptor bytes",
        scope: Scope::Operation,
        default: crate::entry::InterfaceLimits::DEFAULT.descriptor_bytes as u64,
        maximum: crate::entry::InterfaceLimits::MAXIMUM.descriptor_bytes as u64,
    };
    /// Service draw allowances that a Function reserves for its children
    /// before issuing their roots: 64 default service allowances by default,
    /// and at most one maximal allowance for every dispatch a Function can
    /// make.
    pub const FUNCTION_SERVICE_DRAWS: Allowance = Allowance {
        unit: "reserved draws",
        scope: Scope::Invocation,
        default: 64 * Self::SERVICE_DRAWS.default,
        maximum: Self::SERVICE_DRAWS.maximum * Self::DISPATCHES.maximum,
    };
    /// Retained Function call receipts, including failed calls.
    pub const JOURNAL_EVENTS: Allowance = Allowance {
        unit: "retained call receipts",
        scope: Scope::Invocation,
        default: 256,
        maximum: 4096,
    };
    /// Joint and Function dispatch occurrences, including repeated loop steps.
    pub const DISPATCHES: Allowance = Allowance {
        unit: "dispatch occurrences",
        scope: Scope::Invocation,
        default: zkc_runtime::host::joint::RunLimits::HARD_MAX.steps as u64,
        maximum: zkc_runtime::host::joint::RunLimits::HARD_MAX.steps as u64,
    };
    /// Completed or discarded trials of one producing proof call.
    pub const ATTEMPTS: Allowance = Allowance {
        unit: "attempts",
        scope: Scope::Invocation,
        default: 1,
        maximum: crate::proof::AttemptPolicy::MAX_ATTEMPTS,
    };
    /// Proof buffer bytes of one attempt, including framing.
    pub const ATTEMPT_PROOF_BYTES: Allowance = Allowance {
        unit: "proof bytes",
        scope: Scope::Attempt,
        default: zkc_format::proof::MAX_PROOF_BYTES as u64,
        maximum: zkc_format::proof::MAX_PROOF_BYTES as u64,
    };
    /// Bytes the invocation root holds live at once.
    pub const INVOCATION_LIVE_BYTES: Allowance = Allowance {
        unit: "live retained bytes of the invocation root",
        scope: Scope::Invocation,
        default: InvocationLimits::DEFAULT.live_bytes as u64,
        maximum: InvocationLimits::MAXIMUM.live_bytes as u64,
    };
    /// Fresh allocation charged to the invocation root, never refunded.
    pub const INVOCATION_TOTAL_BYTES: Allowance = Allowance {
        unit: "cumulative fresh allocation bytes of the invocation root",
        scope: Scope::Invocation,
        default: InvocationLimits::DEFAULT.total_bytes as u64,
        maximum: InvocationLimits::MAXIMUM.total_bytes as u64,
    };
    /// Logical work charged to the invocation root.
    pub const INVOCATION_LOGICAL_BYTES: Allowance = Allowance {
        unit: "logical work bytes of the invocation root",
        scope: Scope::Invocation,
        default: InvocationLimits::DEFAULT.logical_bytes,
        maximum: InvocationLimits::MAXIMUM.logical_bytes,
    };
    /// The pooled instruction meter of a Function invocation: its interpreter
    /// and every reached child share the root, so the record's `instructions`
    /// bound their sum, and each child runs on what remains.
    pub const FUNCTION_INSTRUCTIONS: Allowance = Allowance {
        unit: "instructions of the Function interpreter and every reached child",
        scope: Scope::Invocation,
        default: Limits::INSTRUCTIONS,
        maximum: Capacity::HARD_MAX.work.instructions,
    };
    /// The pooled iteration meter of a Function invocation, selected by the
    /// record's `iterations` as the instruction meter is by `instructions`.
    pub const FUNCTION_ITERATIONS: Allowance = Allowance {
        unit: "loop iterations of the Function interpreter and every reached child",
        scope: Scope::Invocation,
        default: Limits::ITERATIONS,
        maximum: Capacity::HARD_MAX.work.iterations,
    };
    /// Cumulative work of one input loading: each input node, wire scan or
    /// native measurement, each byte read and each retained estimate,
    /// including cache hits.
    pub const LOADING_WORK: Allowance = Allowance {
        unit: "loading work units",
        scope: Scope::Operation,
        default: 1 << 28,
        maximum: 1 << 28,
    };
    /// Wire bytes of one proof call's public statement, counted at every role
    /// operand a public value initializes, including shared owners.
    pub const PUBLIC_BYTES: Allowance = Allowance {
        unit: "public statement wire bytes, counted at every role operand",
        scope: Scope::Operation,
        default: MaterialLimits::DEFAULT.public_bytes as u64,
        maximum: MaterialLimits::MAXIMUM.public_bytes as u64,
    };
    /// Bytes of the named references one memory request binds.
    pub const REFERENCE_BYTES: Allowance = Allowance {
        unit: "bytes of the named references one request binds",
        scope: Scope::Invocation,
        default: MaterialLimits::DEFAULT.reference_bytes as u64,
        maximum: MaterialLimits::MAXIMUM.reference_bytes as u64,
    };
    /// Setup material supplied with one invocation, counting every copy the
    /// Host holds: each verifier-key copy a proof makes for a public port, and
    /// for a Function invocation the material of all of its deployments.
    pub const SETUP_BYTES: Allowance = Allowance {
        unit: "setup material bytes, counted at every copy",
        scope: Scope::Invocation,
        default: MaterialLimits::DEFAULT.setup_bytes as u64,
        maximum: MaterialLimits::MAXIMUM.setup_bytes as u64,
    };
    /// Bytes of the setup imports an admitted proof Entry retains for reuse
    /// across its calls. A call whose imports do not fit is not refused; it
    /// imports without retaining.
    pub const RETAINED_IMPORTS: Allowance = Allowance {
        unit: "retained bytes of persistent setup imports",
        scope: Scope::Entry,
        default: MaterialLimits::DEFAULT.retained_imports as u64,
        maximum: MaterialLimits::MAXIMUM.retained_imports as u64,
    };
}

/// The allowances over material an application supplies beside its named
/// values: one proof call's public statement, one request's named references,
/// one invocation's setup material and the setup imports a proof Entry
/// retains across calls. Each is its own allowance with its own unit and
/// scope ([`Allowances`]); none derives from a runner's capacity. A selection
/// above a maximum refuses with that allowance's code; it is never clamped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MaterialLimits {
    /// [`Allowances::PUBLIC_BYTES`]; exceeding it refuses with
    /// `entry-input-limit`.
    pub public_bytes: usize,
    /// [`Allowances::REFERENCE_BYTES`]; exceeding it refuses with
    /// `entry-request-limit`.
    pub reference_bytes: usize,
    /// [`Allowances::SETUP_BYTES`]; exceeding it refuses with
    /// `entry-setup-limit`.
    pub setup_bytes: usize,
    /// [`Allowances::RETAINED_IMPORTS`].
    pub retained_imports: usize,
}
impl MaterialLimits {
    pub const DEFAULT: Self = Self {
        public_bytes: 64 << 20,
        reference_bytes: 256 << 20,
        setup_bytes: 64 << 20,
        retained_imports: 64 << 20,
    };
    pub const MAXIMUM: Self = Self::DEFAULT;
    /// Refuse a selection above an installed maximum with that allowance's
    /// code, without clamping it.
    pub fn validate(&self) -> Result<()> {
        for (selected, maximum, code) in [
            (
                self.public_bytes,
                Self::MAXIMUM.public_bytes,
                "entry-public-bytes-limit",
            ),
            (
                self.reference_bytes,
                Self::MAXIMUM.reference_bytes,
                "entry-reference-bytes-limit",
            ),
            (
                self.setup_bytes,
                Self::MAXIMUM.setup_bytes,
                "entry-setup-bytes-limit",
            ),
            (
                self.retained_imports,
                Self::MAXIMUM.retained_imports,
                "entry-retained-imports-limit",
            ),
        ] {
            if selected > maximum {
                return Err(code.into());
            }
        }
        Ok(())
    }
    pub fn record(&self) -> Json {
        json!({"public_bytes":self.public_bytes,"reference_bytes":self.reference_bytes,
            "setup_bytes":self.setup_bytes,"retained_imports":self.retained_imports})
    }
}
impl Default for MaterialLimits {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// The refusal codes of one kind of Host work and storage that an invocation
/// root charges. The root's ledger refuses without naming the allowance it
/// could not afford, so the Host charges each effect's work and bytes
/// separately and reports the code of the allowance that refused: `work` when
/// the root's logical work allowance refuses, `bytes` when its fresh or live
/// byte allowance does. Work is charged first, so a bytes refusal leaves that
/// work committed; committed charges are never refunded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RootCharge {
    pub(crate) work: &'static str,
    pub(crate) bytes: &'static str,
}
impl RootCharge {
    /// Input loading with its file reads, captured references and imported
    /// setup material.
    pub(crate) const LOADING: Self = Self {
        work: "artifact-input-work-limit",
        bytes: "artifact-input-bytes-limit",
    };
    /// A proof's binding root, with the canonical encodings of its public
    /// values and the public copies of its verifier keys.
    pub(crate) const BINDING: Self = Self {
        work: "native-proof-binding-work-limit",
        bytes: "native-proof-binding-bytes-limit",
    };
    /// A received proof that the Host retains for its record codec.
    pub(crate) const RECEIVED_PROOF: Self = Self {
        work: "native-proof-received-work-limit",
        bytes: "native-proof-received-bytes-limit",
    };
    /// The proof bytes of a completed attempt, which the Host retains.
    pub(crate) const ATTEMPT_PROOF: Self = Self {
        work: "native-attempt-proof-work-limit",
        bytes: "native-attempt-proof-bytes-limit",
    };
    /// A Function's own Host work and storage: its invocation context, frames,
    /// environments, call receipts and typed values, and the requests and
    /// results of its children.
    pub(crate) const FUNCTION: Self = Self {
        work: "entry-host-work-limit",
        bytes: "entry-host-bytes-limit",
    };
    /// Charge known work and fresh bytes before their effect: the work, then
    /// the bytes.
    pub(crate) fn charge(self, ledger: &ExecutionLedger, work: u64, fresh: usize) -> Result<()> {
        let budget = |logical_bytes| WorkBudget {
            instructions: 0,
            iterations: 0,
            logical_bytes,
        };
        ledger.charge(budget(work), 0).map_err(|_| self.work)?;
        ledger.charge(budget(0), fresh).map_err(|_| self.bytes)?;
        Ok(())
    }
    /// Hold live bytes in the root without a fresh charge, as for custody
    /// that passes without a new allocation.
    pub(crate) fn hold(self, ledger: &ExecutionLedger, bytes: usize) -> Result<LiveReservation> {
        Ok(ledger.reserve_live(bytes).map_err(|_| self.bytes)?)
    }
    /// Charge and hold storage the Host allocates: its work, its fresh bytes,
    /// then its live bytes. Without a root nothing is charged.
    pub(crate) fn reserve(
        self,
        ledger: Option<&ExecutionLedger>,
        work: u64,
        bytes: usize,
    ) -> Result<Option<LiveReservation>> {
        let Some(ledger) = ledger else {
            return Ok(None);
        };
        self.charge(ledger, work, bytes)?;
        self.hold(ledger, bytes).map(Some)
    }
    /// Charge and hold storage whose logical work equals its bytes, as a copy
    /// reads every byte it writes.
    pub(crate) fn reserve_bytes(
        self,
        ledger: Option<&ExecutionLedger>,
        bytes: usize,
    ) -> Result<Option<LiveReservation>> {
        self.reserve(ledger, bytes as u64, bytes)
    }
}

/// The invocation accounting root's own allowances. They are separate from
/// every runner's allowances in [`Capacity`], even where the numbers agree:
/// the root charges the Host's work and storage for the whole invocation,
/// together with the runners that share it, while each runner's ledger counts
/// only that runner. A selection above [`InvocationLimits::MAXIMUM`] refuses
/// with `native-invocation-limit`; it is never clamped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvocationLimits {
    /// Bytes the root holds live at once: Host-retained storage, values in the
    /// Host's custody, and the whole live allowance of each runner that shares
    /// the root.
    pub live_bytes: usize,
    /// Cumulative fresh allocation charged to the root, never refunded.
    pub total_bytes: usize,
    /// Cumulative logical work charged to the root.
    pub logical_bytes: u64,
}
impl InvocationLimits {
    pub const DEFAULT: Self = Self {
        live_bytes: Limits::VALUE_BYTES,
        total_bytes: Limits::TOTAL_VALUE_BYTES,
        logical_bytes: Limits::LOGICAL_BYTES,
    };
    pub const MAXIMUM: Self = Self::DEFAULT;
    /// Refuse a selection above the installed maximum without clamping it.
    pub fn validate(&self) -> Result<()> {
        if self.live_bytes > Self::MAXIMUM.live_bytes
            || self.total_bytes > Self::MAXIMUM.total_bytes
            || self.logical_bytes > Self::MAXIMUM.logical_bytes
        {
            return Err("native-invocation-limit".into());
        }
        Ok(())
    }
    /// A root that no runner shares. Host-side work is never metered in
    /// instructions or iterations, so it has no allowance of either.
    pub(crate) fn root(&self) -> ExecutionLedger {
        self.pooled(0, 0)
    }
    /// A root that runners share, with the instruction and iteration meter
    /// they pool there.
    pub(crate) fn pooled(&self, instructions: u64, iterations: u64) -> ExecutionLedger {
        ExecutionLedger::new(
            ValueBudget {
                live_bytes: self.live_bytes,
                total_bytes: self.total_bytes,
            },
            WorkBudget {
                instructions,
                iterations,
                logical_bytes: self.logical_bytes,
            },
        )
    }
    pub fn record(&self) -> Json {
        json!({"live_bytes":self.live_bytes,"total_bytes":self.total_bytes,
            "logical_bytes":self.logical_bytes})
    }
}
impl Default for InvocationLimits {
    fn default() -> Self {
        Self::DEFAULT
    }
}

/// A host may raise the default collection counts and instruction and
/// iteration budgets within installed hard limits, or lower byte and logical
/// work ceilings. Neither proof nor deployment data grants this authority.
/// Setup and provider-specific ceilings keep their existing owners.
///
/// Each field selects one allowance. Element, group, wire and value bytes
/// bound one operation. Instructions and iterations are the fuel of each
/// standalone runner, cumulative across the attempts of one proof call; in a
/// Function invocation they are the meter that its interpreter and reached
/// children pool in the invocation root, each child running on what remains
/// ([`Allowances::FUNCTION_INSTRUCTIONS`]). Logical work and the live and
/// cumulative fresh bytes bound each runner's own ledger only; the invocation
/// root has its own allowances ([`InvocationLimits`]).
#[derive(Clone, Copy, Debug)]
pub struct Capacity {
    /// Maximum elements in one numeric collection or complete nested message.
    pub elements: usize,
    /// Maximum group elements in one collection.
    pub groups: usize,
    /// Bytes in one canonical wire frame.
    pub wire_bytes: usize,
    /// Retained bytes in one native value.
    pub value_bytes: usize,
    /// Instructions and loop iterations per runner (cumulative for proof
    /// retries; pooled in a Function invocation), and logical work bytes per
    /// runner.
    pub work: WorkBudget,
    /// Live retained payload and cumulative fresh allocation, in bytes, per
    /// runner.
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
    /// The per-bind loading sublimits under the selected loading work
    /// allowance ([`Allowances::LOADING_WORK`]). The loaded pool passes to the
    /// runners, so its bytes stay within one runner's live and fresh
    /// allowances; the loading work is its own allowance, in its own unit.
    pub(crate) fn loading(&self, work: u64) -> LoadLimits {
        LoadLimits {
            bytes: self.values.live_bytes.min(self.values.total_bytes),
            // A selection that does not fit refuses at admission, never clamped.
            work: usize::try_from(work).unwrap_or(usize::MAX),
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
    #[test]
    fn every_host_allowance_names_its_unit_scope_default_and_maximum() {
        let allowances = [
            (Allowances::RING_WORK, Scope::Runner),
            (Allowances::SEQUENCE_WORK, Scope::Runner),
            (Allowances::EXTERNAL_WORK, Scope::Runner),
            (Allowances::SERVICE_DRAWS, Scope::Operation),
            (Allowances::INTERFACE_WORK, Scope::Operation),
            (Allowances::INTERFACE_DESCRIPTORS, Scope::Operation),
            (Allowances::FUNCTION_SERVICE_DRAWS, Scope::Invocation),
            (Allowances::JOURNAL_EVENTS, Scope::Invocation),
            (Allowances::DISPATCHES, Scope::Invocation),
            (Allowances::ATTEMPTS, Scope::Invocation),
            (Allowances::ATTEMPT_PROOF_BYTES, Scope::Attempt),
            (Allowances::INVOCATION_LIVE_BYTES, Scope::Invocation),
            (Allowances::INVOCATION_TOTAL_BYTES, Scope::Invocation),
            (Allowances::INVOCATION_LOGICAL_BYTES, Scope::Invocation),
            (Allowances::FUNCTION_INSTRUCTIONS, Scope::Invocation),
            (Allowances::FUNCTION_ITERATIONS, Scope::Invocation),
            (Allowances::LOADING_WORK, Scope::Operation),
            (Allowances::PUBLIC_BYTES, Scope::Operation),
            (Allowances::REFERENCE_BYTES, Scope::Invocation),
            (Allowances::SETUP_BYTES, Scope::Invocation),
            (Allowances::RETAINED_IMPORTS, Scope::Entry),
        ];
        for (allowance, scope) in allowances {
            assert!(!allowance.unit.is_empty());
            assert_eq!(allowance.scope, scope);
            assert!(allowance.default <= allowance.maximum);
            // The maximum is admitted and anything above it refused, never
            // reduced to it.
            assert!(allowance.admits(allowance.maximum));
            assert!(!allowance.admits(allowance.maximum + 1));
        }
        // Equal numbers stay separate allowances with their own scopes.
        assert_eq!(
            Allowances::SERVICE_DRAWS.default,
            Allowances::INTERFACE_WORK.default
        );
        assert_ne!(
            Allowances::SERVICE_DRAWS.scope,
            Allowances::FUNCTION_SERVICE_DRAWS.scope
        );
        // The root's allowances and a runner's agree in number by default, yet
        // each is its own allowance with its own scope and unit.
        let runner = Capacity::default();
        assert_eq!(
            Allowances::INVOCATION_LIVE_BYTES.default,
            runner.values.live_bytes as u64
        );
        assert_ne!(Allowances::INVOCATION_LIVE_BYTES.scope, Scope::Runner);
        assert_eq!(
            Allowances::INVOCATION_LOGICAL_BYTES.default,
            runner.work.logical_bytes
        );
        assert_ne!(
            Allowances::LOADING_WORK.unit,
            Allowances::INVOCATION_TOTAL_BYTES.unit
        );
        // The Function meters are the record's own selections, pooled.
        assert_eq!(
            Allowances::FUNCTION_INSTRUCTIONS.default,
            runner.work.instructions
        );
        assert_eq!(
            Allowances::FUNCTION_ITERATIONS.default,
            runner.work.iterations
        );
        // The supplied material's allowances agree in number with a runner's
        // byte allowances by default, yet none derives from them.
        assert_eq!(
            Allowances::PUBLIC_BYTES.default,
            runner.values.live_bytes as u64
        );
        assert_eq!(
            Allowances::REFERENCE_BYTES.default,
            runner.values.total_bytes as u64
        );
        for allowance in [
            Allowances::PUBLIC_BYTES,
            Allowances::REFERENCE_BYTES,
            Allowances::SETUP_BYTES,
            Allowances::RETAINED_IMPORTS,
        ] {
            assert_ne!(allowance.scope, Scope::Runner);
        }
    }
    #[test]
    fn material_allowances_refuse_above_their_maxima_with_their_own_codes() {
        assert_eq!(MaterialLimits::default(), MaterialLimits::DEFAULT);
        MaterialLimits::MAXIMUM.validate().unwrap();
        let maximum = MaterialLimits::MAXIMUM;
        for (limits, code) in [
            (
                MaterialLimits {
                    public_bytes: maximum.public_bytes + 1,
                    ..maximum
                },
                "entry-public-bytes-limit",
            ),
            (
                MaterialLimits {
                    reference_bytes: maximum.reference_bytes + 1,
                    ..maximum
                },
                "entry-reference-bytes-limit",
            ),
            (
                MaterialLimits {
                    setup_bytes: maximum.setup_bytes + 1,
                    ..maximum
                },
                "entry-setup-bytes-limit",
            ),
            (
                MaterialLimits {
                    retained_imports: maximum.retained_imports + 1,
                    ..maximum
                },
                "entry-retained-imports-limit",
            ),
        ] {
            assert_eq!(limits.validate().unwrap_err(), code);
        }
        // Lowering one allowance leaves the others and the runner's capacity
        // untouched.
        let lowered = MaterialLimits {
            setup_bytes: 1,
            ..MaterialLimits::DEFAULT
        };
        lowered.validate().unwrap();
        assert_eq!(lowered.public_bytes, MaterialLimits::DEFAULT.public_bytes);
    }
    #[test]
    fn root_refusals_name_the_allowance_that_refused() {
        let root = |live_bytes, total_bytes, logical_bytes| {
            InvocationLimits {
                live_bytes,
                total_bytes,
                logical_bytes,
            }
            .root()
        };
        for family in [
            RootCharge::LOADING,
            RootCharge::BINDING,
            RootCharge::RECEIVED_PROOF,
            RootCharge::ATTEMPT_PROOF,
            RootCharge::FUNCTION,
        ] {
            assert_ne!(family.work, family.bytes);
            // The logical work allowance refuses before any byte is charged.
            let ledger = root(64, 64, 7);
            assert_eq!(
                family.reserve_bytes(Some(&ledger), 8).err().unwrap(),
                family.work
            );
            assert_eq!(ledger.snapshot().total_value_bytes, 0);
            // The fresh byte allowance refuses after the work is committed.
            let ledger = root(64, 7, 64);
            assert_eq!(
                family.reserve_bytes(Some(&ledger), 8).err().unwrap(),
                family.bytes
            );
            assert_eq!(ledger.snapshot().logical_bytes, 8);
            // The live byte allowance refuses after both are committed.
            let ledger = root(7, 64, 64);
            assert_eq!(
                family.reserve_bytes(Some(&ledger), 8).err().unwrap(),
                family.bytes
            );
            assert_eq!(ledger.snapshot().total_value_bytes, 8);
            assert_eq!(family.hold(&ledger, 8).err().unwrap(), family.bytes);
            // An affordable reservation holds its bytes until dropped, and
            // no root charges nothing.
            let ledger = root(8, 8, 8);
            let held = family.reserve_bytes(Some(&ledger), 8).unwrap().unwrap();
            assert_eq!(ledger.snapshot().live_reserved_bytes, 8);
            drop(held);
            assert_eq!(ledger.snapshot().live_reserved_bytes, 0);
            assert!(family.reserve_bytes(None, usize::MAX).unwrap().is_none());
        }
    }
    #[test]
    fn invocation_allowances_refuse_above_their_maxima() {
        assert_eq!(InvocationLimits::default(), InvocationLimits::DEFAULT);
        InvocationLimits::MAXIMUM.validate().unwrap();
        for limits in [
            InvocationLimits {
                live_bytes: InvocationLimits::MAXIMUM.live_bytes + 1,
                ..InvocationLimits::DEFAULT
            },
            InvocationLimits {
                total_bytes: InvocationLimits::MAXIMUM.total_bytes + 1,
                ..InvocationLimits::DEFAULT
            },
            InvocationLimits {
                logical_bytes: InvocationLimits::MAXIMUM.logical_bytes + 1,
                ..InvocationLimits::DEFAULT
            },
        ] {
            assert_eq!(limits.validate().unwrap_err(), "native-invocation-limit");
        }
        // A root that no runner shares meters no instruction or iteration.
        let root = InvocationLimits::DEFAULT.root();
        for work in [
            WorkBudget {
                instructions: 1,
                iterations: 0,
                logical_bytes: 0,
            },
            WorkBudget {
                instructions: 0,
                iterations: 1,
                logical_bytes: 0,
            },
        ] {
            assert!(root.charge(work, 0).is_err());
        }
    }
    #[test]
    fn loading_work_is_its_own_allowance() {
        let mut capacity = Capacity::default();
        let default = capacity.loading(Allowances::LOADING_WORK.default);
        assert_eq!(default.work as u64, Allowances::LOADING_WORK.default);
        // Lowering the runners' fresh allocation leaves loading work alone.
        capacity.values.total_bytes = 1;
        let lowered = capacity.loading(Allowances::LOADING_WORK.default);
        assert_eq!(lowered.work, default.work);
        assert_eq!(lowered.bytes, 1);
        assert_eq!(capacity.loading(7).work, 7);
    }
    #[test]
    fn maxima_of_two_to_the_thirty_two_keep_their_value_on_thirty_two_bit_targets() {
        // 2^32 does not fit a 32-bit integer, so on wasm32 it does not fit a
        // pointer-sized one either.
        for maximum in [
            Limits::MAX_INSTRUCTIONS,
            Limits::MAX_ITERATIONS,
            Limits::LOGICAL_BYTES,
        ] {
            assert_eq!(maximum, 1 << 32);
            assert!(u32::try_from(maximum).is_err());
            // JSON readers, including JavaScript, read it exactly.
            assert!(maximum <= 1 << 53);
        }
        // Records, ledgers and reports carry them as 64-bit integers.
        let record = Capacity::HARD_MAX.record();
        assert_eq!(record[5], json!(["4294967296", "4294967296", "4294967296"]));
        let parsed = Capacity::parse(record.to_string().as_bytes()).unwrap();
        assert_eq!(parsed.work, Capacity::HARD_MAX.work);
        // A Function's root pools the record's instruction and iteration
        // selections beside the root's own logical-work maximum.
        let root =
            InvocationLimits::MAXIMUM.pooled(parsed.work.instructions, parsed.work.iterations);
        root.charge(parsed.work, 0).unwrap();
        let used = root.snapshot();
        assert_eq!(
            (used.instructions, used.iterations, used.logical_bytes),
            (1 << 32, 1 << 32, 1 << 32)
        );
        for work in [
            WorkBudget {
                instructions: 1,
                iterations: 0,
                logical_bytes: 0,
            },
            WorkBudget {
                instructions: 0,
                iterations: 1,
                logical_bytes: 0,
            },
            WorkBudget {
                instructions: 0,
                iterations: 0,
                logical_bytes: 1,
            },
        ] {
            assert!(root.charge(work, 0).is_err());
        }
        assert_eq!(root.snapshot(), used);
    }
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
