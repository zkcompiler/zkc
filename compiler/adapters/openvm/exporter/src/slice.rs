//! The selected upstream subsystem: the RV32 branch-equal execution slice.
//!
//! Five pinned upstream AIRs are instantiated at KoalaBear and their traces
//! are produced by the pinned upstream executor, trace fillers and chips:
//!
//! | Table | Upstream source (openvm `f08bf283`) | Role |
//! |---|---|---|
//! | `program` | `crates/vm/src/system/program/air.rs` `ProgramAir` | program-bus provider; cached program code |
//! | `connector` | `crates/vm/src/system/connector/mod.rs` `VmConnectorAir` | initial/final state, termination public values |
//! | `branch-equal` | `extensions/rv32im/circuit/src/{branch_eq/core.rs,adapters/branch.rs}` `Rv32BranchEqualAir` | BEQ/BNE executor with two register reads |
//! | `range-checker` | `crates/circuits/primitives/src/var_range/mod.rs` `VariableRangeCheckerAir` | range-bus provider |
//! | `memory-partner` | `crates/vm/src/arch/testing/memory/air.rs` `MemoryDummyAir` | memory-bus boundary stand-in |
//!
//! The memory partner replays the initial and final touched-memory messages
//! that OpenVM's persistent boundary chip would send; that chip, the Merkle
//! chip and the Poseidon2 periphery require `VmField`, which Plonky3 0.4.3
//! does not implement for KoalaBear, so they are outside this slice.
//! Execution follows `VirtualMachine::execute_preflight`: the connector
//! begins at the start pc with the tracing memory's first timestamp, every
//! executed pc counts once in the program frequencies including the
//! terminating instruction, and the final state is the pc of `TERMINATE`
//! with the timestamp left unchanged.

use crate::config::{KoalaBearRelationConfig, config};
use crate::field::F;
use crate::refusal::{Result, ensure, refuse};
use openvm_circuit::arch::testing::memory::air::{MemoryDummyAir, MemoryDummyChip};
use openvm_circuit::arch::testing::{
    EXECUTION_BUS, MEMORY_BUS, RANGE_CHECKER_BUS, READ_INSTRUCTION_BUS,
};
use openvm_circuit::arch::{
    Arena, ExecutionBridge, ExecutionBus, ExecutionState, MatrixRecordArena, MemoryConfig,
    PreflightExecutor, Streams, VmStateMut,
};
use openvm_circuit::system::connector::{VmConnectorAir, VmConnectorChip};
use openvm_circuit::system::memory::offline_checker::{MemoryBridge, MemoryBus};
use openvm_circuit::system::memory::online::{AddressMap, GuestMemory, TracingMemory};
use openvm_circuit::system::memory::{SharedMemoryHelper, TimestampedValues};
use openvm_circuit::system::program::{
    ProgramAir, ProgramBus, ProgramCachedCols, ProgramExecutionCols,
};
use openvm_circuit_primitives::Chip;
use openvm_circuit_primitives::var_range::{
    SharedVariableRangeCheckerChip, VariableRangeCheckerBus, VariableRangeCheckerChip,
};
use openvm_cpu_backend::CpuBackend;
use openvm_instructions::exe::SparseMemoryImage;
use openvm_instructions::instruction::Instruction;
use openvm_instructions::program::{DEFAULT_PC_STEP, MAX_ALLOWED_PC};
use openvm_instructions::riscv::RV32_REGISTER_AS;
use openvm_instructions::{LocalOpcode, SystemOpcode};
use openvm_rv32im_circuit::adapters::{
    Rv32BranchAdapterAir, Rv32BranchAdapterExecutor, Rv32BranchAdapterFiller,
};
use openvm_rv32im_circuit::{
    BranchEqualCoreAir, BranchEqualFiller, Rv32BranchEqualAir, Rv32BranchEqualChip,
    Rv32BranchEqualExecutor,
};
use openvm_rv32im_transpiler::BranchEqualOpcode;
use openvm_stark_backend::p3_air::BaseAir;
use openvm_stark_backend::p3_matrix::Matrix;
use openvm_stark_backend::p3_matrix::dense::RowMajorMatrix;
use openvm_stark_backend::{AirRef, PartitionedBaseAir};
use p3_field::{PrimeCharacteristicRing, PrimeField32};
use rand::SeedableRng;
use rand::rngs::StdRng;
use std::borrow::BorrowMut;
use std::sync::Arc;

pub type SC = KoalaBearRelationConfig;

pub const PROGRAM: usize = 0;
pub const CONNECTOR: usize = 1;
pub const BRANCH: usize = 2;
pub const RANGE: usize = 3;
pub const MEMORY: usize = 4;
pub const AIR_NAMES: [&str; 5] = [
    "program",
    "connector",
    "branch-equal",
    "range-checker",
    "memory-partner",
];
/// Upstream `SystemConfig::is_required_air_id` marks the program and
/// connector AIRs (and the memory boundary and Merkle AIRs outside this
/// slice) as required; every other AIR may be absent from a proof.
pub const REQUIRED: [bool; 5] = [true, true, false, false, false];

/// The register address space has 32 four-byte registers.
pub const REGISTER_CELLS: u32 = 128;
pub const BLOCK: usize = 4;

/// Parameters of the slice. The upstream defaults are `timestamp_max_bits 29`
/// and `decomp 17`; this slice keeps the two-limb timestamp decomposition
/// (`AUX_LEN = 2`) with smaller limbs so that the range table has
/// `2^(range_max_bits + 1)` rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Parameters {
    pub timestamp_max_bits: usize,
    pub range_max_bits: usize,
    pub pc_base: u32,
    pub step_limit: usize,
}

impl Default for Parameters {
    fn default() -> Self {
        Self {
            timestamp_max_bits: 16,
            range_max_bits: 8,
            pc_base: 0,
            step_limit: 64,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Branch {
    Beq,
    Bne,
}

impl Branch {
    fn opcode(self) -> BranchEqualOpcode {
        match self {
            Branch::Beq => BranchEqualOpcode::BEQ,
            Branch::Bne => BranchEqualOpcode::BNE,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Branch::Beq => "beq",
            Branch::Bne => "bne",
        }
    }
}

/// `op rs1, rs2, imm`: compare the four-byte registers at `rs1` and `rs2`
/// and add `imm` to the pc when the comparison holds, else advance by four.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Step {
    pub op: Branch,
    pub rs1: u32,
    pub rs2: u32,
    pub imm: i32,
}

/// Branch instructions at `pc_base, pc_base + 4, ...` followed by
/// `TERMINATE` with the exit code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    pub steps: Vec<Step>,
    pub exit_code: u32,
}

/// Initial register image: four-byte values at register pointers.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Registers(pub Vec<(u32, [u8; BLOCK])>);

impl Registers {
    fn initial(&self, pointer: u32) -> [u8; BLOCK] {
        self.0
            .iter()
            .find(|(p, _)| *p == pointer)
            .map_or([0; BLOCK], |(_, v)| *v)
    }
}

/// One AIR's traces as the prover supplies them: cached main matrices,
/// common main matrix and public values.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trace {
    pub cached_mains: Vec<RowMajorMatrix<F>>,
    pub common_main: RowMajorMatrix<F>,
    pub public_values: Vec<F>,
}

impl Trace {
    pub fn height(&self) -> usize {
        self.common_main.height()
    }
    /// Partitioned main parts in the symbolic builder's order: cached mains
    /// then the common main.
    pub fn parts(&self) -> Vec<&RowMajorMatrix<F>> {
        self.cached_mains
            .iter()
            .chain(std::iter::once(&self.common_main))
            .collect()
    }
}

/// Honest data of one execution: per AIR traces (`None` for an AIR with no
/// rows, which OpenVM omits from the proof) and the execution facts.
#[derive(Clone, Debug, PartialEq)]
pub struct Execution {
    pub program: Program,
    pub registers: Registers,
    pub traces: Vec<Option<Trace>>,
    pub from_state: ExecutionState<u32>,
    pub to_state: ExecutionState<u32>,
    pub exit_code: u32,
    pub frequencies: Vec<u32>,
    /// Touched register blocks: `(pointer, initial bytes, final bytes, final timestamp)`.
    pub touched: Vec<(u32, [u8; BLOCK], [u8; BLOCK], u32)>,
}

/// The instantiated AIRs and the configuration they share.
pub struct Slice {
    pub config: SC,
    pub parameters: Parameters,
    pub memory_config: MemoryConfig,
    airs: Vec<AirRef<SC>>,
    execution_bus: ExecutionBus,
    program_bus: ProgramBus,
    memory_bus: MemoryBus,
    range_bus: VariableRangeCheckerBus,
}

impl Slice {
    pub fn new(parameters: Parameters) -> Result<Self> {
        ensure(
            (1..=17).contains(&parameters.range_max_bits)
                && (1..=29).contains(&parameters.timestamp_max_bits)
                && parameters
                    .timestamp_max_bits
                    .div_ceil(parameters.range_max_bits)
                    == 2
                && (1..=65536).contains(&parameters.step_limit),
            "openvm-parameters",
            || {
                format!(
                    "timestamp_max_bits {} and range_max_bits {} must decompose into exactly two limbs",
                    parameters.timestamp_max_bits, parameters.range_max_bits
                )
            },
        )?;
        ensure(
            parameters.pc_base.is_multiple_of(DEFAULT_PC_STEP)
                && parameters.pc_base <= MAX_ALLOWED_PC,
            "openvm-parameters",
            || "pc_base must be a multiple of the pc step".into(),
        )?;
        let memory_config = MemoryConfig {
            timestamp_max_bits: parameters.timestamp_max_bits,
            decomp: parameters.range_max_bits,
            ..MemoryConfig::default()
        };
        let execution_bus = ExecutionBus::new(EXECUTION_BUS);
        let program_bus = ProgramBus::new(READ_INSTRUCTION_BUS);
        let memory_bus = MemoryBus::new(MEMORY_BUS);
        let range_bus = VariableRangeCheckerBus::new(RANGE_CHECKER_BUS, parameters.range_max_bits);
        let memory_bridge = MemoryBridge::new(memory_bus, parameters.timestamp_max_bits, range_bus);
        let execution_bridge = ExecutionBridge::new(execution_bus, program_bus);
        let branch_air = Rv32BranchEqualAir::new(
            Rv32BranchAdapterAir::new(execution_bridge, memory_bridge),
            BranchEqualCoreAir::new(BranchEqualOpcode::CLASS_OFFSET, DEFAULT_PC_STEP),
        );
        let airs: Vec<AirRef<SC>> = vec![
            Arc::new(ProgramAir::new(program_bus)),
            Arc::new(VmConnectorAir::new(
                execution_bus,
                program_bus,
                range_bus,
                parameters.timestamp_max_bits,
            )),
            Arc::new(branch_air),
            Arc::new(VariableRangeCheckerChip::new(range_bus).air),
            Arc::new(MemoryDummyAir::new(memory_bus)),
        ];
        Ok(Self {
            config: config(),
            parameters,
            memory_config,
            airs,
            execution_bus,
            program_bus,
            memory_bus,
            range_bus,
        })
    }

    pub fn airs(&self) -> &[AirRef<SC>] {
        &self.airs
    }

    /// Bus indices in table order of use: execution, memory, range, program.
    pub fn buses(&self) -> [(&'static str, u16); 4] {
        [
            ("execution", self.execution_bus.index()),
            ("memory", self.memory_bus.index()),
            ("range", self.range_bus.index()),
            ("program", self.program_bus.index()),
        ]
    }

    pub fn range_table_height(&self) -> usize {
        1 << (self.parameters.range_max_bits + 1)
    }

    /// Program rows in pc order: the branch steps then `TERMINATE`.
    pub fn instructions(&self, program: &Program) -> Vec<Instruction<F>> {
        program
            .steps
            .iter()
            .map(|s| {
                Instruction::from_isize(
                    s.op.opcode().global_opcode(),
                    s.rs1 as isize,
                    s.rs2 as isize,
                    s.imm as isize,
                    RV32_REGISTER_AS as isize,
                    RV32_REGISTER_AS as isize,
                )
            })
            .chain(std::iter::once(Instruction::from_usize(
                SystemOpcode::TERMINATE.global_opcode(),
                [0, 0, program.exit_code as usize],
            )))
            .collect()
    }

    /// Run the pinned upstream executor over the program and lay out every
    /// table with the pinned upstream chips.
    pub fn execute(&self, program: &Program, registers: &Registers) -> Result<Execution> {
        let p = self.parameters;
        ensure(
            program.steps.len() <= 65536
                && u64::from(p.pc_base) + program.steps.len() as u64 * u64::from(DEFAULT_PC_STEP)
                    <= u64::from(MAX_ALLOWED_PC),
            "openvm-program-limit",
            || "program or terminating pc exceeds the selected profile".into(),
        )?;
        for step in &program.steps {
            for pointer in [step.rs1, step.rs2] {
                ensure(
                    pointer <= REGISTER_CELLS - BLOCK as u32 && pointer % BLOCK as u32 == 0,
                    "openvm-register",
                    || format!("register pointer {pointer}"),
                )?;
            }
        }
        for (pointer, _) in &registers.0 {
            ensure(
                *pointer <= REGISTER_CELLS - BLOCK as u32 && pointer % BLOCK as u32 == 0,
                "openvm-register",
                || format!("register pointer {pointer}"),
            )?;
        }
        ensure(
            registers
                .0
                .iter()
                .map(|(p, _)| p)
                .collect::<std::collections::BTreeSet<_>>()
                .len()
                == registers.0.len(),
            "openvm-register",
            || "duplicate initial register".into(),
        )?;
        ensure(program.exit_code < F::ORDER_U32, "openvm-exit-code", || {
            "exit code is not a field element".into()
        })?;
        let instructions = self.instructions(program);

        // Initial memory image: an outer obligation in OpenVM (its Merkle
        // root is part of the executable commitment).
        let mut sparse = SparseMemoryImage::new();
        for (pointer, bytes) in &registers.0 {
            for (i, byte) in bytes.iter().enumerate() {
                sparse.insert((RV32_REGISTER_AS, pointer + i as u32), *byte);
            }
        }
        let mut map = AddressMap::from_mem_config(&self.memory_config);
        map.set_from_sparse(&sparse);
        let mut memory = TracingMemory::from_image(GuestMemory::new(map));
        let range_checker: SharedVariableRangeCheckerChip =
            Arc::new(VariableRangeCheckerChip::new(self.range_bus));

        let executor = Rv32BranchEqualExecutor::new(
            Rv32BranchAdapterExecutor,
            BranchEqualOpcode::CLASS_OFFSET,
            DEFAULT_PC_STEP,
        );
        let branch_width = BaseAir::<F>::width(self.airs[BRANCH].as_ref());
        let mut arena = MatrixRecordArena::<F>::with_capacity(p.step_limit, branch_width);
        let mut streams = Streams::<F>::default();
        let mut rng = StdRng::seed_from_u64(0);
        let mut pc = p.pc_base;
        let from_state = ExecutionState::new(pc, memory.timestamp());
        let mut frequencies = vec![0u32; instructions.len()];
        let mut executed = 0usize;
        let terminate = SystemOpcode::TERMINATE.global_opcode().as_usize();
        let exit_code = loop {
            let index = pc
                .checked_sub(p.pc_base)
                .filter(|offset| offset % DEFAULT_PC_STEP == 0)
                .map(|offset| (offset / DEFAULT_PC_STEP) as usize)
                .filter(|i| *i < instructions.len());
            let Some(index) = index else {
                return refuse("openvm-pc-out-of-program", format!("pc {pc}"));
            };
            frequencies[index] += 1;
            let instruction = &instructions[index];
            if instruction.opcode.as_usize() == terminate {
                break instruction.c.as_canonical_u32();
            }
            ensure(executed < p.step_limit, "openvm-step-limit", || {
                format!("more than {} executed branches", p.step_limit)
            })?;
            let state = VmStateMut {
                pc: &mut pc,
                memory: &mut memory,
                streams: &mut streams,
                rng: &mut rng,
                ctx: &mut arena,
            };
            executor
                .execute(state, instruction)
                .map_err(|e| crate::refusal::Refusal {
                    id: "openvm-execution",
                    detail: e.to_string(),
                })?;
            executed += 1;
        };
        ensure(
            memory.timestamp() < (1u32 << p.timestamp_max_bits),
            "openvm-timestamp-limit",
            || "execution exceeds the configured timestamp range".into(),
        )?;
        let to_state = ExecutionState::new(pc, memory.timestamp());

        // Branch rows: the chip wrapper fills the records the executor left
        // in the arena, requesting range checks for the timestamp aux columns.
        let rows_used = arena.trace_offset / arena.width;
        let branch = (rows_used > 0).then(|| {
            let chip = Rv32BranchEqualChip::<F>::new(
                BranchEqualFiller::new(
                    Rv32BranchAdapterFiller,
                    BranchEqualOpcode::CLASS_OFFSET,
                    DEFAULT_PC_STEP,
                ),
                SharedMemoryHelper::new(range_checker.clone(), p.timestamp_max_bits),
            );
            let ctx =
                Chip::<MatrixRecordArena<F>, CpuBackend<SC>>::generate_proving_ctx(&chip, arena);
            Trace {
                cached_mains: vec![],
                common_main: ctx.common_main,
                public_values: ctx.public_values,
            }
        });

        // Connector: both boundary states, with range checks of the timestamps.
        let mut connector = VmConnectorChip::<F>::new(range_checker.clone(), p.timestamp_max_bits);
        connector.begin(from_state);
        connector.end(to_state, Some(exit_code));
        let ctx = Chip::<(), CpuBackend<SC>>::generate_proving_ctx(&connector, ());
        let connector_trace = Trace {
            cached_mains: vec![],
            common_main: ctx.common_main,
            public_values: ctx.public_values,
        };

        // Program: cached code rows (laid out as upstream
        // `program/trace.rs::generate_cached_trace`, which is crate-private)
        // and the execution frequency column.
        let program_trace = self.program_trace(&instructions, &frequencies);

        // Memory partner: initial and final messages of every touched block.
        let mut touched = Vec::new();
        let mut partner = MemoryDummyChip::<F>::new(MemoryDummyAir::new(self.memory_bus));
        for ((address_space, pointer), TimestampedValues { timestamp, values }) in
            memory.finalize::<F>()
        {
            ensure(
                address_space == RV32_REGISTER_AS,
                "openvm-address-space",
                || format!("touched address space {address_space}"),
            )?;
            let initial = registers.initial(pointer);
            let final_bytes: [u8; BLOCK] =
                std::array::from_fn(|i| values[i].as_canonical_u32() as u8);
            partner.send(address_space, pointer, &initial.map(F::from_u8), 0);
            partner.receive(address_space, pointer, &values, timestamp);
            touched.push((pointer, initial, final_bytes, timestamp));
        }
        let partner_trace = (!touched.is_empty()).then(|| {
            let ctx = Chip::<(), CpuBackend<SC>>::generate_proving_ctx(&partner, ());
            Trace {
                cached_mains: vec![],
                common_main: ctx.common_main,
                public_values: ctx.public_values,
            }
        });

        // Range checker last: its trace consumes the accumulated counts.
        let ctx = Chip::<(), CpuBackend<SC>>::generate_proving_ctx(range_checker.as_ref(), ());
        let range_trace = Trace {
            cached_mains: vec![],
            common_main: ctx.common_main,
            public_values: ctx.public_values,
        };

        Ok(Execution {
            program: program.clone(),
            registers: registers.clone(),
            traces: vec![
                Some(program_trace),
                Some(connector_trace),
                branch,
                Some(range_trace),
                partner_trace,
            ],
            from_state,
            to_state,
            exit_code,
            frequencies,
            touched,
        })
    }

    fn program_trace(&self, instructions: &[Instruction<F>], frequencies: &[u32]) -> Trace {
        let width = ProgramCachedCols::<F>::width();
        let mut rows: Vec<(u32, Instruction<F>)> = instructions
            .iter()
            .enumerate()
            .map(|(i, instruction)| {
                (
                    self.parameters.pc_base + i as u32 * DEFAULT_PC_STEP,
                    instruction.clone(),
                )
            })
            .collect();
        // Upstream pads with `TERMINATE` and exit code `EXIT_CODE_FAIL = 1`.
        let padding = Instruction::from_usize(SystemOpcode::TERMINATE.global_opcode(), [0, 0, 1]);
        while !rows.len().is_power_of_two() {
            rows.push((
                self.parameters.pc_base + rows.len() as u32 * DEFAULT_PC_STEP,
                padding.clone(),
            ));
        }
        let height = rows.len();
        let mut values = F::zero_vec(height * width);
        for (idx, (row, (pc, instruction))) in values.chunks_exact_mut(width).zip(&rows).enumerate()
        {
            let cols: &mut ProgramCachedCols<F> = row.borrow_mut();
            cols.exec_end = F::ONE + F::from_bool(idx == height - 1);
            cols.exec_start = F::from_bool(idx == 0);
            cols.exec = ProgramExecutionCols {
                pc: F::from_u32(*pc),
                opcode: instruction.opcode.to_field(),
                a: instruction.a,
                b: instruction.b,
                c: instruction.c,
                d: instruction.d,
                e: instruction.e,
                f: instruction.f,
                g: instruction.g,
            };
        }
        let mut freqs = F::zero_vec(height);
        for (f, x) in freqs.iter_mut().zip(frequencies) {
            *f = F::from_u32(*x);
        }
        Trace {
            cached_mains: vec![RowMajorMatrix::new(values, width)],
            common_main: RowMajorMatrix::new(freqs, 1),
            public_values: vec![],
        }
    }
}

/// Column names of one AIR when its upstream `ColumnsAir` reflection knows
/// them, in partitioned order; `None` otherwise.
pub fn column_names(slice: &Slice, air: usize) -> Option<Vec<String>> {
    use openvm_circuit_primitives::ColumnsAir;
    match air {
        PROGRAM => ProgramAir::new(slice.program_bus).columns(),
        CONNECTOR => VmConnectorAir::new(
            slice.execution_bus,
            slice.program_bus,
            slice.range_bus,
            slice.parameters.timestamp_max_bits,
        )
        .columns(),
        BRANCH => Rv32BranchEqualAir::new(
            Rv32BranchAdapterAir::new(
                ExecutionBridge::new(slice.execution_bus, slice.program_bus),
                MemoryBridge::new(
                    slice.memory_bus,
                    slice.parameters.timestamp_max_bits,
                    slice.range_bus,
                ),
            ),
            BranchEqualCoreAir::new(BranchEqualOpcode::CLASS_OFFSET, DEFAULT_PC_STEP),
        )
        .columns(),
        RANGE => VariableRangeCheckerChip::new(slice.range_bus).air.columns(),
        MEMORY => MemoryDummyAir::new(slice.memory_bus).columns(),
        _ => None,
    }
}

/// Widths the symbolic builder and verifying key use for an AIR.
pub fn trace_width(air: &AirRef<SC>) -> openvm_stark_backend::keygen::types::TraceWidth {
    openvm_stark_backend::keygen::types::TraceWidth {
        preprocessed: None,
        cached_mains: PartitionedBaseAir::<F>::cached_main_widths(air.as_ref()),
        common_main: PartitionedBaseAir::<F>::common_main_width(air.as_ref()),
    }
}
