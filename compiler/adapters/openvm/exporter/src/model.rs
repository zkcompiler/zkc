//! The export model: what the adapter captured from the pinned upstream and
//! how it lowers to relation-bundle carriers.

use crate::arena::Arena;
use crate::slice::Parameters;

/// Scopes of lowered assertions, as the bundle states them.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Scope {
    All,
    First,
    Last,
    /// Rows `[0, h-1)`: `interior(0, 1)`.
    Transition,
    /// Rows `[1, h-1)`: `interior(1, 1)`.
    Interior,
    /// Rows `[1, h)`: `interior(1, 0)`.
    Tail,
}

impl Scope {
    pub fn contains(self, row: usize, height: usize) -> bool {
        match self {
            Scope::All => true,
            Scope::First => row == 0,
            Scope::Last => row + 1 == height,
            Scope::Transition => row + 1 < height,
            Scope::Interior => row >= 1 && row + 1 < height,
            Scope::Tail => row >= 1,
        }
    }
    pub fn name(self) -> &'static str {
        match self {
            Scope::All => "all",
            Scope::First => "first",
            Scope::Last => "last",
            Scope::Transition => "transition",
            Scope::Interior => "interior",
            Scope::Tail => "tail",
        }
    }
}

/// The three row classes of the row-indicator selector law at height at
/// least two: `(is_first_row, is_last_row, is_transition)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowClass {
    First,
    Interior,
    Last,
}

impl RowClass {
    pub const ALL: [RowClass; 3] = [RowClass::First, RowClass::Interior, RowClass::Last];
    pub fn selectors(self) -> (bool, bool, bool) {
        match self {
            RowClass::First => (true, false, true),
            RowClass::Interior => (false, false, true),
            RowClass::Last => (false, true, false),
        }
    }
}

/// A verifying-key DAG node with canonical constants.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DagNode {
    Variable {
        kind: VariableKind,
        part: usize,
        offset: usize,
        index: usize,
    },
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(u32),
    Add(usize, usize, usize),
    Sub(usize, usize, usize),
    Neg(usize, usize),
    Mul(usize, usize, usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VariableKind {
    Main,
    Preprocessed,
    Public,
    Challenge,
}

impl VariableKind {
    pub fn name(self) -> &'static str {
        match self {
            VariableKind::Main => "main",
            VariableKind::Preprocessed => "preprocessed",
            VariableKind::Public => "public",
            VariableKind::Challenge => "challenge",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DagInteraction {
    pub bus: u16,
    pub message: Vec<usize>,
    pub count: usize,
    pub count_weight: u32,
}

/// The verifying key's `SymbolicConstraintsDag` for one AIR.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dag {
    pub nodes: Vec<DagNode>,
    pub constraint_idx: Vec<usize>,
    pub interactions: Vec<DagInteraction>,
}

/// Bundle input binding of one arena slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Input {
    Read {
        group: usize,
        offset: usize,
        column: usize,
    },
    Public(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assertion {
    /// Recorder constraint index (upstream emission order).
    pub constraint: usize,
    pub scope: Scope,
    pub output: usize,
    pub degree: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interaction {
    /// Index into `Export::buses`.
    pub bus: usize,
    pub message: Vec<usize>,
    pub count: usize,
    pub count_weight: u32,
    pub degree: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Height {
    Fixed(usize),
    /// Fixed by the configuration data (a cached main).
    Config,
    /// Chosen by the instance: a power of two in `[2, 2^20]`.
    Instance,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Group {
    pub name: String,
    pub authority: &'static str,
    pub width: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AirExport {
    pub name: String,
    pub upstream_type: String,
    pub required: bool,
    pub groups: Vec<Group>,
    pub num_public_values: usize,
    pub column_names: Option<Vec<String>>,
    pub need_rot: bool,
    pub max_constraint_degree: u8,
    pub unused_variables: Vec<(VariableKind, usize, usize, usize)>,
    pub dag: Dag,
    /// DAG node of each recorder constraint, in emission order.
    pub recorder_constraints: Vec<usize>,
    pub recorder_degrees: Vec<usize>,
    pub inputs: Vec<Input>,
    pub arena: Arena,
    pub assertions: Vec<Assertion>,
    /// Recorder constraints identically zero on a row class.
    pub vacuous: Vec<(usize, RowClass)>,
    pub interactions: Vec<Interaction>,
    pub height: Height,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Bus {
    pub name: String,
    pub index: u16,
    pub arity: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearConstraint {
    pub coefficients: Vec<u32>,
    pub threshold: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Export {
    pub parameters: Parameters,
    pub buses: Vec<Bus>,
    /// `(name, air, public index)` of every bundle public slot.
    pub publics: Vec<(String, usize, usize)>,
    pub airs: Vec<AirExport>,
    pub trace_height_constraints: Vec<LinearConstraint>,
    pub vk_pre_hash: Vec<u32>,
    pub l_skip: usize,
    pub max_constraint_degree: usize,
    pub max_interaction_count: u32,
    pub log_max_message_length: u32,
}
