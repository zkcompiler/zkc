//! The exported view: what each arena input means, the table layout and the
//! checks that both the exporter and the importer apply to it.

use crate::arena::{Arena, Node};
use crate::field::{F, MAX_LOG_HEIGHT, log_height};
use crate::refusal::{Result, ensure, refuse};
use std::collections::HashSet;

pub const MAX_WIDTH: usize = 4_096;
pub const MAX_PUBLIC_VALUES: usize = 4_096;
pub const MAX_PREPROCESSED_CELLS: usize = 1 << 22;
pub const MAX_NAME_BYTES: usize = 256;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SelectorKind {
    FirstRow,
    LastRow,
    Transition,
}

impl SelectorKind {
    pub const ALL: [SelectorKind; 3] = [Self::FirstRow, Self::LastRow, Self::Transition];
    pub fn name(self) -> &'static str {
        match self {
            Self::FirstRow => "first-row",
            Self::LastRow => "last-row",
            Self::Transition => "transition",
        }
    }
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|k| k.name() == name)
    }
}

/// Binding of one arena input. Reads are cyclic: offset one on the last row
/// reads row zero. The derived `Ord` is the canonical slot order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Slot {
    Main { offset: usize, column: usize },
    Preprocessed { offset: usize, column: usize },
    Public(usize),
    Selector(SelectorKind),
}

/// How an arena node arose from the upstream expression. Upstream `Sub(x, y)`
/// is `add(x, neg(y))` with origins `Sub` and `SubNegation`, so the upstream
/// tree is recoverable exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Origin {
    Leaf,
    Add,
    Sub,
    SubNegation,
    Neg,
    Mul,
}

impl Origin {
    pub const ALL: [Origin; 6] = [
        Self::Leaf,
        Self::Add,
        Self::Sub,
        Self::SubNegation,
        Self::Neg,
        Self::Mul,
    ];
    pub fn name(self) -> &'static str {
        match self {
            Self::Leaf => "leaf",
            Self::Add => "add",
            Self::Sub => "sub",
            Self::SubNegation => "sub-negation",
            Self::Neg => "neg",
            Self::Mul => "mul",
        }
    }
    pub fn parse(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|o| o.name() == name)
    }
}

/// Fixed columns produced by the AIR's `preprocessed_trace`. They are
/// configuration bound by the export identity, not prover input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Preprocessed {
    pub width: usize,
    pub height: usize,
    pub next_row_columns: Vec<usize>,
    /// Row-major values.
    pub values: Vec<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub main_width: usize,
    pub main_next_row_columns: Vec<usize>,
    pub preprocessed: Option<Preprocessed>,
    pub public_values: usize,
}

/// One upstream `assert_zero`, in emission order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Assertion {
    /// Index of the upstream constraint; `DebugConstraintBuilder` reports it.
    pub constraint: usize,
    /// Upstream `degree_multiple`, recomputed from the arena.
    pub degree_multiple: u64,
    /// Selectors occurring in guard position.
    pub selectors: Vec<SelectorKind>,
}

/// Unsupported upstream surfaces the capture probes for and refuses.
pub const PROBED_ABSENT: [&str; 5] = [
    "extension-constraint",
    "periodic-column",
    "permutation-challenge",
    "permutation-column",
    "permutation-value",
];

/// A candidate relation exported from one AIR. It carries no authority until a
/// verifier configuration selects its identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Export {
    pub air: String,
    pub layout: Layout,
    pub arena: Arena,
    pub slots: Vec<Slot>,
    pub origins: Vec<Origin>,
    pub assertions: Vec<Assertion>,
    pub features: Vec<String>,
}

/// Upstream `degree_multiple` weights: trace reads and first/last selectors
/// count one, publics and the transition selector zero.
pub fn degree_multiple_weight(slot: &Slot) -> u64 {
    match slot {
        Slot::Main { .. } | Slot::Preprocessed { .. } => 1,
        Slot::Selector(SelectorKind::FirstRow | SelectorKind::LastRow) => 1,
        Slot::Public(_) | Slot::Selector(SelectorKind::Transition) => 0,
    }
}

/// Degree weights of the two-adic polynomial view for height `n`: trace
/// interpolants and the first/last Lagrange selectors have degree `n - 1`,
/// the transition selector `x - g^-1` degree one, publics degree zero.
pub fn polynomial_weight(slot: &Slot, height: usize) -> u64 {
    match slot {
        Slot::Main { .. } | Slot::Preprocessed { .. } => height as u64 - 1,
        Slot::Selector(SelectorKind::FirstRow | SelectorKind::LastRow) => height as u64 - 1,
        Slot::Selector(SelectorKind::Transition) => 1,
        Slot::Public(_) => 0,
    }
}

/// Selector paths to every assertion root must pass only through `mul` and
/// `neg`. Then each residual is plus or minus a product of selector powers and
/// a selector-free factor, and the row and point selector laws have the same
/// zero locus on the trace domain. A selector below `add` (including the `add`
/// of an upstream `sub`) is refused before any interpretation.
/// Returns the selector kinds of each output.
pub fn check_guards(arena: &Arena, slots: &[Slot]) -> Result<Vec<Vec<SelectorKind>>> {
    let selector = |node: &Node| match node {
        Node::Input(s) => match slots[*s] {
            Slot::Selector(kind) => Some(kind),
            _ => None,
        },
        _ => None,
    };
    let mut seen: HashSet<(usize, bool)> = HashSet::new();
    for (position, root) in arena.outputs().iter().enumerate() {
        let mut stack = vec![(*root, true)];
        while let Some((node, guarded)) = stack.pop() {
            if !seen.insert((node, guarded)) {
                continue;
            }
            let n = &arena.nodes()[node];
            if let Some(kind) = selector(n) {
                ensure(guarded, "plonky3-selector-not-guard", || {
                    format!(
                        "assertion {position} uses the {} selector below an addition",
                        kind.name()
                    )
                })?;
            }
            let child_guarded = guarded && !matches!(n, Node::Add(..));
            for child in n.children() {
                stack.push((child, child_guarded));
            }
        }
    }
    let mut masks: Vec<u8> = Vec::with_capacity(arena.nodes().len());
    for n in arena.nodes() {
        let mut mask = selector(n).map_or(0, |k| 1u8 << (k as u8));
        for child in n.children() {
            mask |= masks[child];
        }
        masks.push(mask);
    }
    Ok(arena
        .outputs()
        .iter()
        .map(|root| {
            SelectorKind::ALL
                .into_iter()
                .filter(|k| masks[*root] & (1 << (*k as u8)) != 0)
                .collect()
        })
        .collect())
}

/// Inventory of upstream features the export represents, sorted.
pub fn features(arena: &Arena, slots: &[Slot], origins: &[Origin]) -> Vec<String> {
    let mut names: Vec<&str> = Vec::new();
    for slot in slots {
        names.push(match slot {
            Slot::Main { offset: 0, .. } => "main-current",
            Slot::Main { .. } => "main-next",
            Slot::Preprocessed { offset: 0, .. } => "preprocessed-current",
            Slot::Preprocessed { .. } => "preprocessed-next",
            Slot::Public(_) => "public-value",
            Slot::Selector(SelectorKind::FirstRow) => "selector-first-row",
            Slot::Selector(SelectorKind::LastRow) => "selector-last-row",
            Slot::Selector(SelectorKind::Transition) => "selector-transition",
        });
    }
    if arena.nodes().iter().any(|n| matches!(n, Node::Constant(_))) {
        names.push("constant");
    }
    for origin in origins {
        match origin {
            Origin::Add => names.push("add"),
            Origin::Sub => names.push("sub"),
            Origin::Neg => names.push("neg"),
            Origin::Mul => names.push("mul"),
            Origin::Leaf | Origin::SubNegation => {}
        }
    }
    names.sort_unstable();
    names.dedup();
    names.into_iter().map(String::from).collect()
}

fn check_columns(columns: &[usize], width: usize, what: &str) -> Result<()> {
    ensure(
        columns.windows(2).all(|w| w[0] < w[1]) && columns.iter().all(|c| *c < width),
        "plonky3-next-row-metadata",
        || {
            format!(
                "{what} next-row columns {columns:?} are not distinct columns below width {width}"
            )
        },
    )
}

impl Layout {
    pub fn check(&self) -> Result<()> {
        ensure(
            (1..=MAX_WIDTH).contains(&self.main_width),
            "plonky3-layout",
            || format!("main width {} is outside 1..={MAX_WIDTH}", self.main_width),
        )?;
        ensure(
            self.public_values <= MAX_PUBLIC_VALUES,
            "plonky3-layout",
            || format!("{} public values", self.public_values),
        )?;
        check_columns(&self.main_next_row_columns, self.main_width, "main")?;
        if let Some(p) = &self.preprocessed {
            ensure(
                (1..=MAX_WIDTH).contains(&p.width),
                "plonky3-preprocessed-shape",
                || format!("preprocessed width {}", p.width),
            )?;
            ensure(
                p.height.is_power_of_two() && p.height.trailing_zeros() as usize <= MAX_LOG_HEIGHT,
                "plonky3-preprocessed-shape",
                || format!("preprocessed height {}", p.height),
            )?;
            ensure(
                p.width
                    .checked_mul(p.height)
                    .is_some_and(|c| c <= MAX_PREPROCESSED_CELLS && c == p.values.len()),
                "plonky3-preprocessed-shape",
                || "preprocessed cell count".into(),
            )?;
            check_columns(&p.next_row_columns, p.width, "preprocessed")?;
        }
        Ok(())
    }

    /// The trace height this layout admits: fixed by the preprocessed table if
    /// there is one, otherwise any admitted power of two.
    pub fn admits_height(&self, height: usize) -> Result<usize> {
        let log = log_height(height)?;
        if let Some(p) = &self.preprocessed {
            ensure(p.height == height, "plonky3-height", || {
                format!(
                    "trace height {height} differs from preprocessed height {}",
                    p.height
                )
            })?;
        }
        Ok(log)
    }
}

impl Export {
    /// Every structural fact of the view, recomputed from its own content.
    pub fn validate(&self) -> Result<()> {
        ensure(
            !self.air.is_empty()
                && self.air.len() <= MAX_NAME_BYTES
                && self.air.bytes().all(|b| b.is_ascii_graphic()),
            "plonky3-export-schema",
            || "AIR name".into(),
        )?;
        self.layout.check()?;
        ensure(
            self.slots.len() == self.arena.inputs(),
            "plonky3-slot",
            || "slot count differs from arena inputs".into(),
        )?;
        ensure(
            self.slots.windows(2).all(|w| w[0] < w[1]),
            "plonky3-slot",
            || "slots are not in canonical order".into(),
        )?;
        let mut used = vec![false; self.slots.len()];
        for node in self.arena.nodes() {
            if let Node::Input(s) = node {
                used[*s] = true;
            }
        }
        ensure(used.iter().all(|u| *u), "plonky3-slot", || {
            "an exported slot is unused".into()
        })?;
        for slot in &self.slots {
            match *slot {
                Slot::Main { offset, column } => {
                    ensure(
                        offset <= 1 && column < self.layout.main_width,
                        "plonky3-slot",
                        || format!("{slot:?}"),
                    )?;
                    ensure(
                        offset == 0
                            || self
                                .layout
                                .main_next_row_columns
                                .binary_search(&column)
                                .is_ok(),
                        "plonky3-next-row-metadata",
                        || format!("main column {column} is read on the next row but not declared"),
                    )?;
                }
                Slot::Preprocessed { offset, column } => {
                    let Some(p) = &self.layout.preprocessed else {
                        return refuse(
                            "plonky3-slot",
                            "preprocessed read without a preprocessed table",
                        );
                    };
                    ensure(offset <= 1 && column < p.width, "plonky3-slot", || {
                        format!("{slot:?}")
                    })?;
                    ensure(
                        offset == 0 || p.next_row_columns.binary_search(&column).is_ok(),
                        "plonky3-next-row-metadata",
                        || {
                            format!(
                                "preprocessed column {column} is read on the next row but not declared"
                            )
                        },
                    )?;
                }
                Slot::Public(i) => ensure(i < self.layout.public_values, "plonky3-slot", || {
                    format!("public {i}")
                })?,
                Slot::Selector(_) => {}
            }
        }
        ensure(
            self.origins.len() == self.arena.nodes().len(),
            "plonky3-node-map",
            || "origin count".into(),
        )?;
        let mut negation_users = vec![false; self.origins.len()];
        for (i, (node, origin)) in self.arena.nodes().iter().zip(&self.origins).enumerate() {
            let consistent = match (node, origin) {
                (Node::Constant(_) | Node::Input(_), Origin::Leaf) => true,
                (Node::Add(_, b), Origin::Sub) => {
                    negation_users[*b] = true;
                    self.origins[*b] == Origin::SubNegation
                }
                (Node::Add(..), Origin::Add) | (Node::Mul(..), Origin::Mul) => true,
                (Node::Neg(_), Origin::Neg | Origin::SubNegation) => true,
                _ => false,
            };
            ensure(consistent, "plonky3-node-map", || {
                format!("node {i} has origin {}", origin.name())
            })?;
        }
        for (i, node) in self.arena.nodes().iter().enumerate() {
            for (j, child) in node.children().enumerate() {
                let sub_right = j == 1 && self.origins[i] == Origin::Sub;
                ensure(
                    self.origins[child] != Origin::SubNegation || sub_right,
                    "plonky3-node-map",
                    || format!("node {child} is a subtraction negation outside a subtraction"),
                )?;
            }
        }
        ensure(
            self.origins
                .iter()
                .zip(&negation_users)
                .all(|(o, u)| *o != Origin::SubNegation || *u),
            "plonky3-node-map",
            || "unused subtraction negation".into(),
        )?;
        ensure(
            self.assertions.len() == self.arena.outputs().len(),
            "plonky3-assertion",
            || "assertion count differs from arena outputs".into(),
        )?;
        let weights: Vec<u64> = self.slots.iter().map(degree_multiple_weight).collect();
        let degrees = self.arena.degrees(&weights)?;
        let selectors = check_guards(&self.arena, &self.slots)?;
        for (position, assertion) in self.assertions.iter().enumerate() {
            let root = self.arena.outputs()[position];
            ensure(
                assertion.constraint == position,
                "plonky3-assertion",
                || {
                    format!(
                        "assertion {position} names constraint {}",
                        assertion.constraint
                    )
                },
            )?;
            ensure(
                assertion.degree_multiple == degrees[root],
                "plonky3-assertion",
                || format!("assertion {position} degree multiple"),
            )?;
            ensure(
                assertion.selectors == selectors[position],
                "plonky3-assertion",
                || format!("assertion {position} selectors"),
            )?;
        }
        ensure(
            self.features == features(&self.arena, &self.slots, &self.origins),
            "plonky3-feature-inventory",
            || "declared features differ from the exported content".into(),
        )?;
        Ok(())
    }

    /// Exact upper bound on each assertion's polynomial degree at height `n`.
    pub fn polynomial_degrees(&self, height: usize) -> Result<Vec<u64>> {
        let weights: Vec<u64> = self
            .slots
            .iter()
            .map(|s| polynomial_weight(s, height))
            .collect();
        let degrees = self.arena.degrees(&weights)?;
        Ok(self.arena.outputs().iter().map(|o| degrees[*o]).collect())
    }
}
