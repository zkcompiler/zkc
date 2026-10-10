//! A polynomial view of one present table on the multiplicative subgroup whose
//! order is the table's own height. The immutable Bundle owns the bindings and
//! degree facts; this view derives the descriptors a consuming library needs
//! and prepares the ordered assertion arena for substitution. It selects no
//! quotient combination, challenge, commitment or proof, and claims nothing
//! about interactions.
use super::*;

/// Bound on `quotient_chunks * height`, the coefficients a consumer of the
/// quotient degree bound would allocate.
pub const POLYNOMIAL_SIZE_LIMIT: u64 = 1 << 24;

/// Widths count field elements per row. Each authority's combined matrix is
/// row-major over the sum of its group widths, in group declaration order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolynomialShape {
    pub witness_width: u64,
    pub config_width: u64,
    pub public_width: u64,
    pub public_slots: u64,
    pub inputs: u64,
    pub assertions: u64,
    pub quotient_chunks: u64,
}
/// `kind` is 0 for a bundle public slot (`column` is the slot), or 1, 2, 3 for
/// a witness, configuration or public-group read. A read's `column` is its
/// column in that authority's combined matrix and `rotation` is its signed
/// offset reduced modulo the height.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PolynomialInput {
    pub kind: u64,
    pub column: u64,
    pub rotation: u64,
}

/// A table field substituted in the carrier: the carrier itself, or KoalaBear
/// in its installed degree-eight extension.
pub(super) fn lifts(field: Identity, carrier: Identity) -> bool {
    field == carrier || (carrier == Identity::KoalaBearExt8 && field == Identity::KoalaBear)
}
pub(super) fn kind(authority: Authority) -> u64 {
    match authority {
        Authority::Witness => 1,
        Authority::Config => 2,
        Authority::Public => 3,
    }
}

/// Borrowing the admitted Bundle prevents a view from being used with a
/// different definition. The view owns nothing: descriptors are derived on
/// demand, and only `prepare` allocates.
#[derive(Clone, Copy, Debug)]
pub struct PolynomialView<'a> {
    bundle: &'a Bundle,
    table: usize,
    field: Identity,
}
/// The sub-DAG of selected outputs of one table, prepared for substitution:
/// the assertions of a polynomial view or the records of an interaction view.
/// It keeps the table's input numbering.
#[derive(Clone, Debug)]
pub struct PolynomialArena {
    pub(super) arena: Expression,
    pub(super) outputs: Vec<usize>,
}
impl PolynomialArena {
    pub fn arena(&self) -> &Expression {
        &self.arena
    }
    /// For each emitted slot in order, the node of its output in `arena()`.
    pub fn outputs(&self) -> &[usize] {
        &self.outputs
    }
}
/// Some power-of-two height of at least 2 is admitted by the policy. On the
/// subgroup of order h, rotation by `offset mod h` realizes a cyclic read
/// exactly and a finite read wherever its window is defined. KoalaBear has
/// two-adicity 24, so every power-of-two height up to HEIGHT_LIMIT has that
/// subgroup.
pub(super) fn two_adic_premise(t: &Table) -> Result<()> {
    if u64::from(t.height.min.max(2)).next_power_of_two() > u64::from(t.height.max) {
        return Err(Error("bundle-polynomial-two-adic"));
    }
    Ok(())
}
/// The height checks every height-taking view kernel starts with: a
/// power-of-two height of at least 2 that the policy admits.
pub(super) fn checked_height(t: &Table, height: u64) -> Result<u32> {
    if height < 2 || !height.is_power_of_two() {
        return Err(Error("bundle-polynomial-two-adic"));
    }
    u32::try_from(height)
        .ok()
        .filter(|h| (t.height.min..=t.height.max).contains(h))
        .ok_or(Error("bundle-height"))
}
/// Element widths of the table's witness, configuration and public matrices,
/// after checking that its declared data at this height, with every public
/// slot, stays within the coordinate bound.
pub(super) fn data_widths(bundle: &Bundle, t: &Table, height: u64) -> Result<[u64; 3]> {
    // Below HEIGHT_LIMIT, 256 groups of width 2^16 and 2^16 slots of eight
    // coordinates, these products and sums cannot overflow.
    let element = |field| degree(field).expect("admitted field") as u64;
    let mut widths = [0; 3];
    let mut coordinates = bundle.publics.iter().map(|s| element(s.field)).sum::<u64>();
    for g in &t.groups {
        widths[kind(g.authority) as usize - 1] += u64::from(g.width);
        coordinates += height * u64::from(g.width) * element(g.field);
    }
    if coordinates > COORDINATE_LIMIT {
        return Err(Error("bundle-data-limit"));
    }
    Ok(widths)
}
/// A window is an interval condition: the extreme offsets of the outputs'
/// reads decide it.
pub(super) fn window(
    t: &Table,
    facts: &[OutputFact],
    scope: Scope,
    h: u32,
    outputs: &[usize],
) -> Result<()> {
    let offsets = outputs
        .iter()
        .flat_map(|p| facts[*p].reads.iter().map(|r| r.1));
    let extremes = [offsets.clone().min(), offsets.max()];
    window_at(scope, t.read_model, h, &extremes.map(|o| o.unwrap_or(0)))
}

impl Bundle {
    /// Static premises shared by the polynomial kernels: table index, an
    /// installed carrier, carrier compatibility of every public slot, table
    /// group and assertion output, and a power-of-two height of at least 2
    /// admitted by the height policy. Interaction-only outputs are not
    /// checked. Nothing is allocated.
    pub fn polynomial_view(&self, table: usize, field: Identity) -> Result<PolynomialView<'_>> {
        let t = self
            .tables
            .get(table)
            .ok_or(Error("relation-table-index"))?;
        // Arena formation admits add and mul only of equal fields and only the
        // KoalaBear-to-Ext8 embedding. Every node an output needs therefore has
        // the output's field or, below Ext8, KoalaBear: checking each assertion
        // output checks its whole sub-DAG.
        if !matches!(field, Identity::KoalaBear | Identity::KoalaBearExt8)
            || self.publics.iter().any(|p| !lifts(p.field, field))
            || t.groups.iter().any(|g| !lifts(g.field, field))
            || t.assertions
                .iter()
                .any(|a| !lifts(self.facts[table][a.output].field, field))
        {
            return Err(Error("relation-table-carrier"));
        }
        two_adic_premise(t)?;
        Ok(PolynomialView {
            bundle: self,
            table,
            field,
        })
    }
}
impl PolynomialView<'_> {
    /// The viewed table's definition in the admitted Bundle.
    pub fn definition(&self) -> &Table {
        &self.bundle.tables[self.table]
    }
    pub fn field(&self) -> Identity {
        self.field
    }
    pub fn input_count(&self) -> usize {
        self.definition().inputs.len()
    }
    pub fn assertion_count(&self) -> usize {
        self.definition().assertions.len()
    }
    /// Units charged by every polynomial kernel, before its height profile or
    /// any preparation: nodes, inputs, groups, public slots, assertions, the
    /// read facts of each assertion's output, and 1. None grows with height.
    pub fn work(&self) -> u64 {
        let t = self.definition();
        let reads: u64 = t
            .assertions
            .iter()
            .map(|a| self.bundle.facts[self.table][a.output].reads.len() as u64)
            .sum();
        (t.arena.nodes().len()
            + t.inputs.len()
            + t.groups.len()
            + self.bundle.publics.len()
            + t.assertions.len()
            + 1) as u64
            + reads
    }
    /// Additional units of one substituted point: nodes, inputs, assertions
    /// and 1. A batch charges this once per row.
    pub fn point_work(&self) -> u64 {
        let t = self.definition();
        (t.arena.nodes().len() + t.inputs.len() + t.assertions.len() + 1) as u64
    }
    /// The sub-DAG of the distinct assertion outputs and each assertion's
    /// node in it. Callers bound its storage, which never exceeds the table
    /// arena plus a few indices per assertion, and charge its work before
    /// preparing.
    pub fn prepare(&self) -> Result<PolynomialArena> {
        let t = self.definition();
        let mut positions: Vec<_> = t.assertions.iter().map(|a| a.output).collect();
        positions.sort_unstable();
        positions.dedup();
        let arena = t.arena.select(&positions)?;
        let outputs = t
            .assertions
            .iter()
            .map(|a| arena.outputs()[positions.binary_search(&a.output).expect("selected")])
            .collect();
        Ok(PolynomialArena { arena, outputs })
    }
    /// The height profile shared by `shape`, `input` and `scope`: two-adic
    /// height, height policy, every assertion window, then the data, work and
    /// quotient bounds. Nothing is allocated.
    fn profile(&self, height: u64) -> Result<(u32, PolynomialShape)> {
        let t = self.definition();
        let h = checked_height(t, height)?;
        let facts = &self.bundle.facts[self.table];
        for a in &t.assertions {
            window(t, facts, a.scope, h, &[a.output])?;
        }
        let widths = data_widths(self.bundle, t, height)?;
        if !t.assertions.is_empty() && height * self.point_work() > WORK_LIMIT {
            return Err(Error("bundle-work-limit"));
        }
        // Read polynomials have degree at most h-1. A nonzero quotient of an
        // assertion with degree d over its active rows A has degree at most
        // d*(h-1) - |A|; when d*(h-1) < |A| exact divisibility forces zero.
        let mut chunks = 1;
        for a in &t.assertions {
            let (lo, hi) = scope_rows(a.scope, h);
            if lo >= hi {
                continue;
            }
            let numerator = u64::from(facts[a.output].degree) * (height - 1);
            if let Some(quotient) = numerator.checked_sub(u64::from(hi - lo)) {
                chunks = chunks.max(quotient / height + 1);
            }
        }
        if chunks * height > POLYNOMIAL_SIZE_LIMIT {
            return Err(Error("bundle-polynomial-limit"));
        }
        Ok((
            h,
            PolynomialShape {
                witness_width: widths[0],
                config_width: widths[1],
                public_width: widths[2],
                public_slots: self.bundle.publics.len() as u64,
                inputs: t.inputs.len() as u64,
                assertions: t.assertions.len() as u64,
                quotient_chunks: chunks,
            },
        ))
    }
    pub fn shape(&self, height: u64) -> Result<PolynomialShape> {
        self.profile(height).map(|(_, shape)| shape)
    }
    /// The descriptor of one ordered arena input, after the height profile.
    pub fn input(&self, height: u64, slot: u64) -> Result<PolynomialInput> {
        self.profile(height)?;
        let t = self.definition();
        let input = usize::try_from(slot)
            .ok()
            .and_then(|s| t.inputs.get(s))
            .ok_or(Error("relation-table-input-index"))?;
        Ok(match *input {
            Input::Public(slot) => PolynomialInput {
                kind: 0,
                column: u64::from(slot),
                rotation: 0,
            },
            Input::Read {
                group,
                offset,
                column,
            } => {
                let authority = t.groups[group as usize].authority;
                let first: u64 = t.groups[..group as usize]
                    .iter()
                    .filter(|g| g.authority == authority)
                    .map(|g| u64::from(g.width))
                    .sum();
                PolynomialInput {
                    kind: kind(authority),
                    column: first + u64::from(column),
                    rotation: i64::from(offset).rem_euclid(height as i64) as u64,
                }
            }
        })
    }
    /// Active rows `[begin, end)` of one assertion, after the height profile.
    /// An empty interior scope is `(0, 0)`; an empty interval keeps its start.
    pub fn scope(&self, height: u64, assertion: u64) -> Result<(u64, u64)> {
        let (h, _) = self.profile(height)?;
        let a = usize::try_from(assertion)
            .ok()
            .and_then(|a| self.definition().assertions.get(a))
            .ok_or(Error("relation-table-assertion-index"))?;
        let (lo, hi) = scope_rows(a.scope, h);
        Ok((u64::from(lo), u64::from(hi)))
    }
}
