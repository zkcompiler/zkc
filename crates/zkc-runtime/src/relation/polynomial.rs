//! A polynomial view of one present table on the multiplicative subgroup whose
//! order is the table's own height. The immutable Bundle owns the bindings and
//! degree facts; this view derives the descriptors a consuming library needs
//! and the ordered assertion arena. It selects no quotient combination,
//! challenge, commitment or proof, and claims nothing about interactions.
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
fn lifts(field: Identity, carrier: Identity) -> bool {
    field == carrier || (carrier == Identity::KoalaBearExt8 && field == Identity::KoalaBear)
}
fn kind(authority: Authority) -> u64 {
    match authority {
        Authority::Witness => 1,
        Authority::Config => 2,
        Authority::Public => 3,
    }
}

/// Borrowing the admitted Bundle prevents a view from being used with a
/// different definition. Nothing here grows with the height.
#[derive(Clone, Debug)]
pub struct PolynomialView<'a> {
    bundle: &'a Bundle,
    table: usize,
    field: Identity,
    arena: Expression,      // Sub-DAG of the assertion outputs.
    assertions: Vec<usize>, // Assertion -> position in `arena`'s outputs.
    widths: [u64; 3],       // Witness, configuration, public groups.
    columns: Vec<u64>,      // First combined column of each group.
    reads: u64,             // Syntactic reads over assertion outputs.
}
impl Bundle {
    /// Static premises shared by the four polynomial kernels: table index,
    /// carrier compatibility of every public slot, table group and node an
    /// assertion needs, and a power-of-two height of at least 2 admitted by
    /// the height policy. Interaction-only outputs are not selected.
    pub fn polynomial_view(&self, table: usize, field: Identity) -> Result<PolynomialView<'_>> {
        let t = self
            .tables
            .get(table)
            .ok_or(Error("relation-table-index"))?;
        if degree(field).is_none()
            || self.publics.iter().any(|p| !lifts(p.field, field))
            || t.groups.iter().any(|g| !lifts(g.field, field))
        {
            return Err(Error("relation-table-carrier"));
        }
        let positions: Vec<_> = t
            .assertions
            .iter()
            .map(|a| a.output)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let arena = t.arena.select(&positions)?;
        if arena.facts().iter().any(|f| !lifts(f.field, field)) {
            return Err(Error("relation-table-carrier"));
        }
        // On the subgroup of order h, rotation by `offset mod h` realizes a
        // cyclic read exactly and a finite read wherever its window is defined.
        if u64::from(t.height.min.max(2)).next_power_of_two() > u64::from(t.height.max) {
            return Err(Error("bundle-polynomial-two-adic"));
        }
        let mut widths = [0; 3];
        let columns = t
            .groups
            .iter()
            .map(|g| {
                let width = &mut widths[kind(g.authority) as usize - 1];
                let first = *width;
                *width += u64::from(g.width);
                first
            })
            .collect();
        Ok(PolynomialView {
            bundle: self,
            table,
            field,
            assertions: t
                .assertions
                .iter()
                .map(|a| positions.binary_search(&a.output).expect("selected"))
                .collect(),
            arena,
            widths,
            columns,
            reads: t
                .assertions
                .iter()
                .map(|a| self.facts[table][a.output].reads.len() as u64)
                .sum(),
        })
    }
}
impl PolynomialView<'_> {
    fn definition(&self) -> &Table {
        &self.bundle.tables[self.table]
    }
    pub fn field(&self) -> Identity {
        self.field
    }
    pub fn input_count(&self) -> usize {
        self.definition().inputs.len()
    }
    pub fn assertion_count(&self) -> usize {
        self.assertions.len()
    }
    /// The selected assertion sub-DAG. It keeps the table's input numbering;
    /// its outputs are the distinct assertion outputs in arena order.
    pub fn arena(&self) -> &Expression {
        &self.arena
    }
    /// For each assertion in order, its position in `arena().outputs()`.
    pub fn assertion_outputs(&self) -> &[usize] {
        &self.assertions
    }
    /// Units charged by every polynomial kernel: the static reference check
    /// and the height profile, both independent of the height.
    pub fn work(&self) -> u64 {
        let t = self.definition();
        (t.arena.nodes().len()
            + t.inputs.len()
            + t.groups.len()
            + self.bundle.publics.len()
            + t.assertions.len()
            + 1) as u64
            + self.reads
    }
    /// Additional units of one point substitution, with its preparation.
    pub fn point_work(&self) -> u64 {
        let t = self.definition();
        (t.arena.nodes().len() + t.inputs.len() + t.assertions.len() + 1) as u64
    }
    /// The height profile shared by `shape`, `input` and `scope`: two-adic
    /// height, height policy, every assertion window, then the data, work and
    /// quotient bounds. Nothing is allocated in proportion to the height.
    fn profile(&self, height: u64) -> Result<(u32, PolynomialShape)> {
        let t = self.definition();
        if height < 2 || !height.is_power_of_two() {
            return Err(Error("bundle-polynomial-two-adic"));
        }
        let h = u32::try_from(height)
            .ok()
            .filter(|h| (t.height.min..=t.height.max).contains(h))
            .ok_or(Error("bundle-height"))?;
        let facts = &self.bundle.facts[self.table];
        for a in &t.assertions {
            let offsets: Vec<_> = facts[a.output].reads.iter().map(|r| r.1).collect();
            window_at(a.scope, t.read_model, h, &offsets)?;
        }
        let element = |field| degree(field).expect("admitted field") as u64;
        let coordinates = self
            .bundle
            .publics
            .iter()
            .map(|s| element(s.field))
            .sum::<u64>()
            + t.groups
                .iter()
                .map(|g| height * u64::from(g.width) * element(g.field))
                .sum::<u64>();
        if coordinates > COORDINATE_LIMIT {
            return Err(Error("bundle-data-limit"));
        }
        let scan = (t.arena.nodes().len() + t.inputs.len() + t.assertions.len() + 1) as u64;
        if !t.assertions.is_empty() && height * scan > WORK_LIMIT {
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
                witness_width: self.widths[0],
                config_width: self.widths[1],
                public_width: self.widths[2],
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
            } => PolynomialInput {
                kind: kind(t.groups[group as usize].authority),
                column: self.columns[group as usize] + u64::from(column),
                rotation: i64::from(offset).rem_euclid(height as i64) as u64,
            },
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
