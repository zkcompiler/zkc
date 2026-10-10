//! The interaction view of one table: its declared height policy, interaction
//! descriptors and record substitutions. The immutable Bundle owns the
//! interactions and degree facts; this view derives the descriptors a
//! consuming library needs and prepares the record outputs for substitution.
//! It applies no scope, multiplicity range, balance, challenge or reduction,
//! and claims nothing about presence or satisfaction.
use super::polynomial::{data_widths, lifts, window};
use super::*;

/// One interaction at a height. `side` is `None` for a field balance, which
/// has no side. `local` is the local key. `bound` is a multiset's bound or a
/// field balance's declared count bound. `[begin, end)` are the active rows
/// of its scope. `tuple_degree` is the largest degree fact of its tuple
/// outputs (0 without any) and `count_degree` that of its count output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InteractionDescriptor {
    pub kind: ChannelKind,
    pub channel: u64,
    pub side: Option<Side>,
    pub local: Option<u32>,
    pub begin: u64,
    pub end: u64,
    pub arity: u64,
    pub bound: Option<u64>,
    pub tuple_degree: u64,
    pub count_degree: u64,
}

/// Borrowing the admitted Bundle prevents a view from being used with a
/// different definition. The view owns nothing: descriptors are derived on
/// demand, and only `prepare` allocates.
#[derive(Clone, Copy, Debug)]
pub struct InteractionView<'a> {
    bundle: &'a Bundle,
    table: usize,
    field: Identity,
}
impl Bundle {
    /// Whole-table carrier admission, the static premise of
    /// the interaction kernels: table index, an installed carrier, and
    /// carrier compatibility of every public slot, table group, assertion
    /// output and interaction output. No height is involved, so the declared
    /// policy of any table is exposed. Nothing is allocated.
    pub fn interaction_view(&self, table: usize, field: Identity) -> Result<InteractionView<'_>> {
        let t = self
            .tables
            .get(table)
            .ok_or(Error("relation-table-index"))?;
        // Every node an output needs has the output's field or, below Ext8,
        // KoalaBear: checking each output checks its whole sub-DAG. Every
        // arena output is an assertion or interaction output.
        let facts = &self.facts[table];
        if !matches!(field, Identity::KoalaBear | Identity::KoalaBearExt8)
            || self.publics.iter().any(|p| !lifts(p.field, field))
            || t.groups.iter().any(|g| !lifts(g.field, field))
            || t.assertions
                .iter()
                .any(|a| !lifts(facts[a.output].field, field))
            || t.interactions
                .iter()
                .flat_map(Interaction::output_indices)
                .any(|o| !lifts(facts[o].field, field))
        {
            return Err(Error("relation-table-carrier"));
        }
        Ok(InteractionView {
            bundle: self,
            table,
            field,
        })
    }
}
impl InteractionView<'_> {
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
    pub fn interaction_count(&self) -> usize {
        self.definition().interactions.len()
    }
    /// Values per record row: each interaction's arity plus one count. At
    /// most 4,096 interactions of arity 64, so this cannot overflow.
    pub fn record_width(&self) -> usize {
        self.definition()
            .interactions
            .iter()
            .map(|i| i.parts().3.len() + 1)
            .sum()
    }
    /// The declared presence and height policy, whatever heights the view
    /// could interpret.
    pub fn policy(&self) -> (bool, Height) {
        let t = self.definition();
        (t.optional, t.height)
    }
    /// Units charged by every interaction kernel, before its height profile
    /// or any preparation: nodes, inputs, groups, public slots, assertions,
    /// record width, the read facts of each assertion output and of each
    /// interaction output, and 1. None grows with height.
    pub fn work(&self) -> u64 {
        let t = self.definition();
        let facts = &self.bundle.facts[self.table];
        let reads: usize = t
            .assertions
            .iter()
            .map(|a| a.output)
            .chain(t.interactions.iter().flat_map(Interaction::output_indices))
            .map(|o| facts[o].reads.len())
            .sum();
        (t.arena.nodes().len()
            + t.inputs.len()
            + t.groups.len()
            + self.bundle.publics.len()
            + t.assertions.len()
            + self.record_width()
            + reads
            + 1) as u64
    }
    /// Additional units of one substituted record row: nodes, inputs, record
    /// width and 1. A batch charges this once per row.
    pub fn point_work(&self) -> u64 {
        let t = self.definition();
        (t.arena.nodes().len() + t.inputs.len() + self.record_width() + 1) as u64
    }
    /// The sub-DAG of the distinct record outputs and, for each record slot
    /// in order, its node in it. Callers bound its storage, which never
    /// exceeds the table arena plus one index per record slot, and charge its
    /// work before preparing.
    pub fn prepare(&self) -> Result<PolynomialArena> {
        let t = self.definition();
        let slots: Vec<usize> = t
            .interactions
            .iter()
            .flat_map(Interaction::output_indices)
            .collect();
        let mut positions = slots.clone();
        positions.sort_unstable();
        positions.dedup();
        let arena = t.arena.select(&positions)?;
        let outputs = slots
            .iter()
            .map(|o| arena.outputs()[positions.binary_search(o).expect("selected")])
            .collect();
        Ok(PolynomialArena { arena, outputs })
    }
    /// The height profile shared by the descriptors: height policy, every
    /// assertion and interaction window, then the data and
    /// record work bounds. Nothing is allocated.
    fn profile(&self, height: u64) -> Result<u32> {
        let t = self.definition();
        let h = u32::try_from(height)
            .ok()
            .filter(|h| (t.height.min..=t.height.max).contains(h))
            .filter(|h| !t.height.power_of_two || h.is_power_of_two())
            .ok_or(Error("bundle-height"))?;
        let facts = &self.bundle.facts[self.table];
        for a in &t.assertions {
            window(t, facts, a.scope, h, &[a.output])?;
        }
        for i in &t.interactions {
            // Borrow each output: metadata and precharge paths allocate nothing.
            for output in i.output_indices() {
                window(t, facts, i.parts().2, h, std::slice::from_ref(&output))?;
            }
        }
        data_widths(self.bundle, t, height)?;
        if !t.interactions.is_empty() && height * self.point_work() > WORK_LIMIT {
            return Err(Error("bundle-work-limit"));
        }
        Ok(h)
    }
    /// Interaction count and record width, after the height profile.
    pub fn interactions(&self, height: u64) -> Result<(u64, u64)> {
        self.profile(height)?;
        Ok((self.interaction_count() as u64, self.record_width() as u64))
    }
    /// The descriptor of one interaction, after the height profile.
    pub fn interaction(&self, height: u64, index: u64) -> Result<InteractionDescriptor> {
        let h = self.profile(height)?;
        let interaction = usize::try_from(index)
            .ok()
            .and_then(|i| self.definition().interactions.get(i))
            .ok_or(Error("relation-table-interaction-index"))?;
        let facts = &self.bundle.facts[self.table];
        let (channel, locality, scope, tuple, count) = interaction.parts();
        let (lo, hi) = scope_rows(scope, h);
        let (kind, side, bound) = match interaction {
            Interaction::FieldBalance { declared, .. } => {
                (ChannelKind::FieldBalance, None, *declared)
            }
            Interaction::Multiset { side, bound, .. } => {
                (ChannelKind::Multiset, Some(*side), Some(*bound))
            }
        };
        Ok(InteractionDescriptor {
            kind,
            channel: channel as u64,
            side,
            local: match locality {
                Locality::Global => None,
                Locality::Local(key) => Some(key),
            },
            begin: u64::from(lo),
            end: u64::from(hi),
            arity: tuple.len() as u64,
            bound,
            tuple_degree: tuple
                .iter()
                .map(|p| u64::from(facts[*p].degree))
                .max()
                .unwrap_or(0),
            count_degree: u64::from(facts[count].degree),
        })
    }
}
