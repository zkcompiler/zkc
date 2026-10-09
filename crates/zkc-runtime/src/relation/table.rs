//! A homogeneous view of one present table's assertions. The immutable Bundle
//! owns the bindings; callers supply actual columns, never expanded reads or
//! selector values. Interaction and presence obligations are separate.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TableLengths {
    pub witness: usize,
    pub configuration: usize,
    pub public_data: usize,
    pub results: usize,
}
#[derive(Clone, Debug)]
pub struct TableData {
    pub height: u32,
    pub witness: Columns,
    pub configuration: Columns,
    pub public_data: Columns,
}
/// Borrowing the admitted Bundle prevents a view from being used with a
/// different definition. Widths count field elements, not base coordinates.
#[derive(Clone, Debug)]
pub struct TableView<'a> {
    bundle: &'a Bundle,
    table: usize,
    field: Identity,
    widths: [usize; 3], // witness, configuration, public
    degree: u32,
}
impl Bundle {
    pub fn table_view(&self, table: usize, field: Identity) -> Result<TableView<'_>> {
        let t = self
            .tables
            .get(table)
            .ok_or(Error("relation-table-index"))?;
        if degree(field).is_none()
            || self.publics.iter().any(|p| p.field != field)
            || t.groups.iter().any(|g| g.field != field)
            || t.assertions
                .iter()
                .any(|a| self.facts[table][a.output].field != field)
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
        let selected = t.arena.select(&positions)?;
        if selected.facts().iter().any(|f| {
            f.field != field
                && !(field == Identity::KoalaBearExt8 && f.field == Identity::KoalaBear)
        }) {
            return Err(Error("relation-table-carrier"));
        }
        let mut widths = [0; 3];
        for group in &t.groups {
            widths[authority(group.authority)] += group.width as usize;
        }
        let degree = t
            .assertions
            .iter()
            .map(|a| self.facts[table][a.output].degree)
            .max()
            .unwrap_or(0);
        Ok(TableView {
            bundle: self,
            table,
            field,
            widths,
            degree,
        })
    }
}
fn authority(a: Authority) -> usize {
    match a {
        Authority::Witness => 0,
        Authority::Config => 1,
        Authority::Public => 2,
    }
}
impl TableView<'_> {
    pub fn field(&self) -> Identity {
        self.field
    }
    pub fn degree(&self) -> u32 {
        self.degree
    }
    pub fn assertion_count(&self) -> usize {
        self.bundle.tables[self.table].assertions.len()
    }
    /// A conservative count of visits used by the native shared work budget.
    pub fn work(&self, height: u32) -> u64 {
        let t = &self.bundle.tables[self.table];
        (u64::from(height) + 1)
            * (t.arena.nodes().len() + t.inputs.len() + t.assertions.len() + 1) as u64
    }
    pub fn lengths(&self, height: u32) -> Result<TableLengths> {
        let t = &self.bundle.tables[self.table];
        if height < t.height.min
            || height > t.height.max
            || (t.height.power_of_two && !height.is_power_of_two())
        {
            return Err(Error("bundle-height"));
        }
        let h = u64::from(height);
        let w = h * self.widths[0] as u64;
        let c = h * self.widths[1] as u64;
        let p = h * self.widths[2] as u64 + self.bundle.publics.len() as u64;
        let coordinates = degree(self.field).expect("admitted field") as u64;
        if (w + c + p) * coordinates > COORDINATE_LIMIT {
            return Err(Error("bundle-data-limit"));
        }
        for a in &t.assertions {
            let offsets: Vec<_> = self.bundle.facts[self.table][a.output]
                .reads
                .iter()
                .map(|(_, offset, _)| *offset)
                .collect();
            window_at(a.scope, t.read_model, height, &offsets)?;
        }
        if !t.assertions.is_empty()
            && h * (t.arena.nodes().len() + t.inputs.len() + t.assertions.len() + 1) as u64
                > WORK_LIMIT
        {
            return Err(Error("bundle-work-limit"));
        }
        let results = h * t.assertions.len() as u64;
        if results > RESULT_RECORD_LIMIT || results * coordinates > RESULT_COORDINATE_LIMIT {
            return Err(Error("bundle-result-limit"));
        }
        Ok(TableLengths {
            witness: w as usize,
            configuration: c as usize,
            public_data: p as usize,
            results: results as usize,
        })
    }
    pub fn slice(&self, c: &Configuration, i: &Instance, w: &Witness) -> Result<TableData> {
        let admitted = self.bundle.admit(c, i, w)?;
        if !admitted.present[self.table] {
            return Err(Error("relation-table-absent"));
        }
        let height = admitted.heights[self.table];
        self.lengths(height)?;
        let mut carriers = [
            vec![],
            vec![],
            i.publics.iter().flatten().cloned().collect(),
        ];
        for (group, values) in self.bundle.tables[self.table]
            .groups
            .iter()
            .zip(self.bundle.present_groups(self.table, c, i, w))
        {
            carriers[authority(group.authority)].extend(values.iter().cloned());
        }
        let [witness, configuration, public_data] = carriers;
        Ok(TableData {
            height,
            witness,
            configuration,
            public_data,
        })
    }
    /// Dense row-major residuals with zero in inactive assertion slots. Only
    /// the sub-DAG of active assertions is interpreted. Scratch for one segment
    /// is dropped before the next; no height-sized collection of arenas exists.
    pub fn evaluate<A: Algebra>(
        &self,
        height: u32,
        witness: &[A::Value],
        configuration: &[A::Value],
        public_data: &[A::Value],
        algebra: &A,
    ) -> Result<Vec<A::Value>> {
        let lengths = self.lengths(height)?;
        for (actual, expected, error) in [
            (
                witness.len(),
                lengths.witness,
                "relation-table-witness-shape",
            ),
            (
                configuration.len(),
                lengths.configuration,
                "relation-table-configuration-shape",
            ),
            (
                public_data.len(),
                lengths.public_data,
                "relation-table-public-shape",
            ),
        ] {
            if actual != expected {
                return Err(Error(error));
            }
        }
        let zero = algebra.constant(self.field, "0")?;
        let mut result = vec![zero; lengths.results];
        let t = &self.bundle.tables[self.table];
        if t.assertions.is_empty() {
            return Ok(result);
        }
        let carriers = [witness, configuration, public_data];
        let mut offsets = [0, 0, self.bundle.publics.len()];
        let mut groups = Vec::with_capacity(t.groups.len());
        for g in &t.groups {
            let carrier = authority(g.authority);
            groups.push((carrier, offsets[carrier], g.width as usize));
            offsets[carrier] += height as usize * g.width as usize;
        }
        let ranges: Vec<_> = t
            .assertions
            .iter()
            .map(|a| scope_rows(a.scope, height))
            .collect();
        let mut cuts = BTreeSet::from([0, height]);
        for &(lo, hi) in &ranges {
            if lo < hi {
                cuts.insert(lo);
                cuts.insert(hi);
            }
        }
        let cuts: Vec<_> = cuts.into_iter().collect();
        for cut in cuts.windows(2) {
            let (from, to) = (cut[0], cut[1]);
            let active: Vec<_> = ranges
                .iter()
                .enumerate()
                .filter(|(_, (lo, hi))| lo < hi && *lo <= from && to <= *hi)
                .map(|(i, _)| i)
                .collect();
            if active.is_empty() {
                continue;
            }
            let positions: Vec<_> = active
                .iter()
                .map(|i| t.assertions[*i].output)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            let selected = t.arena.select(&positions)?;
            for row in from..to {
                let mut fetch = |input: usize| match t.inputs[input] {
                    Input::Public(slot) => Ok(public_data[slot as usize].clone()),
                    Input::Read {
                        group,
                        offset,
                        column,
                    } => {
                        let (carrier, base, width) = groups[group as usize];
                        let read = read_row(t.read_model, height, row, offset) as usize;
                        Ok(carriers[carrier][base + read * width + column as usize].clone())
                    }
                };
                let values = interpret(&selected, algebra, &mut fetch)?;
                for &index in &active {
                    let output = positions
                        .binary_search(&t.assertions[index].output)
                        .expect("selected output");
                    result[row as usize * t.assertions.len() + index] = values[output].clone();
                }
            }
        }
        Ok(result)
    }
}
