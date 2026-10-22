//! Immutable canonical sparse COO and typed contractions, without VM policy.
use crate::fields::Coefficient;
use std::sync::Arc;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Index,
    Order,
    Zero,
    Shape,
    Count,
    Allocation,
}
impl Error {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Index => "matrix-index",
            Self::Order => "matrix-order",
            Self::Zero => "matrix-zero",
            Self::Shape => "matrix-shape",
            Self::Count => "matrix-count",
            Self::Allocation => "allocation",
        }
    }
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.code())
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
/// Entries are unique, nonzero and strictly ordered by (row, column). Only
/// checked constructors can create this representation; clones share backing.
#[derive(Clone, Debug)]
pub struct SparseCoo<S> {
    rows: usize,
    columns: usize,
    entries: Arc<[(u32, u32, S)]>,
}
impl<S> SparseCoo<S> {
    pub fn rows(&self) -> usize {
        self.rows
    }
    pub fn columns(&self) -> usize {
        self.columns
    }
    pub fn entries(&self) -> &[(u32, u32, S)] {
        &self.entries
    }
    /// Shared immutable entries; adapters may account for their backing identity.
    pub fn storage(&self) -> &Arc<[(u32, u32, S)]> {
        &self.entries
    }
}
/// Checked lookup in the logical coefficient map. Missing entries within the
/// shape denote zero; coordinates outside the shape are refused.
pub fn get<S: Coefficient>(matrix: &SparseCoo<S>, row: usize, column: usize) -> Result<S> {
    if row >= matrix.rows || column >= matrix.columns {
        return Err(Error::Index);
    }
    // Stored coordinates are u32. A larger logical coordinate has no stored
    // nonzero; do not narrow it into an unrelated coordinate.
    let (Ok(row), Ok(column)) = (u32::try_from(row), u32::try_from(column)) else {
        return Ok(S::zero());
    };
    Ok(matrix
        .entries
        .binary_search_by_key(&(row, column), |&(r, c, _)| (r, c))
        .map(|i| matrix.entries[i].2)
        .unwrap_or_else(|_| S::zero()))
}
fn entry<S: Coefficient>(
    rows: usize,
    columns: usize,
    previous: Option<(u32, u32)>,
    current: (u32, u32, S),
) -> Result<()> {
    let (r, c, a) = current;
    if r as usize >= rows || c as usize >= columns {
        return Err(Error::Index);
    }
    if previous.is_some_and(|p| p >= (r, c)) {
        return Err(Error::Order);
    }
    if a == S::zero() {
        return Err(Error::Zero);
    }
    Ok(())
}
pub fn from_entries<S: Coefficient>(
    rows: usize,
    columns: usize,
    entries: &[(u32, u32, S)],
) -> Result<SparseCoo<S>> {
    let cells = rows.checked_mul(columns).ok_or(Error::Count)?;
    if entries.len() > cells {
        return Err(Error::Count);
    }
    let mut previous = None;
    for &e in entries {
        entry(rows, columns, previous, e)?;
        previous = Some((e.0, e.1));
    }
    let mut owned = crate::allocation::reserve(entries.len()).map_err(|_| Error::Allocation)?;
    owned.extend_from_slice(entries);
    Ok(SparseCoo {
        rows,
        columns,
        entries: owned.into(),
    })
}

fn contract_row<S: Coefficient>(entries: &[(u32, u32, S)], x: &[S]) -> S {
    entries
        .iter()
        .map(|&(_, c, a)| a * x[c as usize])
        .reduce(|sum, term| sum + term)
        .unwrap_or_else(S::zero)
}
/// Contract only the selected row. Sorted COO gives a contiguous range, found
/// without reading coefficients in other rows or allocating a dense vector.
pub fn row_dot<S: Coefficient>(m: &SparseCoo<S>, x: &[S], row: usize) -> Result<S> {
    if x.len() != m.columns {
        return Err(Error::Shape);
    }
    if row >= m.rows {
        return Err(Error::Index);
    }
    let start = m.entries.partition_point(|&(r, _, _)| (r as usize) < row);
    let end = start + m.entries[start..].partition_point(|&(r, _, _)| (r as usize) == row);
    Ok(contract_row(&m.entries[start..end], x))
}

/// Row-major COO has no contiguous column range. Scan its existing nonzeros,
/// multiplying only the selected column and retaining just one accumulator.
pub fn column_dot<S: Coefficient>(m: &SparseCoo<S>, y: &[S], column: usize) -> Result<S> {
    if y.len() != m.rows {
        return Err(Error::Shape);
    }
    if column >= m.columns {
        return Err(Error::Index);
    }
    Ok(m.entries
        .iter()
        .filter(|&&(_, c, _)| c as usize == column)
        .fold(S::zero(), |sum, &(r, _, a)| sum + a * y[r as usize]))
}

/// Distributivity applies the left weight once per occupied row, without
/// materializing the forward product or changing the stored entry order.
pub fn bilinear<S: Coefficient>(m: &SparseCoo<S>, y: &[S], x: &[S]) -> Result<S> {
    if y.len() != m.rows || x.len() != m.columns {
        return Err(Error::Shape);
    }
    Ok(m.entries
        .chunk_by(|a, b| a.0 == b.0)
        .fold(S::zero(), |sum, row| {
            sum + y[row[0].0 as usize] * contract_row(row, x)
        }))
}

/// Complete destination shape is checked before writing; input storage remains immutable.
pub fn mul_into<S: Coefficient>(
    m: &SparseCoo<S>,
    x: &[S],
    transpose: bool,
    result: &mut [S],
) -> Result<()> {
    let (input, output) = if transpose {
        (m.rows, m.columns)
    } else {
        (m.columns, m.rows)
    };
    if x.len() != input || result.len() != output {
        return Err(Error::Shape);
    }
    result.fill(S::zero());
    if transpose {
        for row in m.entries.chunk_by(|a, b| a.0 == b.0) {
            let weight = x[row[0].0 as usize];
            for &(_, c, a) in row {
                result[c as usize] = result[c as usize] + a * weight;
            }
        }
    } else {
        for row in m.entries.chunk_by(|a, b| a.0 == b.0) {
            result[row[0].0 as usize] = contract_row(row, x);
        }
    }
    Ok(())
}
