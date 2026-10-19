/// Exact checked shape over immutable row-major storage, without materialization.
pub(crate) struct RowMajor<'a, T> {
    data: &'a [T],
    rows: usize,
    cols: usize,
}

impl<'a, T> RowMajor<'a, T> {
    pub(crate) fn new(data: &'a [T], rows: usize, cols: usize) -> Option<Self> {
        if rows.checked_mul(cols)? != data.len() {
            return None;
        }
        Some(Self { data, rows, cols })
    }

    pub(crate) fn rows(&self) -> usize {
        self.rows
    }

    pub(crate) fn cols(&self) -> usize {
        self.cols
    }

    pub(crate) fn row(&self, row: usize) -> Option<&'a [T]> {
        if row >= self.rows {
            return None;
        }
        let start = row.checked_mul(self.cols)?;
        self.data.get(start..start.checked_add(self.cols)?)
    }

    pub(crate) fn get(&self, row: usize, col: usize) -> Option<&'a T> {
        if row >= self.rows || col >= self.cols {
            return None;
        }
        self.data.get(row.checked_mul(self.cols)?.checked_add(col)?)
    }

    /// Index the logical `(cols, rows)` transpose without allocating or copying.
    pub(crate) fn transpose(&self, row: usize, col: usize) -> Option<&'a T> {
        self.get(col, row)
    }
}
