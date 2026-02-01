use itertools::{EitherOrBoth, Itertools};
use p1::{Field, poly::Multilinear};
use std::collections::BTreeMap;
use std::ops::{Index, Neg, Sub};

/// A sparse matrix stored in Compressed Sparse Row (CSR) format.
///
/// CSR stores only non-zero entries, making it efficient for sparse matrices.
/// The format uses three arrays:
/// - `values`: the non-zero entries, stored row by row
/// - `col_indices`: the column index for each entry in `values`
/// - `row_offsets`: for row i, entries are in values[row_offsets[i]..row_offsets[i+1]]
///
/// Example: For the matrix [[1, 0, 2], [0, 0, 3], [4, 5, 0]]:
/// - values = [1, 2, 3, 4, 5]
/// - col_indices = [0, 2, 2, 0, 1]
/// - row_offsets = [0, 2, 3, 5]
#[derive(Debug, Clone)]
pub struct SparseMatrix<F> {
    pub rows: usize,
    pub cols: usize,
    pub values: Vec<F>,
    pub col_indices: Vec<usize>,
    pub row_offsets: Vec<usize>,
    zero: F,
}

impl<F: Field> SparseMatrix<F> {
    /// Creates an empty sparse matrix with the given dimensions.
    pub fn new(rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            values: Vec::new(),
            col_indices: Vec::new(),
            row_offsets: vec![0; rows + 1],
            zero: F::zero(),
        }
    }

    /// Converts the matrix to a multilinear extension.
    ///
    /// The matrix is flattened in column-major order (entries ordered by column, then row)
    /// and padded to a power of two. The MLE can then be evaluated at any point in F^n
    /// where n = log2(rows * cols rounded up to power of two).
    pub fn multilinear_extension(&self) -> Multilinear<F> {
        let row_size = self.rows.next_power_of_two();
        let col_size = self.cols.next_power_of_two();
        let n_vars = (row_size * col_size).ilog2() as usize;

        let mut evals = vec![F::zero(); row_size * col_size];
        for ((row, col), &val) in self.iter() {
            evals[col * row_size + row] = val;
        }
        Multilinear::new(n_vars, evals)
    }

    /// Creates a sparse matrix from a list of (row, col, value) entries.
    ///
    /// Duplicate entries at the same position are summed together.
    /// Zero entries are automatically filtered out.
    pub fn from_entries(
        rows: usize,
        cols: usize,
        entries: impl IntoIterator<Item = (usize, usize, F)>,
    ) -> Self {
        let mut map: BTreeMap<(usize, usize), F> = BTreeMap::new();
        for (i, j, val) in entries {
            assert!(i < rows && j < cols, "Index out of bounds");
            map.entry((i, j)).and_modify(|v| *v += val).or_insert(val);
        }

        let mut values = Vec::new();
        let mut col_indices = Vec::new();
        let mut row_offsets = vec![0; rows + 1];

        for ((row, col), val) in map.into_iter().filter(|(_, val)| !val.is_zero()) {
            values.push(val);
            col_indices.push(col);
            row_offsets[row + 1] += 1;
        }

        for i in 1..=rows {
            row_offsets[i] += row_offsets[i - 1];
        }

        Self {
            rows,
            cols,
            values,
            col_indices,
            row_offsets,
            zero: F::zero(),
        }
    }
    /// Multiplies the matrix by a dense vector, returning a dense result.
    pub fn mul_dense(&self, x: &[F]) -> Vec<F> {
        assert_eq!(x.len(), self.cols);
        let mut result = vec![F::zero(); self.rows];
        for (i, res) in result.iter_mut().enumerate() {
            let start = self.row_offsets[i];
            let end = self.row_offsets[i + 1];
            for idx in start..end {
                let col = self.col_indices[idx];
                let val = self.values[idx];
                *res += val * x[col];
            }
        }
        result
    }

    /// Multiplies the matrix by a sparse vector, returning a sparse result.
    pub fn mul_sparse(&self, vec: &SparseVector<F>) -> SparseVector<F> {
        assert_eq!(self.cols, vec.size);

        let mut result = SparseVector::new(self.rows);

        for row in 0..self.rows {
            let mut acc = F::zero();
            let start = self.row_offsets[row];
            let end = self.row_offsets[row + 1];

            for idx in start..end {
                let col = self.col_indices[idx];
                acc += self.values[idx] * vec[col];
            }

            if !acc.is_zero() {
                result.insert(row, acc);
            }
        }

        result
    }

    /// Returns the number of non-zero entries.
    pub fn nnz(&self) -> usize {
        self.values.len()
    }

    /// Adds a single entry to the matrix. Zero values are ignored.
    pub fn add_entry(&mut self, row: usize, col: usize, value: F) {
        if value.is_zero() {
            return;
        }
        assert!(row < self.rows && col < self.cols);

        let insert_pos = self.row_offsets[row + 1];
        self.col_indices.insert(insert_pos, col);
        self.values.insert(insert_pos, value);

        for r in (row + 1)..=self.rows {
            self.row_offsets[r] += 1;
        }
    }

    /// Iterates over all non-zero entries as ((row, col), value) tuples.
    pub fn iter(&self) -> impl Iterator<Item = ((usize, usize), &F)> {
        (0..self.rows).flat_map(|row| {
            self.row_iter(row)
                .map(move |(col, value)| ((row, col), value))
        })
    }

    /// Iterates over non-zero entries in a single row as (col, value) tuples.
    pub fn row_iter(&self, row: usize) -> impl Iterator<Item = (usize, &F)> {
        let start = self.row_offsets[row];
        let end = self.row_offsets[row + 1];
        self.col_indices[start..end]
            .iter()
            .zip(&self.values[start..end])
            .map(|(&col, val)| (col, val))
    }
}

impl<F> std::fmt::Display for SparseMatrix<F>
where
    F: std::fmt::Display + Clone + PartialEq,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "SparseMatrix ({} x {}):", self.rows, self.cols)?;
        for row in 0..self.rows {
            let start = self.row_offsets[row];
            let end = self.row_offsets[row + 1];

            // Collect the (col, value) pairs for the current row
            let row_entries = (start..end)
                .map(|i| (self.col_indices[i], &self.values[i]))
                .collect::<Vec<_>>();

            write!(f, "[")?;
            for col in 0..self.cols {
                if let Some((_, val)) = row_entries.iter().find(|(c, _)| *c == col) {
                    write!(f, " {val:>3}")?;
                } else {
                    write!(f, " {:>3}", self.zero)?;
                }
            }
            writeln!(f, " ]")?;
        }
        Ok(())
    }
}

impl<F: Field> Index<(usize, usize)> for SparseMatrix<F> {
    type Output = F;
    fn index(&self, index: (usize, usize)) -> &F {
        let start = self.row_offsets[index.0];
        let end = self.row_offsets[index.0 + 1];
        for idx in start..end {
            if self.col_indices[idx] == index.1 {
                return &self.values[idx];
            }
        }
        &self.zero
    }
}

/// A sparse vector that stores only non-zero entries.
///
/// Entries are stored in a BTreeMap for efficient lookup and ordered iteration.
/// Indexing a position with no stored value returns zero.
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SparseVector<F> {
    pub size: usize,
    contents: BTreeMap<usize, F>,
    zero: F,
}

use std::fmt::{self, Display};
impl<F: Display> Display for SparseVector<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.size {
            if i > 0 {
                write!(f, ", ")?;
            }
            match self.contents.get(&i) {
                Some(val) => write!(f, "{val}")?,
                None => write!(f, "{}", self.zero)?,
            }
        }
        write!(f, "]")
    }
}
impl<F: Field> Index<usize> for SparseVector<F> {
    type Output = F;
    fn index(&self, idx: usize) -> &F {
        self.contents.get(&idx).unwrap_or(&self.zero)
    }
}

impl<F: Field> IntoIterator for SparseVector<F> {
    type Item = (usize, F);
    type IntoIter = std::collections::btree_map::IntoIter<usize, F>;
    fn into_iter(self) -> Self::IntoIter {
        self.contents.into_iter()
    }
}

impl<F: Field> SparseVector<F> {
    /// Creates an empty sparse vector of the given size.
    pub fn new(size: usize) -> Self {
        Self {
            size,
            contents: BTreeMap::new(),
            zero: F::zero(),
        }
    }

    /// Creates a sparse vector from (index, value) pairs. Zero values are filtered out.
    pub fn from_entries(size: usize, entries: impl IntoIterator<Item = (usize, F)>) -> Self {
        Self {
            size,
            contents: entries.into_iter().filter(|(_, f)| !f.is_zero()).collect(),
            zero: F::zero(),
        }
    }

    /// Converts a dense vector to sparse representation.
    pub fn from_dense(dense: &[F]) -> Self {
        Self::from_entries(dense.len(), dense.iter().cloned().enumerate())
    }

    /// Iterates over non-zero entries as (index, value) pairs in sorted order.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &F)> {
        self.contents.iter().map(|(&idx, f)| (idx, f))
    }

    /// Converts to a dense vector, filling zeros for missing entries.
    pub fn to_dense(&self) -> Vec<F> {
        let mut dense = vec![F::zero(); self.size];
        for (i, &val) in self.iter() {
            dense[i] = val;
        }
        dense
    }

    /// Concatenates two sparse vectors into one.
    pub fn concat(&self, other: &SparseVector<F>) -> SparseVector<F> {
        let mut new_contents = self.contents.clone();
        for (&i, &v) in &other.contents {
            new_contents.insert(i + self.size, v);
        }

        SparseVector {
            size: self.size + other.size,
            contents: new_contents,
            zero: self.zero,
        }
    }

    /// Inserts or updates a value at the given index. Inserting zero removes the entry.
    pub fn insert(&mut self, idx: usize, value: F) {
        if value.is_zero() {
            self.remove(idx);
            return;
        }

        self.contents.insert(idx, value);
    }

    /// Removes the entry at the given index (equivalent to setting it to zero).
    pub fn remove(&mut self, idx: usize) {
        self.contents.remove(&idx);
    }

    /// Computes the dot product of two sparse vectors.
    ///
    /// This is efficient because it only iterates over indices where both vectors
    /// have non-zero entries, using a merge-join on the sorted indices.
    pub fn dot(&self, other: &Self) -> F {
        assert_eq!(self.size, other.size);
        self.iter()
            .merge_join_by(other.iter(), |(i, _), (j, _)| i.cmp(j))
            .filter_map(|entry| entry.both().map(|((_, &l), (_, &r))| l * r))
            .sum()
    }

    /// Merges two sparse vectors using custom functions for each case.
    ///
    /// - `f_both`: called when both vectors have a value at the same index
    /// - `f_left`: called when only self has a value at an index
    /// - `f_right`: called when only other has a value at an index
    ///
    /// Each function returns Option<F> -- returning None omits that entry from the result.
    pub fn merge(
        &self,
        other: &Self,
        mut f_both: impl FnMut(&F, &F) -> Option<F>,
        mut f_left: impl FnMut(&F) -> Option<F>,
        mut f_right: impl FnMut(&F) -> Option<F>,
    ) -> Self {
        assert_eq!(self.size, other.size);

        Self::from_entries(
            self.size,
            self.iter()
                .merge_join_by(other.iter(), |(i, _), (j, _)| i.cmp(j))
                .filter_map(|entry| match entry {
                    EitherOrBoth::Both((i, l), (_, r)) => f_both(l, r).map(|x| (i, x)),
                    EitherOrBoth::Left((i, v)) => f_left(v).map(|x| (i, x)),
                    EitherOrBoth::Right((i, v)) => f_right(v).map(|x| (i, x)),
                }),
        )
    }

    /// Adds two sparse vectors element-wise.
    pub fn add_sparse(&self, other: &Self) -> Self {
        self.merge(
            other,
            |&l, &r| {
                let sum = l + r;
                (!sum.is_zero()).then_some(sum)
            },
            |&l| Some(l),
            |&r| Some(r),
        )
    }

    /// Computes the Hadamard (element-wise) product of two sparse vectors.
    pub fn hadamard(&self, other: &Self) -> Self {
        self.merge(other, |&l, &r| Some(l * r), |_| None, |_| None)
    }

    /// Converts the vector to a multilinear extension, padding to a power of two.
    pub fn multilinear_extension(&self) -> Multilinear<F> {
        let size = self.size.next_power_of_two();
        let evals = (0..size)
            .map(|i| self.contents.get(&i).copied().unwrap_or_else(F::zero))
            .collect();
        Multilinear::new(size.ilog2() as usize, evals)
    }

    /// Returns the number of non-zero entries.
    pub fn nnz(&self) -> usize {
        self.contents.len()
    }
}

impl<F: Field> Neg for SparseVector<F> {
    type Output = SparseVector<F>;

    fn neg(self) -> Self::Output {
        SparseVector {
            size: self.size,
            contents: self
                .contents
                .into_iter()
                .map(|(i, f)| (i, f.neg()))
                .collect(),
            zero: self.zero,
        }
    }
}

impl<F: Field> Sub for SparseVector<F> {
    type Output = SparseVector<F>;

    fn sub(self, other: Self) -> Self::Output {
        self.add_sparse(&-other)
    }
}
