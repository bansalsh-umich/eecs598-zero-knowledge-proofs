use p1::{
    Field,
    poly::{Multilinear, Univariate},
};
use std::fmt::{self, Debug};

/// Represents a combination of multilinear extensions: g(x) = C(f_1(x), f_2(x), ..., f_k(x)).
///
/// In sumcheck, we often need to sum a function that combines multiple MLEs. For example,
/// to prove that matrix-vector product Az = y, we sum over the hypercube:
///     sum_x A(r, x) * z(x)
/// Here g combines two MLEs (A and z) via multiplication.
///
/// The `combiner` function specifies how to combine evaluations of the individual MLEs.
/// The `deg` field is the total degree of g, which determines how many points are needed
/// to interpolate the round polynomial in sumcheck.
#[derive(Clone)]
pub struct CombinedMLE<F> {
    exts: Vec<Multilinear<F>>,
    combiner: fn(&[F]) -> F,
    deg: usize,
}

/// Iterates over pairs of hypercube points that differ only in bit i.
///
/// For an n-variable hypercube, yields 2^(n-1) pairs (p0, p1) where p0 has bit i = 0
/// and p1 has bit i = 1, but all other bits are identical. This is used in to_univariate
/// to efficiently compute the round polynomial by iterating over all "free" variables
/// while treating variable i as the one being reduced.
fn boolean_hypercube_fixed(n: usize, i: usize) -> impl Iterator<Item = (usize, usize)> {
    assert!(i < n);
    let fixed_mask = 1 << i;
    (0..(1 << (n - 1))).map(move |x| {
        let low = x & (fixed_mask - 1);
        let high = x >> i;
        let base = (high << (i + 1)) | low;
        (base, base | fixed_mask)
    })
}

impl<F: Debug> Debug for CombinedMLE<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CombinedMLE")
            .field("exts", &self.exts)
            .finish()
    }
}

impl<F: Field> PartialEq for CombinedMLE<F> {
    fn eq(&self, other: &Self) -> bool {
        self.exts == other.exts
    }
}

impl<F: Field> Eq for CombinedMLE<F> {}

impl<F> CombinedMLE<F>
where
    F: Field,
{
    /// Creates a new CombinedMLE.
    ///
    /// - `degree`: the total degree of the combining function (e.g., 2 for a product of two MLEs)
    /// - `combiner`: a function that takes a slice of field elements (one per MLE) and returns
    ///   their combined value
    /// - `extensions`: the list of MLEs to combine; all must have the same number of variables
    pub fn new(degree: usize, combiner: fn(&[F]) -> F, extensions: Vec<Multilinear<F>>) -> Self {
        if !extensions.is_empty() {
            let l = extensions[0].evals.len();
            assert!(extensions.iter().skip(1).all(|e| e.evals.len() == l))
        }

        Self {
            exts: extensions,
            combiner,
            deg: degree,
        }
    }
    /// Returns the total degree of the combined polynomial.
    pub const fn degree(&self) -> usize {
        self.deg
    }

    /// Returns the number of variables in the combined MLE.
    pub fn num_vars(&self) -> usize {
        self.exts
            .first()
            .map(|e| e.evals.len().ilog2() as usize)
            .unwrap_or(0)
    }

    /// Partially evaluates all MLEs at the given point, reducing the number of variables.
    ///
    /// If the original MLEs have n variables and partial_point has k elements,
    /// the result has n - k variables.
    pub fn partial_eval(&self, partial_point: &[F]) -> Self {
        Self {
            exts: self
                .exts
                .iter()
                .map(|x| x.partial_eval(partial_point))
                .collect(),
            combiner: self.combiner,
            deg: self.deg,
        }
    }

    /// Evaluates the combined MLE at a point by evaluating each MLE and applying the combiner.
    pub fn evaluate(&self, point: &[F]) -> F {
        let points = self
            .exts
            .iter()
            .map(|ext| ext.evaluate(point))
            .collect::<Vec<_>>();
        (self.combiner)(&points)
    }

    /// Computes the round polynomial for sumcheck by fixing one variable and summing over the rest.
    ///
    /// Given a combined MLE g(x_0, ..., x_{n-1}), this computes the univariate polynomial:
    ///     p(X) = sum_{b in {0,1}^{n-1}} g(x_0, ..., x_{i-1}, X, x_{i+1}, ..., x_{n-1})
    /// where the sum is over all boolean assignments to variables other than x_i.
    ///
    /// The resulting polynomial has degree equal to self.degree(), so we evaluate at
    /// deg + 1 points and interpolate.
    pub fn to_univariate(&self, variable_index: usize) -> Univariate<F> {
        let n = self.num_vars();

        let sums = boolean_hypercube_fixed(n, variable_index).fold(
            vec![F::zero(); self.deg + 1],
            |sums, (i0, i1)| {
                sums.into_iter()
                    .enumerate()
                    .map(|(r, sum)| {
                        let r = F::from(r as u64);
                        let evals_at_r: Vec<F> = self
                            .exts
                            .iter()
                            .map(|ext| ext[i0] + r * (ext[i1] - ext[i0]))
                            .collect();
                        sum + (self.combiner)(&evals_at_r)
                    })
                    .collect()
            },
        );

        let points: Vec<_> = sums
            .into_iter()
            .enumerate()
            .map(|(r, sum)| (F::from(r as u64), sum))
            .collect();

        Univariate::interpolate(&points)
    }

    /// Computes the sum of the combined MLE over the boolean hypercube.
    ///
    /// This is the claimed value that the sumcheck protocol proves:
    ///     sum_{x in {0,1}^n} g(x)
    pub fn sum_over_hypercube(&self) -> F {
        let n = self.num_vars();
        (0..(1usize << n))
            .map(|i| {
                let evals: Vec<F> = self.exts.iter().map(|ext| ext[i]).collect();
                (self.combiner)(&evals)
            })
            .sum()
    }
}

/// Converts a single MLE into a CombinedMLE with the identity combiner.
impl<F: Field> From<Multilinear<F>> for CombinedMLE<F> {
    fn from(value: Multilinear<F>) -> Self {
        CombinedMLE::new(1, |eval| eval[0], vec![value])
    }
}
