use crate::Variable;
use p1::Field;

/// Represents a single row of an R1CS matrix (i.e. a linear combination of variables) Implements
/// sensible arithmetic operations e.g. lc + variable, lc + (coeff, variable), lc + lc, etc, ditto
/// for subtraction and negation Lc's can be constructed from single field elements, (field,
/// variable) pairs or singular variables via Lc::from or via Lc::zero
#[derive(Clone, Eq, PartialEq, Default, Debug, Hash)]
pub struct Lc<F>(Vec<(F, Variable)>);

impl<F> IntoIterator for Lc<F> {
    type Item = (F, Variable);
    type IntoIter = std::vec::IntoIter<(F, Variable)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

use std::ops::{Add, Mul, Sub};

impl<F: Field> Mul<F> for Lc<F> {
    type Output = Lc<F>;

    fn mul(self, scalar: F) -> Self::Output {
        Lc(self
            .0
            .into_iter()
            .map(|(coeff, var)| (coeff * scalar, var))
            .collect())
    }
}

impl<F: Field> Add<(F, Variable)> for Lc<F> {
    type Output = Lc<F>;

    fn add(mut self, cv: (F, Variable)) -> Lc<F> {
        self.0.push(cv);
        self
    }
}

impl<F: Field> Sub<(F, Variable)> for Lc<F> {
    type Output = Lc<F>;

    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, (coeff, var): (F, Variable)) -> Lc<F> {
        self + (coeff.neg(), var)
    }
}

impl<F: Field> Add<Variable> for Lc<F> {
    type Output = Lc<F>;

    fn add(self, other: Variable) -> Lc<F> {
        self + (F::one(), other)
    }
}

impl<F: Field> Sub<Variable> for Lc<F> {
    type Output = Lc<F>;

    fn sub(self, other: Variable) -> Lc<F> {
        self - (F::one(), other)
    }
}

impl<F: Field> Add<F> for Lc<F> {
    type Output = Lc<F>;

    fn add(self, other: F) -> Lc<F> {
        self + (other, Variable::one())
    }
}

impl<F: Field> Sub<F> for Lc<F> {
    type Output = Lc<F>;

    fn sub(self, other: F) -> Lc<F> {
        self - (other, Variable::one())
    }
}

impl<F: Field> Add for Lc<F> {
    type Output = Lc<F>;

    fn add(mut self, other: Lc<F>) -> Lc<F> {
        self.0.extend(other.0);
        self
    }
}

impl<F: Field> Sub for Lc<F> {
    type Output = Lc<F>;

    fn sub(self, other: Lc<F>) -> Lc<F> {
        other
            .into_iter()
            .fold(self, |acc, (coeff, var)| acc - (coeff, var))
    }
}

impl<F: Field> From<(F, Variable)> for Lc<F> {
    fn from(cv: (F, Variable)) -> Self {
        Lc(vec![cv])
    }
}

impl<F: Field> From<Variable> for Lc<F> {
    fn from(cv: Variable) -> Self {
        Lc(vec![(F::one(), cv)])
    }
}
impl<F: Field> From<F> for Lc<F> {
    fn from(f: F) -> Self {
        Lc(vec![(f, Variable::one())])
    }
}

impl<F: Field> Lc<F> {
    pub fn zero() -> Self {
        Lc(Vec::new())
    }
}
