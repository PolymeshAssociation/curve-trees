//! Definition of linear combinations.

#[cfg(not(feature = "std"))]
use alloc::{vec, vec::Vec};

use ark_ff::Field;
use core::iter::FromIterator;
use core::marker::PhantomData;
use core::ops::{Add, Mul, Neg, Sub};
use core::cmp::Ordering;
use ark_std::collections::BTreeMap;

/// Represents a variable in a constraint system.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Variable<F: Field> {
    /// A Pedersen vector commitment. The first usize corresponds to the index of the Pedersen commitment and
    /// the second corresponds to index of this variable in this committed vector
    VectorCommit(usize, usize),
    /// Represents an external input specified by a commitment.
    Committed(usize),
    /// Represents the left input of a multiplication gate.
    MultiplierLeft(usize),
    /// Represents the right input of a multiplication gate.
    MultiplierRight(usize),
    /// Represents the output of a multiplication gate.
    MultiplierOutput(usize),
    /// Represents the constant 1.
    One(PhantomData<F>),
}

impl<F: Field> PartialOrd for Variable<F> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<F: Field> Ord for Variable<F> {
    fn cmp(&self, other: &Self) -> Ordering {
        use Variable::*;
        fn variant_index<F: Field>(v: &Variable<F>) -> u8 {
            match v {
                VectorCommit(_, _) => 0,
                Committed(_) => 1,
                MultiplierLeft(_) => 2,
                MultiplierRight(_) => 3,
                MultiplierOutput(_) => 4,
                One(_) => 5,
            }
        }
        let self_idx = variant_index(self);
        let other_idx = variant_index(other);
        match self_idx.cmp(&other_idx) {
            Ordering::Equal => match (self, other) {
                (VectorCommit(a1, a2), VectorCommit(b1, b2)) => (a1, a2).cmp(&(b1, b2)),
                (Committed(a), Committed(b)) => a.cmp(b),
                (MultiplierLeft(a), MultiplierLeft(b)) => a.cmp(b),
                (MultiplierRight(a), MultiplierRight(b)) => a.cmp(b),
                (MultiplierOutput(a), MultiplierOutput(b)) => a.cmp(b),
                (One(_), One(_)) => Ordering::Equal,
                _ => Ordering::Equal, // Should not happen
            },
            ord => ord,
        }
    }
}

impl<F: Field> From<Variable<F>> for LinearCombination<F> {
    fn from(v: Variable<F>) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(v, F::one())],
        }
    }
}

// impl<F: Field, S: Into<F> + Marker> From<S> for LinearCombination<F> {
//     fn from(s: S) -> LinearCombination<F> {
//         LinearCombination {
//             terms: vec![(Variable::One(), s.into())],
//         }
//     }
// }

impl<F: Field> From<F> for LinearCombination<F> {
    fn from(c: F) -> LinearCombination<F> {
        LinearCombination {
            terms: vec![(Variable::One(PhantomData), c)],
        }
    }
}

pub fn constant<F: Field, I: Into<F>>(c: I) -> LinearCombination<F> {
    LinearCombination {
        terms: vec![(Variable::One(PhantomData), c.into())],
    }
}

// Arithmetic on variables produces linear combinations

impl<F: Field> Neg for Variable<F> {
    type Output = LinearCombination<F>;

    fn neg(self) -> Self::Output {
        -LinearCombination::from(self)
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Add<L> for Variable<F> {
    type Output = LinearCombination<F>;

    fn add(self, other: L) -> Self::Output {
        LinearCombination::from(self) + other.into()
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Sub<L> for Variable<F> {
    type Output = LinearCombination<F>;

    fn sub(self, other: L) -> Self::Output {
        LinearCombination::from(self) - other.into()
    }
}

impl<F: Field, S: Into<F>> Mul<S> for Variable<F> {
    type Output = LinearCombination<F>;

    fn mul(self, other: S) -> Self::Output {
        LinearCombination {
            terms: vec![(self, other.into())],
        }
    }
}

// Arithmetic on scalars with variables produces linear combinations

// pub trait Marker {}
// impl<F: Field> Marker for F {}

// impl<F: Field + Marker> Add<Variable<F>> for F {
//     type Output = LinearCombination<F>;

//     fn add(self, other: Variable<F>) -> Self::Output {
//         LinearCombination {
//             terms: vec![(Variable::One(), self), (other, F::one())],
//         }
//     }
// }

// impl Sub<Variable> for Field {
//     type Output = LinearCombination<Field>;

//     fn sub(self, other: Variable) -> Self::Output {
//         LinearCombination {
//             terms: vec![(Variable::One(), self), (other, -F::one())],
//         }
//     }
// }

// impl Mul<Variable> for Field {
//     type Output = LinearCombination<Field>;

//     fn mul(self, other: Variable) -> Self::Output {
//         LinearCombination {
//             terms: vec![(other, self)],
//         }
//     }
// }

/// Represents a linear combination of
/// [`Variables`](::r1cs::Variable).  Each term is represented by a
/// `(Variable, Scalar)` pair.
#[derive(Clone, Debug, PartialEq)]
pub struct LinearCombination<F: Field> {
    pub(super) terms: Vec<(Variable<F>, F)>,
}

impl<F: Field> Default for LinearCombination<F> {
    fn default() -> Self {
        LinearCombination { terms: Vec::new() }
    }
}

impl<F: Field> FromIterator<(Variable<F>, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (Variable<F>, F)>,
    {
        LinearCombination {
            terms: iter.into_iter().collect(),
        }
    }
}

impl<'a, F: Field> FromIterator<&'a (Variable<F>, F)> for LinearCombination<F> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = &'a (Variable<F>, F)>,
    {
        LinearCombination {
            terms: iter.into_iter().copied().collect(),
        }
    }
}

// Arithmetic on linear combinations

impl<F: Field, L: Into<LinearCombination<F>>> Add<L> for LinearCombination<F> {
    type Output = Self;

    fn add(mut self, rhs: L) -> Self::Output {
        self.terms.extend(rhs.into().terms.iter().copied());
        LinearCombination { terms: self.terms }
    }
}

impl<F: Field, L: Into<LinearCombination<F>>> Sub<L> for LinearCombination<F> {
    type Output = Self;

    fn sub(mut self, rhs: L) -> Self::Output {
        self.terms.extend(
            rhs.into()
                .terms
                .iter()
                .map(|(var, coeff)| (*var, -(*coeff))),
        );
        LinearCombination { terms: self.terms }
    }
}

// impl<F: Field> Mul<LinearCombination<F>> for F {
//     type Output = LinearCombination<F>;

//     fn mul(self, other: LinearCombination<F>) -> Self::Output {
//         let out_terms = other
//             .terms
//             .into_iter()
//             .map(|(var, scalar)| (var, scalar * self))
//             .collect();
//         LinearCombination { terms: out_terms }
//     }
// }

impl<F: Field> LinearCombination<F> {
    pub fn scalar_mul(self, scalar: F) -> LinearCombination<F> {
        let out_terms = self
            .terms
            .into_iter()
            .map(|(var, entry)| (var, entry * scalar))
            .collect();
        LinearCombination { terms: out_terms }
    }

    pub fn inner(self) -> Vec<(Variable<F>, F)> {
        self.terms
    }

    /// Simplify linear combination by taking Variables common across terms and adding their corresponding scalars.
    /// Useful when linear combinations become large. Takes ownership of linear combination as this function is useful
    /// when memory is limited and the obvious action after this function call will be to free the memory held by the passed linear combination
    pub fn simplify(self) -> LinearCombination<F> {
        let mut vars: BTreeMap<Variable<F>, F> = BTreeMap::new();
        let terms = self.inner();
        for (var, val) in terms {
            *vars.entry(var).or_insert(F::zero()) += val;
        }

        let mut new_lc_terms = vec![];
        for (var, val) in vars {
            new_lc_terms.push((var, val));
        }
        new_lc_terms.iter().collect()
    }
}

impl<F: Field> Neg for LinearCombination<F> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for (_, s) in self.terms.iter_mut() {
            *s = -*s
        }
        self
    }
}

impl<F: Field, S: Into<F>> Mul<S> for LinearCombination<F> {
    type Output = Self;

    fn mul(mut self, other: S) -> Self::Output {
        let other = other.into();
        for (_, s) in self.terms.iter_mut() {
            *s *= other
        }
        self
    }
}

/// For a value that is already committed in the circuit.
#[derive(Copy, Clone, Debug)]
pub struct AllocatedScalar<F: Field> {
    /// Variable for the value
    pub variable: Variable<F>,
    /// The value itself
    pub assignment: Option<F>
}

