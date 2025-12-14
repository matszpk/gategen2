// gate.rs - gate module

use std::collections::*;
use std::fmt::Debug;
use std::ops::{Neg, Not};

use generic_array::*;

/// A variable literal. It holds variable number if it is not negated,
/// or negated variable number if it is negated.
///
/// Zero value is not allowed.
/// It can be a signed integer type: from `i8` to `i64` or `isize`.
pub trait VarLit:
    Neg + PartialEq + Eq + Ord + Copy + TryInto<isize> + TryInto<usize> + TryFrom<usize> + Debug
where
    <Self as VarLit>::Unsigned: Clone + Copy,
{
    type Unsigned;
    /// Converts variable literal to isize.
    #[inline]
    fn to(self) -> isize
    where
        <Self as TryInto<isize>>::Error: Debug,
    {
        self.try_into().expect("VarLit is too big")
    }
    /// Converts variable literal to usize.
    #[inline]
    fn to_usize(self) -> usize
    where
        <Self as TryInto<usize>>::Error: Debug,
    {
        self.try_into().expect("VarLit out of range")
    }
    #[inline]
    fn from_usize(v: usize) -> Self
    where
        <Self as TryFrom<usize>>::Error: Debug,
    {
        v.try_into().expect("Usize out of range")
    }
    /// Returns true if literal is empty (zero value - not allowed).
    fn is_empty(self) -> bool;
    /// Returns empty literal - zero.
    fn empty() -> Self;
    /// Returns first variable - 1.
    fn first_value() -> Self;
    /// Returns some positive value (absolute value) if no overflow encountered.
    fn positive(self) -> Option<Self>;
    /// Returns some positive value (absolute value) if no overflow encountered.
    fn is_positive(self) -> bool;
    /// Returns next value.
    fn next_value(self) -> Option<Self>;
    /// Write self value to vector of bytes.
    fn write_to_vec(self, vec: &mut Vec<u8>);
}

macro_rules! impl_varlit {
    ($Ty:ident, $Uty:ident) => {
        /// Implementation for an integer type.
        impl VarLit for $Ty {
            type Unsigned = $Uty;

            #[inline]
            fn is_empty(self) -> bool {
                self == 0
            }
            #[inline]
            fn empty() -> Self {
                0
            }
            #[inline]
            fn first_value() -> Self {
                1
            }
            #[inline]
            fn positive(self) -> Option<Self> {
                self.checked_abs()
            }

            #[inline]
            fn is_positive(self) -> bool {
                self > 0
            }

            #[inline]
            fn next_value(self) -> Option<Self> {
                self.checked_add(1)
            }

            #[inline]
            fn write_to_vec(self, vec: &mut Vec<u8>) {
                itoap::write_to_vec(vec, self);
            }
        }
    };
}

impl_varlit!(i8, u8);
impl_varlit!(i16, u16);
impl_varlit!(i32, u32);
impl_varlit!(i64, u64);
impl_varlit!(isize, usize);

/// A literal. It holds variable literal or value literal (false or true).
///
/// It can be used to construct clause from either variables or constants.
/// T type must be VarLit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Literal<T: VarLit> {
    /// It holds variable literal.
    VarLit(T),
    /// It holds boolean value.
    Value(bool),
}

impl<T: VarLit> Literal<T> {
    /// Returns true if self is variable literal.
    pub fn is_varlit(self) -> bool {
        matches!(self, Literal::VarLit(_))
    }

    /// Returns true if self is value.
    pub fn is_value(self) -> bool {
        matches!(self, Literal::Value(_))
    }

    /// Returns value if it is.
    pub fn value(self) -> Option<bool> {
        if let Literal::Value(t) = self {
            Some(t)
        } else {
            None
        }
    }

    /// Returns variable literal if it is.
    pub fn varlit(self) -> Option<T> {
        if let Literal::VarLit(t) = self {
            Some(t)
        } else {
            None
        }
    }
}

impl<T: VarLit + Neg<Output = T>> Not for Literal<T> {
    type Output = Literal<T>;

    fn not(self) -> Self::Output {
        match self {
            Literal::Value(t) => Literal::Value(!t),
            Literal::VarLit(t) => Literal::VarLit(-t),
        }
    }
}

/// Converts boolean value to Literal.
impl<T: VarLit> From<bool> for Literal<T> {
    fn from(t: bool) -> Self {
        Literal::Value(t)
    }
}

/// Converts variable literal to Literal.
impl<T: VarLit> From<T> for Literal<T> {
    fn from(t: T) -> Self {
        Literal::VarLit(t)
    }
}

/// Basic clause trait. It contains variable literals.
///
/// This clause is a disjuction of literals. Type T must be VarLit.
/// An empty clause is always false - formula contains that clause going
/// to be unsatisfied.
/// It can be a slice, an array, a vector or other collection like BTreeMap.
pub trait Clause<T>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    /// Mainly to internal use. Returns length of clause - number of literals.
    fn clause_len(&self) -> usize;
    /// Mainly to internal use. Returns true only if this function returns true for
    /// all items.
    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool;
    /// Mainly to internal use. It performs function for each item.
    fn clause_for_each<F: FnMut(&T)>(&self, f: F);

    /// Checks clause whether it have only allowed variable literals and variables
    /// used in this clause doesn't have number greater than var_num.
    fn check_clause(&self, var_num: usize) -> bool {
        self.clause_all(|x| {
            *x != T::empty()
                && if let Some(p) = x.positive() {
                    p.to_usize() <= var_num
                } else {
                    false
                }
        })
    }
}

macro_rules! impl_clause {
    ($Ty:ty) => {
        /// An implementation for this type.
        impl<T> Clause<T> for $Ty
        where
            T: VarLit + Neg<Output = T>,
            <T as TryInto<usize>>::Error: Debug,
        {
            fn clause_len(&self) -> usize {
                self.len()
            }

            fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
                self.iter().all(f)
            }

            fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
                self.iter().for_each(f);
            }
        }
    };
}

/// An implementation for a reference of slice.
impl<'a, T> Clause<T> for &'a [T]
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        self.len()
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}

impl_clause!([T]);
impl_clause!(Vec<T>);
impl_clause!(VecDeque<T>);
impl_clause!(BTreeSet<T>);
impl_clause!(BinaryHeap<T>);
impl_clause!(HashSet<T>);
impl_clause!(LinkedList<T>);

/// An implementation for an array.
impl<T, const N: usize> Clause<T> for [T; N]
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        N
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}

/// An implementation for a generic-array.
impl<T, N: ArrayLength> Clause<T> for GenericArray<T, N>
where
    T: VarLit + Neg<Output = T>,
    <T as TryInto<usize>>::Error: Debug,
{
    fn clause_len(&self) -> usize {
        N::USIZE
    }

    fn clause_all<F: FnMut(&T) -> bool>(&self, f: F) -> bool {
        self.iter().all(f)
    }

    fn clause_for_each<F: FnMut(&T)>(&self, f: F) {
        self.iter().for_each(f);
    }
}
