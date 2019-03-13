//! Abstract representation of a multi-dimensional resource counter.
//!
//! Many applications of resource counters need to manage multiple different individual resources
//! at the same time. Instead of replicating the entire resource-counter infrastructure for each
//! resource, the counter is abstracted instead to allow for multi-dimensional resource counters.
//!
//! The `[Counter]` trait represents a multi-dimensional resource counter, which can be indexed to
//! access its individual slots. Each slot is represented by the `[Scalar]` trait, which describes
//! the numerical operations that are allowed on this value.
//!
//! Due to restrictions in the trait-system of rust, all individual slots on a counter must share
//! the same type implementing `[Scalar]`.

/// Scalar resource counter
///
/// This trait is used to denote scalar values that count the share of a single resource. It
/// usually is backed by a simple integer value, but that is not necessarily required. This trait
/// makes heavy use of the traits defined by the `num` crate to abstract over integer operations.
pub trait Scalar where
    Self: Clone +
          Ord +
          Sized +
          num::Zero +
          for<'a> num::traits::NumAssignOps<&'a Self>,
{
}

/// Multi-dimensional resource counter
///
/// This trait represents a set of resource counters that can be indexed to access the individual
/// scalar counters. In its simplest form it can be thought of as an array of scalar counters, but
/// more complex setups are possible.
///
/// A resource counter needs to select the index used to access the individual slots, the scalar
/// type that each slot uses, as well as a function to replicate itself.
pub trait Counter {
    type Index: Clone + Ord;
    type Scalar: Scalar;

    /// Create new counter from a template.
    ///
    /// This takes an existing counter as a template and creates a new counter that has the same
    /// dimensions. The new counter is initialized to zero. That is, the template is only used to
    /// make sure both counters have the same amount of slots.
    fn from_template(template: &Self) -> Self;

    /// Dereference an individual slot on the counter.
    ///
    /// This function returns a mutable reference to the slot with index `[index]`. It is similar
    /// to an implementation of `[std::ops::IndexMut]`, but takes a reference as index.
    fn slot(&mut self, index: &Self::Index) -> &mut Self::Scalar;

    /// Check whether the counter is empty.
    ///
    /// This checks all slots of the counter whether they are empty. If all are empty (that is,
    /// they are `0`, as in `num::Zero::is_zero()`), this will return `true`, otherwise `false` is
    /// returned.
    fn empty(&self) -> bool;
}

impl<T> Scalar for T where
    T: Clone +
       Ord +
       Sized +
       num::Zero +
       for<'a> num::traits::NumAssignOps<&'a Self>,
{
}

// An implementation over a one-dimensional counter.
impl<S> Counter for [S; 1] where
    S: Scalar,
{
    type Index = ();
    type Scalar = S;

    fn from_template(_template: &Self) -> Self {
        [num::Zero::zero()]
    }

    fn slot(&mut self, _index: &Self::Index) -> &mut Self::Scalar {
        &mut self[0]
    }

    fn empty(&self) -> bool {
        num::Zero::is_zero(&self[0])
    }
}

// XXX: We want a static implementation for any static array like:
//
//          impl<S, n> Counter for [S; n]
//
//      However, that is currently not possible, since there is no generic over constants. We
//      could provide implementations for everything up to a static size limit (`std` does that),
//      though we didn't really need it so far. We can add it on request.

// An implementation over dynamically sized arrays.
impl<S> Counter for Box<[S]> where
    S: Scalar,
{
    type Index = usize;
    type Scalar = S;

    fn from_template(template: &Self) -> Self {
        let n = template.len();
        let mut v = Vec::with_capacity(n);

        v.resize_with(n, num::Zero::zero);

        v.into_boxed_slice()
    }

    fn slot(&mut self, index: &Self::Index) -> &mut Self::Scalar {
        &mut self[*index]
    }

    fn empty(&self) -> bool {
        for slot in &**self {
            if !num::Zero::is_zero(slot) {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Test scalar counter implementation.
    //
    // This runs basic tests against the standard implementation of `[Counter]` for scalar values
    // (i.e., one-dimensional arrays with no index).
    #[test]
    fn test_scalar_counter() {
        let mut x = [1024];

        assert_eq!{*x.slot(&()), 1024};
        assert_eq!{Counter::from_template(&x), [0]};

        assert!{!x.empty()};
        *x.slot(&()) = 0;
        assert!{x.empty()};
    }

    // Test boxed-slice counter implementation.
    //
    // This runs basic tests against the standard implementation of `[Counter]` for dynamically
    // sized boxed slices of scalars.
    #[test]
    fn test_boxed_slice() {
        let mut x: Box<[usize]> = Box::new([0, 1, 2, 3]);
        let zero: Box<[usize]> = Box::new([0, 0, 0, 0]);

        for i in 0..4 {
            assert_eq!{*x.slot(&i), i};
        }

        assert_eq!{&Counter::from_template(&x), &zero};

        assert!{!x.empty()};
        assert!{zero.empty()};
    }
}
