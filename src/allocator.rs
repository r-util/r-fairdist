//! Allocation Calculations
//!
//! This module implements the allocation calculations which the fair distribution algorithm is
//! based on. It defines a new trait `[Allocator]`, which abstracts the exact details how to
//! divide a resource set amongst different requests. Furthermore, this module comes with a set of
//! pre-defines allocator implementations, each with different properties and guarantees.

// Calculate ceiled base-2 logarithm.
//
// This is an internal helper which calculates the base-2 logarithm, rounding up in case of
// missing precision.
//
// If `v` is 0, or negative, the function will produce a result, but does not give guarantees on
// its value (currently, it will produce the maximum logarithm representable in `T`).
fn log2_ceil<T>(v: &T) -> T where
    T: crate::counter::Scalar +
       num::FromPrimitive +
       num::PrimInt,
{
    // XXX: There is currently no way to retrieve the bit-length of a `PrimInt`, even though it
    //      is a well-defined concept, given that it can be calculated through other means:
    //
    //          * `zero().count_zeroes()`
    //          * `x.count_zeros() + x.count_ones()`
    //          * ...
    //
    //      There is an upstream bug-report about this. It might be as simple as using `size_of()`
    //      but that needs to be explicitly documented. Until then, we use a version that can be
    //      optimized by the compiler well enough.
    let length: u32 = <T as num::Zero>::zero().count_zeros();

    // This calculates the ceiled logarithm. What we do is count the leading zeros of the value in
    // question and then substract it from its bit-length. By subtracting one from the value first
    // we make sure the value is ceiled.
    //
    // Hint: To calculate the floored value, you would do the subtraction of 1 from the final
    //       value, rather than from the source value: `length - v.leading_zeros() - 1`
    //
    // XXX: This should use `usize`, but upstream `num` has not fixed that, yet. They intend to
    //      fix it with the next ABI break, whenever that happens.
    let log2: u32 = length - (*v - num::One::one()).leading_zeros();

    // Convert the value back into the source type. Since the source type must be an integer type,
    // it must have a representation for all integers between its original and 0. Hence, this
    // cannot fail.
    <T as num::FromPrimitive>::from_u32(log2).unwrap()
}

/// Abstraction to calculate constraints of an allocator
///
/// This trait abstracts over the exact algorithm used to divide a resource set amongst requests.
/// The allocator cannot have state. All member methods are associated functions and never get
/// access to `Self`.
pub trait Allocator<S> where
    S: crate::counter::Scalar,
{
    /// Calculate minimum reserve size given the parameters of an allocation request.
    ///
    /// This takes the three parameters of an allocation request and calculates the minimum
    /// reserve size needed to grant this allocation. It takes the number of users that currently
    /// hold shares (it must include the caller, so `users` cannot be `0`). Furthermore, `share`
    /// contains the amount of resources already allocated to the caller (excluding `amount`)
    /// Lastly, `amount` describes the amount of resources the allocation requests.
    ///
    /// This function returns the minimum size the reserve must have to grant this request. If the
    /// reserve is bigger than, or equal to, this minimum, then the allocation can be safely
    /// granted. The caller should then decrease the reserve, and increase the shares, by
    /// `amount`.
    /// If the minimum reserve cannot be represented in the domain of `S`, this function will
    /// return `None`. This should be treated as an infinitely high minimum, and thus the
    /// allocation should be rejected.
    ///
    /// Implementors must be careful about the constraints of the domain `S` during temporary
    /// computations. This function must **not** return `None`, unless the final result cannot be
    /// represented in `S`. That is, you should not return `None` just because an intermediate
    /// value exceeds the domain of `S`. Instead, you must adjust your calculations to never
    /// exceed the domain, or extend the domain of your intermediates.
    fn minimum_reserve_for(
        users: usize,
        share: &S,
        amount: &S,
    ) -> Option<S>;
}

/// Allocator with exponential guarantees
///
/// This is a predefined allocator that implements `[Allocator]`.
///
/// This allocator grants `1 / 2` of the remaining resources to every allocation. This
/// guarantees every user gets a share proportional to `O(2^n)` of the total.
pub struct Exponential {
}

impl<S> Allocator<S> for Exponential where
    S: crate::counter::Scalar +
       num::CheckedAdd +
       num::CheckedMul +
       num::CheckedSub +
       num::FromPrimitive,
{
    fn minimum_reserve_for(
        _users: usize,
        share: &S,
        amount: &S,
    ) -> Option<S> {
        if let Some(n) = num::FromPrimitive::from_usize(2) {
            if let Some(limit) = share.checked_add(&amount) {
                if let Some(limit) = limit.checked_mul(&n) {
                    return limit.checked_sub(&share);
                }
            }
        }

        None
    }
}

/// Allocator with polynomial guarantees
///
/// This is a predefined allocator that implements `[Allocator]`.
///
/// This allocator grants `1 / (n+1)` of the remaining resources to every allocation. This
/// guarantees every user gets a share proportional to `O(n^2)` of the total.
pub struct Polynomial {
}

impl<S> Allocator<S> for Polynomial where
    S: crate::counter::Scalar +
       num::CheckedAdd +
       num::CheckedMul +
       num::CheckedSub +
       num::FromPrimitive,
{
    fn minimum_reserve_for(
        users: usize,
        share: &S,
        amount: &S,
    ) -> Option<S> {
        if let Some(n) = num::FromPrimitive::from_usize(users + 1) {
            if let Some(limit) = share.checked_add(amount) {
                if let Some(limit) = limit.checked_mul(&n) {
                    return limit.checked_sub(share);
                }
            }
        }

        None
    }
}


/// Allocator with quasilinear guarantees
///
/// This is a predefined allocator that implements `[Allocator]`.
///
/// This allocator grants `1 / ((n+1) * log_2(n+1) + (n+1))` of the remaining resources to every
/// allocation. This guarantees every user gets a share proportional to `O(n log(n)^2)` of the
/// total.
pub struct Quasilinear {
}

impl<S> Allocator<S> for Quasilinear where
    S: crate::counter::Scalar +
       num::CheckedAdd +
       num::CheckedMul +
       num::CheckedSub +
       num::FromPrimitive +
       num::PrimInt,
{
    fn minimum_reserve_for(
        users: usize,
        share: &S,
        amount: &S,
    ) -> Option<S> {
        if let Some(users_plus_one) = num::FromPrimitive::from_usize(users + 1) {
            if let Some(n) = log2_ceil::<S>(&users_plus_one).checked_mul(&users_plus_one) {
                if let Some(n) = n.checked_add(&users_plus_one) {
                    if let Some(limit) = share.checked_add(amount) {
                        if let Some(limit) = limit.checked_mul(&n) {
                            return limit.checked_sub(share);
                        }
                    }
                }
            }
        }

        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // The quasilinear allocators need base-2 logarithms on integers. We have a fast
    // implementation based on the `clz` (count-leading-zeroes) CPU features. This test simply
    // verifies it works correctly.
    #[test]
    fn verify_log() {
        fn verify_log2_ceil<T>() where
            T: crate::counter::Scalar +
               num::FromPrimitive +
               num::PrimInt +
               num::ToPrimitive,
        {
            let tests: &[(u64, u64)] = &[
                ( 1, 0), ( 2, 1), ( 3, 2), ( 4, 2),
                ( 5, 3), ( 6, 3), ( 7, 3), ( 8, 3),
                ( 9, 4), (10, 4), (11, 4), (12, 4),
                (13, 4), (14, 4), (15, 4), (16, 4),

                ( 127,  7), ( 128,  7), ( 129,  8),
                (1023, 10), (1024, 10), (1025, 11),

                (std::u8::MAX as u64 - 1, 8),
                (std::u8::MAX as u64 + 0, 8),
                (std::u8::MAX as u64 + 1, 8),
                (std::u8::MAX as u64 + 2, 9),

                (std::u16::MAX as u64 - 1, 16),
                (std::u16::MAX as u64 + 0, 16),
                (std::u16::MAX as u64 + 1, 16),
                (std::u16::MAX as u64 + 2, 17),

                (std::u32::MAX as u64 - 1, 32),
                (std::u32::MAX as u64 + 0, 32),
                (std::u32::MAX as u64 + 1, 32),
                (std::u32::MAX as u64 + 2, 33),

                (std::u64::MAX as u64 - 1, 64),
                (std::u64::MAX as u64 + 0, 64),
            ];

            for &(input, output) in tests {
                if let Some(max) = <T as num::ToPrimitive>::to_u64(&<T as num::Bounded>::max_value()) {
                    if input <= max {
                        let p_input = <T as num::FromPrimitive>::from_u64(input).unwrap();
                        let p_output = <T as num::FromPrimitive>::from_u64(output).unwrap();

                        assert!{log2_ceil(&p_input) == p_output};
                    }
                }
            }
        }

        verify_log2_ceil::<u8>();
        verify_log2_ceil::<u16>();
        verify_log2_ceil::<u32>();
        verify_log2_ceil::<u64>();
        verify_log2_ceil::<usize>();
    }

    // This tests the behavior of the exponential allocator. We simulate a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 512.
    //
    // The allocator we use grants everyone 1/2 of the remaining resources. It does *NOT* depend
    // on the number of active users, hence it is ignored in these tests.
    #[test]
    fn exponential_allocation() {
        let op = <Exponential as Allocator<usize>>::minimum_reserve_for;

        // As first step verify nothing bigger than 512 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        assert!{op(1, &0, &513).unwrap() > 1024};
        assert!{op(1, &0, &1024).unwrap() > 1024};
        assert!{op(1, &0, &std::usize::MAX).is_none()};

        // Now try a full allocation of 512. This is the biggest allocation possible on our
        // simulated pool of 1024.
        assert_eq!{op(1, &0, &512).unwrap(), 1024};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{op(1, &512, &1).unwrap() > 512};
        assert!{op(1, &512, &512).unwrap() > 512};
        assert!{op(1, &512, &1024).unwrap() > 512};
        assert!{op(1, &512, &std::usize::MAX).is_none()};

        // Now switch to the next virtual share and try again. This time the maximum is 256 (half
        // of the remaining 512). We perform the allocation in two steps 128 each. We then verify
        // that this saturates the allocation.
        assert!{op(2, &0, &257).unwrap() > 512};
        assert!{op(2, &0, &512).unwrap() > 512};
        assert!{op(2, &0, &1024).unwrap() > 512};
        assert!{op(2, &0, &std::usize::MAX).is_none()};

        assert!{op(2, &0, &128).unwrap() <= 512};
        assert_eq!{op(2, &128, &128).unwrap(), 384};

        assert!{op(2, &256, &1).unwrap() > 256};
    }

    // This tests the behavior of the polynomial allocator. We simulate a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 512.
    //
    // The allocator we use grants everyone an n-plus-1'th of the remaining resources. Hence, we
    // need to update @n according to the current number of peers.
    #[test]
    fn polynomial_allocation() {
        let op = <Polynomial as Allocator<usize>>::minimum_reserve_for;

        // As first step verify nothing bigger than 512 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        assert!{op(1, &0, &513).unwrap() > 1024};
        assert!{op(1, &0, &1024).unwrap() > 1024};
        assert!{op(1, &0, &std::usize::MAX).is_none()};

        // Now try a full allocation of 512. This is the biggest allocation possible on our
        // simulated pool of 1024.
        assert_eq!{op(1, &0, &512).unwrap(), 1024};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{op(1, &512, &1).unwrap() > 512};
        assert!{op(1, &512, &512).unwrap() > 512};
        assert!{op(1, &512, &1024).unwrap() > 512};
        assert!{op(1, &512, &std::usize::MAX).is_none()};

        // Now switch to the next share and try again. This time the maximum is a third of 512,
        // which is 170. We split it in two allocations of 85 each, to verify split allocations
        // work the same way.
        assert!{op(2, &0, &171).unwrap() > 512};
        assert!{op(2, &0, &512).unwrap() > 512};
        assert!{op(2, &0, &1024).unwrap() > 512};
        assert!{op(2, &0, &std::usize::MAX).is_none()};

        assert!{op(2, &0, &85).unwrap() <= 512};
        assert_eq!{op(2, &85, &85).unwrap(), 425}; // should be 427, but lacking precision

        assert!{op(2, &170, &1).unwrap() > 342};
    }

    // This tests the behavior of the quasilinear allocator. We simulate a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 256.
    //
    // The allocator we use grants everyone `1 / ((n+1) * log_2(n+1) + (n+1))` of the remaining
    // resources.
    #[test]
    fn quasilinear_allocation() {
        let op = <Quasilinear as Allocator<usize>>::minimum_reserve_for;

        // As first step verify nothing bigger than 256 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        assert!{op(1, &0, &257).unwrap() > 1024};
        assert!{op(1, &0, &1024).unwrap() > 1024};
        assert!{op(1, &0, &std::usize::MAX).is_none()};

        // Now try a full allocation of 256. This is the biggest allocation possible on our
        // simulated pool of 1024.
        assert_eq!{op(1, &0, &256).unwrap(), 1024};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{op(1, &256, &1).unwrap() > 768};
        assert!{op(1, &256, &256).unwrap() > 768};
        assert!{op(1, &256, &1024).unwrap() > 768};
        assert!{op(1, &256, &std::usize::MAX).is_none()};

        // Now switch to the next share and try again. This time the maximum is a nineth of 512,
        // which is 85.3~. We split it in two allocations of 40 and 45, to verify split
        // allocations work the same way.
        assert!{op(2, &0, &86).unwrap() > 768};
        assert!{op(2, &0, &256).unwrap() > 768};
        assert!{op(2, &0, &1024).unwrap() > 768};
        assert!{op(2, &0, &std::usize::MAX).is_none()};

        assert!{op(2, &0, &40).unwrap() <= 768};
        assert_eq!{op(2, &40, &45).unwrap(), 725}; // should be 728, but lacking precision

        assert!{op(2, &85, &1).unwrap() > 683};
    }
}
