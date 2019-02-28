//! Allocator
//!
//! This module implements the allocation calculations which the fair distribution algorithm is
//! based on. At its core is the `[allocate()]` function, which performs quota checks and updates
//! resource counters based on the selected algorithm.

use std::sync::atomic;

// Perform a generic operation on an atomic.
//
// This function performs an operation on an atomic value. Unlike on normal values, updating an
// atomic might race with other updates. Hence, this function fetches the current atomic value,
// calls the provided closure to calculate the next value, and then tries to update the atomic. If
// the atomic changed in the meantime, the operation is retried.
//
// XXX: This function is available on all atomics in upstream rust, but currently marked as
//      unstable. We should update to it as soon as it is stabilized.
fn atomic_fetch_update<F>(
    atomic: &atomic::AtomicUsize,
    mut operator: F,
    fetch_order: atomic::Ordering,
    set_order: atomic::Ordering,
) -> Result<usize, usize> where
    F: FnMut(usize) -> Option<usize>
{
    let mut previous = atomic.load(fetch_order);

    while let Some(next) = operator(previous) {
        match atomic.compare_exchange_weak(previous, next, set_order, fetch_order) {
            x @ Ok(_)       => return x,
            Err(next_previous)  => previous = next_previous,
        }
    }

    Err(previous)
}

// Calculate floored base-2 logarithm.
//
// This is an internal helper which calculates the base-2 logarithm of a `usize` value, rounding
// down in case of missing precision.
//
// Note that this is only here for testing and documentational purposes. The `log2_ceil()` version
// is the one we actually need.
#[cfg(test)]
fn log2_floor(v: usize) -> usize {
    assert!{v > 0};
    (std::mem::size_of::<usize>() * 8) as usize - v.leading_zeros() as usize - 1
}

// Calculate ceiled base-2 logarithm.
//
// This is an internal helper which calculates the base-2 logarithm of a `usize` value, rounding
// up in case of missing precision.
fn log2_ceil(v: usize) -> usize {
    assert!{v > 0};
    (std::mem::size_of::<usize>() * 8) as usize - (v - 1).leading_zeros() as usize
}

/// Allocator with exponential guarantees.
///
/// This is a predefined allocator to be used in combination with `[allocate()]`.
///
/// This allocator grants `1 / 2` of the remaining resources to every allocation. This
/// guarantees every user gets a share proportional to `O(2^n)` of the total.
pub fn allocate_exponential(previous: usize, _users: usize, share: usize, amount: usize) -> Option<usize> {
    if let Some(limit) = share.checked_add(amount) {
        if let Some(limit) = limit.checked_mul(2) {
            if let Some(limit) = limit.checked_sub(share) {
                if limit <= previous {
                    return Some(previous - amount);
                }
            }
        }
    }

    None
}

/// Allocator with polynomial guarantees.
///
/// This is a predefined allocator to be used in combination with `[allocate()]`.
///
/// This allocator grants `1 / (n+1)` of the remaining resources to every allocation. This
/// guarantees every user gets a share proportional to `O(n^2)` of the total.
pub fn allocate_polynomial(previous: usize, users: usize, share: usize, amount: usize) -> Option<usize> {
    if let Some(limit) = share.checked_add(amount) {
        if let Some(limit) = limit.checked_mul(users + 1) {
            if let Some(limit) = limit.checked_sub(share) {
                if limit <= previous {
                    return Some(previous - amount);
                }
            }
        }
    }

    None
}

/// Allocator with quasilinear guarantees.
///
/// This is a predefined allocator to be used in combination with `[allocate()]`.
///
/// This allocator grants `1 / ((n+1) * log_2(n+1) + (n+1))` of the remaining resources to every
/// allocation. This guarantees every user gets a share proportional to `O(n log(n)^2)` of the
/// total.
pub fn allocate_quasilinear(previous: usize, users: usize, share: usize, amount: usize) -> Option<usize> {
    if let Some(n) = log2_ceil(users + 1).checked_mul(users + 1) {
        if let Some(n) = n.checked_add(users + 1) {
            if let Some(limit) = share.checked_add(amount) {
                if let Some(limit) = limit.checked_mul(n) {
                    if let Some(limit) = limit.checked_sub(share) {
                        if limit <= previous {
                            return Some(previous - amount);
                        }
                    }
                }
            }
        }
    }

    None
}

/// Fair Resource Allocator
///
/// This is the backend implementation of the actual resource allocator. This function takes a
/// resource counter `resource_slot` and subtracts `amount` from it if, and only if, the
/// allocation passes the quota checks. On success, true is returned. On failure, false is
/// returned.
///
/// The quota checks are under control of the caller. The closure given as `operator` is passed
/// all the allocation parameters, and then decides whether the allocation should take place or
/// not.
///
/// This function operates in a lockless fashion. It first charges the new allocation on
/// `share_slot`, which is the slot that remembers the allocations done so far by the calling
/// user. It then calculates the maximum charge allowed to the calling user (which is based on its
/// past allocations `share_slot`, on the number of active other users `users_slot` and the
/// remaining resources `resource_slot`). If `amount` is less than, or equal to, the allowed
/// charge, then it is substracted from `resource_slot`. If not, the charge on `share_slot` is
/// reversed and `false` is returned.
///
/// The quota closure `operator` is used to check whether the final charge is allowed to happen.
/// After `share_slot` was charged, the current values of `resource_slot` and `users_slot` are
/// fetched and passed together with the initial value of `share_slot` and `amount` (in that
/// order) to the closure. The closure should then return an `Option<usize>` that tells whether
/// the allocation should succeed, and if it should, what to set `resource_slot` to. Since this
/// might be called in a compare-and-swap loop, the function might be called multiple times in
/// case other allocations race this one.
///
/// If in doubt, use `[allocate_quasilinear()]` as @operator. It is a fair allocator with best
/// distribution and quasilinear allocation guarantees. Other allocators available include
/// `[allocate_polynomial()]` and `[allocate_exponential()]`.
pub fn allocate<F>(
    resource_slot: &atomic::AtomicUsize,
    users_slot: &atomic::AtomicUsize,
    share_slot: &atomic::AtomicUsize,
    mut operator: F,
    amount: usize,
) -> bool where
    F: FnMut(usize, usize, usize, usize) -> Option<usize>
{
    if let Ok(share) =
        atomic_fetch_update(
            share_slot,
            |previous| previous.checked_add(amount),
            atomic::Ordering::Acquire,
            atomic::Ordering::SeqCst,
        )
    {
        if let Ok(_) =
            atomic_fetch_update(
                resource_slot,
                |previous| {
                    operator(
                        previous,
                        users_slot.load(atomic::Ordering::Acquire),
                        share,
                        amount,
                    )
                },
                atomic::Ordering::Acquire,
                atomic::Ordering::SeqCst,
            )
        {
            return true;
        }

        let n = share_slot.fetch_sub(amount, atomic::Ordering::Release);
        assert!{n >= amount};
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    // The quasilinear allocators need base-2 logarithms on integers. We have two trivial
    // implementations based on the `clz` (count-leading-zeroes) CPU features. This test simply
    // verifies they work correctly.
    #[test]
    fn verify_log() {
        assert_eq!{log2_floor( 1), 0};
        assert_eq!{log2_floor( 2), 1};
        assert_eq!{log2_floor( 3), 1};
        assert_eq!{log2_floor( 4), 2};
        assert_eq!{log2_floor( 5), 2};
        assert_eq!{log2_floor( 6), 2};
        assert_eq!{log2_floor( 7), 2};
        assert_eq!{log2_floor( 8), 3};
        assert_eq!{log2_floor( 9), 3};
        assert_eq!{log2_floor(10), 3};
        assert_eq!{log2_floor(11), 3};
        assert_eq!{log2_floor(12), 3};
        assert_eq!{log2_floor(13), 3};
        assert_eq!{log2_floor(14), 3};
        assert_eq!{log2_floor(15), 3};
        assert_eq!{log2_floor(16), 4};

        assert_eq!{log2_ceil( 1), 0};
        assert_eq!{log2_ceil( 2), 1};
        assert_eq!{log2_ceil( 3), 2};
        assert_eq!{log2_ceil( 4), 2};
        assert_eq!{log2_ceil( 5), 3};
        assert_eq!{log2_ceil( 6), 3};
        assert_eq!{log2_ceil( 7), 3};
        assert_eq!{log2_ceil( 8), 3};
        assert_eq!{log2_ceil( 9), 4};
        assert_eq!{log2_ceil(10), 4};
        assert_eq!{log2_ceil(11), 4};
        assert_eq!{log2_ceil(12), 4};
        assert_eq!{log2_ceil(13), 4};
        assert_eq!{log2_ceil(14), 4};
        assert_eq!{log2_ceil(15), 4};
        assert_eq!{log2_ceil(16), 4};
    }

    // This tests the behavior of the exponential allocator. We setup a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 512.
    //
    // The allocator we use grants everyone 1/2 of the remaining resources. It does *NOT* depend
    // on the number of active users, hence it is ignored in these tests.
    #[test]
    fn exponential_allocation() {
        let op = allocate_exponential;
        let r = atomic::AtomicUsize::new(1024);
        let n = atomic::AtomicUsize::new(0);
        let s1 = atomic::AtomicUsize::new(0);
        let s2 = atomic::AtomicUsize::new(0);

        // As first step verify nothing bigger than 512 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        assert!{!allocate(&r, &n, &s1, op, 513)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 1024};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 0};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Now try a full allocation of 512. This is the biggest allocation possible. Verify
        // afterwards that the counters have been correctly updated.
        assert!{allocate(&r, &n, &s1, op, 512)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{!allocate(&r, &n, &s1, op, 1)};
        assert!{!allocate(&r, &n, &s1, op, 512)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        // Now switch to the next share and try again. This time the maximum is 256 (half of the
        // remaining 512). We perform the allocation in two steps 128 each. We then verify that
        // this saturates the allocation.
        assert!{!allocate(&r, &n, &s2, op, 257)};
        assert!{!allocate(&r, &n, &s2, op, 512)};
        assert!{!allocate(&r, &n, &s2, op, 1024)};
        assert!{!allocate(&r, &n, &s2, op, std::usize::MAX)};

        assert!{allocate(&r, &n, &s2, op, 128)};
        assert!{allocate(&r, &n, &s2, op, 128)};
        assert!{!allocate(&r, &n, &s2, op, 1)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 256};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 256};
    }

    // This tests the behavior of the polynomial allocator. We setup a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 512.
    //
    // The allocator we use grants everyone an n-plus-1'th of the remaining resources. Hence, we
    // need to update @n according to the current number of peers.
    #[test]
    fn polynomial_allocation() {
        let op = allocate_polynomial;
        let r = atomic::AtomicUsize::new(1024);
        let n = atomic::AtomicUsize::new(0);
        let s1 = atomic::AtomicUsize::new(0);
        let s2 = atomic::AtomicUsize::new(0);

        // As first step verify nothing bigger than 512 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        n.fetch_add(1, atomic::Ordering::SeqCst);

        assert!{!allocate(&r, &n, &s1, op, 513)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 1024};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 0};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Now try a full allocation of 512. This is the biggest allocation possible. Verify
        // afterwards that the counters have been correctly updated.
        assert!{allocate(&r, &n, &s1, op, 512)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{!allocate(&r, &n, &s1, op, 1)};
        assert!{!allocate(&r, &n, &s1, op, 512)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        // Now switch to the next share and try again. This time the maximum is a third of 512,
        // which is 170. We split it in two allocations of 85 each, to verify split allocations
        // work the same way.
        n.fetch_add(1, atomic::Ordering::SeqCst);

        assert!{!allocate(&r, &n, &s2, op, 171)};
        assert!{!allocate(&r, &n, &s2, op, 512)};
        assert!{!allocate(&r, &n, &s2, op, 1024)};
        assert!{!allocate(&r, &n, &s2, op, std::usize::MAX)};

        assert!{allocate(&r, &n, &s2, op, 85)};
        assert!{allocate(&r, &n, &s2, op, 85)};
        assert!{!allocate(&r, &n, &s2, op, 1)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 342};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 512};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 170};
    }

    // This tests the behavior of the quasilinear allocator. We setup a resource pool of 1024,
    // which means the biggest allocation (which also has to be the first) is 256.
    //
    // The allocator we use grants everyone `1 / ((n+1) * log_2(n+1) + (n+1))` of the remaining
    // resources.
    #[test]
    fn quasilinear_allocation() {
        let op = allocate_quasilinear;
        let r = atomic::AtomicUsize::new(1024);
        let n = atomic::AtomicUsize::new(0);
        let s1 = atomic::AtomicUsize::new(0);
        let s2 = atomic::AtomicUsize::new(0);

        // As first step verify nothing bigger than 256 ever succeeds. We also try some values
        // that are known to trigger integer overflows. These should be caught by the
        // allocators correctly.
        n.fetch_add(1, atomic::Ordering::SeqCst);

        assert!{!allocate(&r, &n, &s1, op, 257)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 1024};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 0};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Now try a full allocation of 256. This is the biggest allocation possible. Verify
        // afterwards that the counters have been correctly updated.
        assert!{allocate(&r, &n, &s1, op, 256)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 768};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 256};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 0};

        // Verify that this share is saturated and no further allocations are possible.
        assert!{!allocate(&r, &n, &s1, op, 1)};
        assert!{!allocate(&r, &n, &s1, op, 512)};
        assert!{!allocate(&r, &n, &s1, op, 1024)};
        assert!{!allocate(&r, &n, &s1, op, std::usize::MAX)};

        // Now switch to the next share and try again. This time the maximum is a nineth of 512,
        // which is 85.3~. We split it in two allocations of 40 and 45, to verify split
        // allocations work the same way.
        n.fetch_add(1, atomic::Ordering::SeqCst);

        assert!{!allocate(&r, &n, &s2, op, 86)};
        assert!{!allocate(&r, &n, &s2, op, 512)};
        assert!{!allocate(&r, &n, &s2, op, 1024)};
        assert!{!allocate(&r, &n, &s2, op, std::usize::MAX)};

        assert!{allocate(&r, &n, &s2, op, 40)};
        assert!{allocate(&r, &n, &s2, op, 45)};
        assert!{!allocate(&r, &n, &s2, op, 1)};

        assert_eq!{r.load(atomic::Ordering::SeqCst), 683};
        assert_eq!{s1.load(atomic::Ordering::SeqCst), 256};
        assert_eq!{s2.load(atomic::Ordering::SeqCst), 85};
    }
}
