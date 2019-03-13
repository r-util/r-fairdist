// Basic Integration Tests
//
// This file contains a set of basic functionality tests. This includes all kinds of tests for the
// public API, as well as tests for common functionality, and tests that do not belong into the
// more specific other test collections.

use r_fairdist::*;

// Basic Functionality Test
//
// This is a very simple functionality test of the public API. It performs basic allocations on a
// trivial one-dimensional resource counter. It does not rely on complex internals, and thus is a
// good baseline test when changing the API.
#[test]
fn basic_operation() {
    let res = Resource::<allocator::Quasilinear, [usize; 1], usize>::with_reserve([1024]);

    // Single user with quasilinear can acquire 256 of 1024.
    let mut c1 = Charge::new(res.subscribe(&1), &());
    assert!{!c1.charge(&1024)};
    assert!{c1.charge(&256)};
    assert!{!c1.charge(&1)};

    // Second user with quasilinear on full setup can acquire 85 more.
    let mut c2 = Charge::new(res.subscribe(&2), &());
    assert!{!c2.charge(&1024)};
    assert!{c2.charge(&85)};
    assert!{!c2.charge(&1)};

    // Releasing the initial charge allows the second user to bump up to 256.
    drop(c1);
    assert!{c2.charge(&(256 - 85))};
    assert!{!c2.charge(&1)};
}
