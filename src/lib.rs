//! Fair Resource Distribution Algorithm
//!
//! This project provides an implementation of the `fairdist` algorithm, a way to distribute a set
//! of resources fairly amongst a dynamic number of users. Its infrastructure manages a hierarchy
//! of users that currently hold shares of a resource. New users can be added at any time, and
//! charges can be requested and released dynamically. The system ensures that every new user
//! joining the system gets a guaranteed share of the total, regardless of how many users already
//! hold resources.
//!
//! The API abstracts over resources through the `[counter::Counter]` trait. This trait represents
//! a set of numeric resource counters. In most cases these will just be `usize` integers.
//! However, that is not a requirement. The resource counter is only required to "look like an
//! integer" (see `[counter::Counter]` and its dependencies on the `num` crate). Furthermore, the
//! API abstracts over users. It does not track users who interact with the system, but relies on
//! the API user to provide a key or index that identifies the user of a given operation. This way
//! the resource allocators can tell whether separate operations are performed by the same
//! accounting user, or whether they are different. This is all information the system needs about
//! the different users.
//!
//! At the root level, the API user has to create a `[Resource]` object with the resource counters
//! initialized to reflect the total resources available for distribution. These resources can now
//! be requested through `[Charge]` objects. Charges are RAII-type objects that record a resource
//! charge and make sure resources are released again when the `Charge` is dropped. To request
//! resources, the API user must specify the accounting user to perform the charge as, as well as
//! the amount to charge. If the quotas of the accounting user were exceeded, the charge is
//! rejected. Otherwise, the charge will be granted. The allocators behind the resource objects
//! make sure resources are distributed fairly. Additionally to the root-level `[Resource]`
//! objects, the API allows to create sub-hierarchies to redistribute resources further. That is,
//! new non-root-level `[Resource]` objects can be created given the accounting user to act as.
//! This new sub-resource will then behave similar to the top-level resource and allow charges to
//! be performed. It will ensure the same guarantees on its own sub-level, so the sub-distribution
//! is again fair. Furthermore, the top-level guarantees are unaffected by sub-hierarchies that
//! are formed. That is, individual accounting users cannot increase their resource shares by
//! creating sub-hierarchies.
//!
//! There are multiple possible algorithm that can be used for the individual allocations. In most
//! cases the selected default is sufficient. However, the `[allocator::Allocator]` trait allows
//! selecting from a range of predefined allocators, as well as creating individual allocators.
//! The default allocator guarantees quasilinear shares to every user of the system. In
//! particular, this means regardless how many users join the allocation system, each one is
//! guaranteed a share of 1 over `O(n * log(n)^2)` of the total.

use std::sync::{Arc, Weak};

pub mod allocator;
pub mod counter;

// Reference to a Registry Object
//
// Registries hold our internal usage maps as well as the associated resource counters. Since we
// need shared access to the registry from different threads, we put it into a reference counter
// lock. The `RegistryRef` type is an alias for this.
type RegistryRef<A, C, I> = Arc<std::sync::Mutex<Registry<A, C, I>>>;

// Usage table of a single consumer
//
// The resources of a registry are distributed amongst different users. The users are not
// represented in any way. Instead, we only require users to have a unique index of type `I`. We
// then track a usage table for each user. This table records what the user did so far and makes
// sure all accesses through the same user share a common usage table.
//
// Note that the usage table of a specific user can be pinned via the `[Subscription]` type. This
// avoids doing a look-up on each modification. However, it means access to the usage table is
// shared. Therefore, the `[Subscription]` type implements safe sharing of references to the usage
// table.
//
// All fields except for `share` are static. They are not modified during the lifetime of a usage
// table. The `share` field is protected by the mutex of the linked registry. However, for
// performance reasons it is located on the usage table rather than as a separate lookup tree on
// the registry. You must lock the registry when accessing `share`!
struct Usage<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    index: I,
    registry_ref: RegistryRef<A, C, I>,
    share: std::cell::RefCell<C>,
}

// Resource registry
//
// A resource registry is the hidden root object for resource distribution. The registry tracks
// the resources that were assigned to it, as well as all usage tables which got shares of its
// resources.
//
// A resource registry is usually hidden behind a reference counted mutex, which must be held to
// perform any kind of modification.
//
// Resource registries form a hierarchy. The root level resource has no parent resource but has
// resources assigned statically. Each subscription to this resource registry can itself be turned
// into a resource registry, though. This allows subdividing and distributing resources amongst
// hierarchical systems. Note that sub-hierarchies never affect the shares granted on parent or
// sibling hierarchies. That is, access to sub-hierarchies can be delegated to untrusted parties
// without affecting the security of the entire system.
struct Registry<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    parent: Option<Subscription<A, C, I>>,
    usages: std::collections::BTreeMap<I, Weak<Usage<A, C, I>>>,
    reserve: C,
}

/// A subscription to a resource.
///
/// A subscription allows to perform continous allocations on a resource. A subscription is simply
/// the combination of a resource and the user ID to perform accesses as. That is, a subscription
/// can be created from a resource by providing the user ID to subscribe as. All subscriptions of
/// different user IDs are distinct, but subscriptions with the same user ID reference the same
/// underlying usage table.
///
/// To request resource from a resource registry, you have to subscribe to it first. This
/// subscription is then used to request the resources in a charge. The subscription is pinned in
/// every charge, so there is no need for the caller to cache it. However, if continuous charges
/// are required, caching the subscription will skip a map lookup on every charge. Furthermore, as
/// long as a subscription is alive, the underlying resource registry consider the subscriber to
/// be interested in the resources. The resource allocation will thus be able to improve the
/// fairness of the resource distribution, because it can better estimate how many users are
/// interested in resources.
pub struct Subscription<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    usage_ref: Option<Arc<Usage<A, C, I>>>,
}

/// A resource that can be distributed amongst users.
///
/// The resource object represents a set of resources that is offered for distribution amongst
/// users. Resource objects are either assigned static resources at initialization, or they
/// distribute resources of their parent to form a hierarchy.
///
/// Any resource object can be used to subscribe to and then charge resource requests through that
/// subscription.
///
/// Resource objects are merely a reference to the underlying resource registry object. Even if
/// the resource object is destroyed, the underlying resource registry object will remain alive
/// until all charges on it were dropped.
pub struct Resource<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    registry_ref: RegistryRef<A, C, I>,
}

/// A charge represents temporarily borrowed resources.
///
/// When requesting resource shares from a resource object, a `Charge` object will be created.
/// This is an RAII object that represents the charge. When the object is dropped, the charge
/// will be released as well.
///
/// Note that shares on a charge object can be manually increases or decreases, in which case the
/// RAII benefits are lost, though.
pub struct Charge<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    subscription: Subscription<A, C, I>,
    slot: C::Index,
    charge: C::Scalar,
}

impl<A, C, I> Usage<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    // Internal helper to initialize a usage object.
    //
    // This initializes a new `Usage` object. Both `index` and `registry_ref` are cloned and
    // stored in the object. The `reserve` parameter is used as template to create a new counter
    // object. The `reserve` is passed separately, since `registry_ref` might be locked by the
    // caller, so its reserve cannot be accessed here. The caller must make sure the passed
    // reserve is compatible to the one in the registry, though (usually, you would just pass a
    // reference to the reserve in `registry_ref` here).
    fn new(index: &I, registry_ref: &RegistryRef<A, C, I>, reserve: &C) -> Self {
        Usage {
            index: index.clone(),
            registry_ref: registry_ref.clone(),
            share: std::cell::RefCell::new(counter::Counter::from_template(reserve)),
        }
    }

    // Charge Backend
    //
    // This is the backend that performs resource charges. It tries to charge `amount` resources
    // from the resource slot `index`. On success, true is returned. Otherwise, false is returned.
    //
    // This function performs a recursive charge. It tries to serve the request on the current
    // level, but if that is not sufficient, it will traverse upwards.
    fn charge(&self, index: &C::Index, amount: &C::Scalar) -> bool {
        let mut guard = self.registry_ref.lock().unwrap();
        let mut share = self.share.borrow_mut();
        let registry = &mut *guard;
        let n_usages = registry.usages.len();
        let reserve_slot = registry.reserve.slot(index);
        let share_slot = share.slot(index);

        match
            <A as allocator::Allocator<C::Scalar>>::minimum_reserve_for(
                n_usages,
                share_slot,
                amount,
            )
        {
            None => {
                false
            }
            Some(mut minimum) => {
                if &*reserve_slot >= &minimum {
                    *share_slot += amount;
                    *reserve_slot -= amount;

                    true
                } else {
                    minimum -= reserve_slot;
                    if let Some(subscription) = registry.parent.as_ref() {
                        // XXX: This currently recurses into the charge helper. We should instead
                        //      do this via a frame objects on a `Vec`. However, that requires to
                        //      investigate how to store mutex RAII guards in the same `Vec`...
                        if subscription.deref().charge(index, &minimum) {
                            *share_slot += amount;
                            *reserve_slot -= amount;

                            true
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                }
            }
        }
    }

    // Discharge Backend
    //
    // This is the backend implementation of a discharge. It releases `amount` resources of the
    // resource slot `index`. It is the caller's responsibility to guarantee the resources were
    // previously allocated through a charge.
    fn discharge(&self, index: &C::Index, amount: &C::Scalar) {
        let mut guard = self.registry_ref.lock().unwrap();
        let mut share = self.share.borrow_mut();
        let share_slot = share.slot(index);
        let reserve_slot = guard.reserve.slot(index);

        // This simply releases the resources to the current level. It never traverses the parent
        // hierarchy to release further resources, as it would provide little gain but cost a lot
        // of computing time.
        *share_slot -= amount;
        *reserve_slot += amount;
    }
}

impl<A, C, I> Drop for Usage<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    // Verify all shares were dropped, to protect against charge leaks.
    fn drop(&mut self) {
        assert!{self.share.borrow().empty()};
    }
}

impl<A, C, I> Registry<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    // Create a new subscription object.
    //
    // This is the internal backend that creates a new subscription object given a registry and an
    // index. Note that while this will create a new subscription, it will still share the pinned
    // usage with all other subscriptions of this index.
    //
    // This is an associated function since we need access to the Arc so we can clone it for the
    // new subscription.
    fn subscribe(registry_ref: &RegistryRef<A, C, I>, index: &I) -> Subscription<A, C, I> {
        // Lock the registry and search for a usage entry indexed by `index`. If none is available
        // create a new one and insert it into the registry. The result of this block is a usage
        // Arc to either the existing or the new entry.
        let mut guard = registry_ref.lock().unwrap();
        let registry = &mut *guard;
        let usage = match registry.usages.entry(index.clone()) {
            std::collections::btree_map::Entry::Vacant(entry) => {
                // No entry exists. Create a new one, insert a weak reference into the lookup
                // tree and return the strong reference.
                let usage = Arc::new(
                    Usage::new(
                        index,
                        registry_ref,
                        &registry.reserve,
                    )
                );
                entry.insert(Arc::downgrade(&usage));
                usage
            },
            std::collections::btree_map::Entry::Occupied(entry) => {
                // There is already an entry. Since the resource is locked, we know there
                // must be another strong reference, so the upgrade must be successful.
                Weak::upgrade(entry.get()).unwrap()
            },
        };

        Subscription {
            usage_ref: Some(usage),
        }
    }
}

impl<A, C, I> Subscription<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    // Dereference a subscription to the underlying usage.
    //
    // This borrows the subscription and returns a reference to the underlying usage entry. It is
    // basically equivalent to `std::ops::Deref<Target = Usage<A, C, I>>`. However, we cannot
    // implement `Deref`, since we would leak the private type `Usage` through the public type
    // `Subscription`.
    fn deref(&self) -> &Usage<A, C, I> {
        self.usage_ref.as_ref().unwrap()
    }
}

impl<A, C, I> Drop for Subscription<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    fn drop(&mut self) {
        // We have to drop the usage-arc we hold. We have to do that manually, since if we are the
        // last one, we have to unlink the usage from the registry. For that, we steal the Arc
        // from the Pin object here, so it becomes `None` and the rust-runtime can later on
        // tear down the Pin object itself.
        if let Some(usage_ref) = self.usage_ref.take() {
            // XXX: Preferably, we would drop the Arc without acquiring the lock, unless we are
            //      the last. However, the Arc implementation does not provide anything like that.
            //      We would want something like the existing `Arc::try_unwrap()`, but one that
            //      drops the Arc in the failure case, rather than returning it.
            //      Since that does not exist, we instead always acquire and lock the resource. We
            //      then drop the Arc from under the lock under all circumstances.
            let registry_ref = usage_ref.registry_ref.clone();
            let mut guard = registry_ref.lock().unwrap();
            let registry = &mut *guard;

            // If we are the last strong reference, make sure to drop the referenced usage from
            // its parent map. Note that the registry is locked, so no lookups can happen.
            // Additionally, we own the last strong reference, so there is no way anyone else can
            // acquire a strong reference, anymore (ignoring weak-refs, which we do not make use
            // of outside of the lookup tree).
            match Arc::try_unwrap(usage_ref) {
                Ok(usage) => {
                    // We destructed the usage-arc, so now also drop it from the lookup-tree.
                    registry.usages.remove(&usage.index);
                },
                Err(usage_ref) => {
                    // We are not the last reference. Make sure to drop our Arc before releasing
                    // the lock. Note that this drop is for documentational purposes, since the
                    // variable is only valid in this block, anyway.
                    std::mem::drop(usage_ref);
                }
            }
        }
    }
}

impl<A, C, I> Clone for Subscription<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    fn clone(&self) -> Self {
        Subscription {
            usage_ref: Some(self.usage_ref.as_ref().unwrap().clone()),
        }
    }
}

impl<A, C, I> Resource<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    /// Create a new top-level resource with a given reserve.
    ///
    /// This consumes `reserve` and creates a new `Resource` object around it. It will be a
    /// top-level resource. The resources provided through `reserve` will now be available for
    /// distribution through subscriptions to this new `Resource` object.
    pub fn with_reserve(reserve: C) -> Self {
        Resource {
            registry_ref:
                Arc::new(
                    std::sync::Mutex::new(
                        Registry {
                            parent: None,
                            usages: Default::default(),
                            reserve: reserve,
                        }
                    )
                ),
        }
    }

    /// Create a new sub-hierarchy resource.
    ///
    /// This creates a new `Resource` object as child of the resource object of the given
    /// subscription. The new resource has no reserves of its own, but only redistributes the
    /// parent resources in a new hierarchy.
    pub fn with_parent(parent: Subscription<A, C, I>) -> Self {
        let reserve =
            counter::Counter::from_template(
                &parent.deref()
                       .registry_ref.lock()
                       .unwrap()
                       .reserve
            );

        Resource {
            registry_ref:
                Arc::new(
                    std::sync::Mutex::new(
                        Registry {
                            parent: Some(parent),
                            usages: Default::default(),
                            reserve: reserve,
                        }
                    )
                ),
        }
    }

    /// Subscribe to a resource.
    ///
    /// This creates a new `Subscription` object, subscribed to the given resource and index. The
    /// subscription will allow you to request resource charges.
    pub fn subscribe(&self, index: &I) -> Subscription<A, C, I> {
        Registry::subscribe(&self.registry_ref, index)
    }
}

impl<A, C, I> Charge<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    /// Create a new Charge object.
    ///
    /// This creates a new `Charge` object using the given subscription. The `slot` argument
    /// specifies the resource slot to use for any resource request.
    pub fn new(subscription: Subscription<A, C, I>, slot: &C::Index) -> Self {
        Charge {
            subscription: subscription,
            slot: slot.clone(),
            charge: num::Zero::zero(),
        }
    }

    /// Charge further resources through an existing Charge object.
    ///
    /// This tries to increase the charges of the `Charge` object by `amount`. If the charge is
    /// rejected, false is returned and the `Charge` object stays unmodified. If the charge
    /// succeeds, true is returned and the `Charge` object will increase its charge counter by
    /// `amount`.
    pub fn charge(&mut self, amount: &C::Scalar) -> bool {
        let usage = self.subscription.deref();
        let r = usage.charge(&self.slot, amount);

        if r {
            self.charge += amount;
        }

        r
    }

    /// Discharge previously charged resources from a Charge object.
    ///
    /// This releases resources back to the originating `Resource` object. The resources must have
    /// been acquired previously via `[Charge::charge()]`.
    ///
    /// The caller is free to split charges and discharges. That is, the caller is free to only
    /// release partial amounts of a previous charge, or combine multiple individual charges into
    /// a single discharge.
    ///
    /// It is the caller's responsibility to never release more charges than were actually
    /// acquired.
    pub fn discharge(&mut self, amount: &C::Scalar) {
        assert!{amount >= &self.charge};
        let usage = self.subscription.deref();
        usage.discharge(&self.slot, amount);
        self.charge -= amount;
    }

    /// Discharge all previously charged resources.
    ///
    /// This discharges all resources of this `Charge` object. This is also automatically done
    /// when the `Charge` object is dropped.
    pub fn discharge_all(&mut self) {
        let usage = self.subscription.deref();
        usage.discharge(&self.slot, &self.charge);
        self.charge = num::Zero::zero();
    }
}

impl<A, C, I> Drop for Charge<A, C, I> where
    A: allocator::Allocator<C::Scalar>,
    C: counter::Counter,
    I: Clone + Ord,
{
    fn drop(&mut self) {
        // When a charge object is dropped, we need to discharge all pending charges. We simply
        // call into the discharge helpers. No special considerations need to be taken.
        self.discharge_all();
        assert!{num::Zero::is_zero(&self.charge)};
    }
}
