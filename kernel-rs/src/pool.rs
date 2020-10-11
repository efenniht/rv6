use core::marker::PhantomData;
use core::mem::{self, ManuallyDrop, MaybeUninit};
use core::ops::{Deref, DerefMut};

use crate::spinlock::Spinlock;

struct RcEntry<T> {
    ref_cnt: usize,
    data: MaybeUninit<T>,
}

/// A homogeneous memory allocator equipped with reference counts.
pub struct RcPool<T, const CAPACITY: usize> {
    inner: [RcEntry<T>; CAPACITY],
}

pub struct UntaggedRc<T> {
    ptr: *mut RcEntry<T>,
}

impl<T, const CAPACITY: usize> RcPool<T, CAPACITY> {
    pub const fn new() -> Self {
        Self {
            inner: [RcEntry {
                ref_cnt: 0,
                data: MaybeUninit::uninit(),
            }; CAPACITY],
        }
    }
}

impl<T> Deref for UntaggedRc<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { (*self.ptr).data.assume_init_ref() }
    }
}

// TODO: This may cause UB; remove after refactoring File::{read, write}.
impl<T> DerefMut for UntaggedRc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { (*self.ptr).data.assume_init_mut() }
    }
}

impl<T> Drop for UntaggedRc<T> {
    fn drop(&mut self) {
        // HACK(@efenniht): we really need linear type here:
        // https://github.com/rust-lang/rfcs/issues/814
        panic!("UntaggedRc must never drop: use RcPool::dealloc instead.");
    }
}

/// A homogeneous memory allocator, equipped with the box type representing an allocation.
pub trait Pool {
    /// The value type of the allocator.
    type Data: 'static;

    /// The box type of the allocator.
    type PoolBox: 'static;

    /// Failable allocation.
    fn alloc(&self, val: Self::Data) -> Option<Self::PoolBox>;

    fn find_or_alloc<F>(&self, val: Self::Data, f: F) -> Option<Self::PoolBox>
    where
        F: Fn(&Self::Data) -> bool;

    /// # Safety
    ///
    /// `pbox` must be allocated from the pool.
    unsafe fn dealloc(&self, pbox: Self::PoolBox);

    /// # Safety
    ///
    /// `rc` must be allocated from `self`.
    unsafe fn dup(&self, pbox: &Self::PoolBox) -> Self::PoolBox;
}

impl<T: 'static, const CAPACITY: usize> Pool for Spinlock<RcPool<T, CAPACITY>> {
    type Data = T;
    type PoolBox = UntaggedRc<T>;

    fn alloc(&self, val: T) -> Option<UntaggedRc<T>> {
        for entry in self.lock().inner.iter_mut() {
            if entry.ref_cnt == 0 {
                entry.ref_cnt = 1;
                entry.data.write(val);
                return Some(UntaggedRc { ptr: entry });
            }
        }

        None
    }

    fn find_or_alloc<F>(&self, val: T, f: F) -> Option<UntaggedRc<T>>
    where
        F: Fn(&T) -> bool,
    {
        let mut pool = self.lock();
        let mut empty = None;
        for (idx, entry) in pool.inner.iter_mut().enumerate() {
            if empty.is_none() && entry.ref_cnt == 0 {
                empty = Some(idx);
            } else if entry.ref_cnt != 0 && f(unsafe { entry.data.assume_init_ref() }) {
                entry.ref_cnt += 1;
                return Some(UntaggedRc { ptr: entry });
            }
        }

        if let Some(idx) = empty {
            let entry = &mut pool.inner[idx];
            entry.ref_cnt = 1;
            entry.data.write(val);
            return Some(UntaggedRc { ptr: entry });
        }

        None
    }

    /// # Safety
    ///
    /// `rc` must be allocated from `self`.
    unsafe fn dealloc(&self, rc: UntaggedRc<T>) {
        let val = {
            let _guard = self.lock();
            let entry = &mut *rc.ptr;

            entry.ref_cnt -= 1;
            if entry.ref_cnt == 0 {
                Some(entry.data.read())
            } else {
                None
            }
        };

        mem::forget(rc);

        // Drop AFTER the pool lock is released, as dropping val may cause the current thread sleep.

        // TODO: Defer drop may cause invariant break on get_or_alloc.
        mem::drop(val);
    }

    /// # Safety
    ///
    /// `rc` must be allocated from `self`.
    unsafe fn dup(&self, rc: &UntaggedRc<T>) -> UntaggedRc<T> {
        let _guard = self.lock();
        (*rc.ptr).ref_cnt += 1;
        UntaggedRc { ptr: rc.ptr }
    }
}

/// A zero-sized reference of the `Pool`, represented in a type.
///
/// Ensures the safety of `dealloc` by PoolRef type parameter of TaggedBox. See
/// https://ferrous-systems.com/blog/zero-sized-references/ for details.
///
/// # Safety
///
/// There should be at most one implementation of PoolRef for each Pool.
pub unsafe trait PoolRef: Sized {
    type Target: Pool + 'static;

    fn deref() -> &'static Self::Target;

    fn alloc(
        val: <Self::Target as Pool>::Data,
    ) -> Option<TaggedBox<Self, <Self::Target as Pool>::Data>> {
        let alloc = Self::deref().alloc(val)?;
        Some(TaggedBox {
            alloc: ManuallyDrop::new(alloc),
            _marker: PhantomData,
        })
    }

    fn find_or_alloc<F>(
        val: <Self::Target as Pool>::Data,
        f: F,
    ) -> Option<TaggedBox<Self, <Self::Target as Pool>::Data>>
    where
        F: Fn(&<Self::Target as Pool>::Data) -> bool,
    {
        let alloc = Self::deref().find_or_alloc(val, f)?;
        Some(TaggedBox {
            alloc: ManuallyDrop::new(alloc),
            _marker: PhantomData,
        })
    }

    fn dealloc(tbox: TaggedBox<Self, <Self::Target as Pool>::Data>) {
        mem::drop(tbox);
    }
}

/// Allocation from `P`.
#[repr(transparent)]
pub struct TaggedBox<P: PoolRef, T: 'static>
where
    P::Target: Pool<Data = T>,
{
    alloc: ManuallyDrop<<P::Target as Pool>::PoolBox>,
    _marker: PhantomData<P>,
}

impl<P: PoolRef, T: 'static> TaggedBox<P, T>
where
    P::Target: Pool<Data = T>,
{
    /// # Safety
    ///
    /// `pbox` must be allocated from `P`.
    pub unsafe fn from_unchecked(pbox: <P::Target as Pool>::PoolBox) -> Self {
        Self {
            alloc: ManuallyDrop::new(pbox),
            _marker: PhantomData,
        }
    }
}

impl<P: PoolRef, T: 'static> Clone for TaggedBox<P, T>
where
    P::Target: Pool<Data = T>,
{
    fn clone(&self) -> Self {
        unsafe { Self::from_unchecked(P::deref().dup(self)) }
    }
}

impl<P: PoolRef, T: 'static> Deref for TaggedBox<P, T>
where
    P::Target: Pool<Data = T>,
{
    type Target = <P::Target as Pool>::PoolBox;
    fn deref(&self) -> &Self::Target {
        &self.alloc
    }
}

impl<P: PoolRef, T: 'static> DerefMut for TaggedBox<P, T>
where
    P::Target: Pool<Data = T>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.alloc
    }
}

impl<P: PoolRef, T: 'static> Drop for TaggedBox<P, T>
where
    P::Target: Pool<Data = T>,
{
    fn drop(&mut self) {
        // SAFETY: We can ensure the box is allocated from `P` by the invariant of PoolRef.
        unsafe {
            let pbox = ManuallyDrop::take(&mut self.alloc);
            P::deref().dealloc(pbox);
        }
    }
}
