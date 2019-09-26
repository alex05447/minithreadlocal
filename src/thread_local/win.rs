use std::marker::PhantomData;
use std::ptr;

use winapi::shared::minwindef::{DWORD, LPVOID};
use winapi::shared::winerror::ERROR_SUCCESS;
use winapi::um::errhandlingapi::GetLastError;
use winapi::um::processthreadsapi::{
    TlsAlloc, TlsFree, TlsGetValue, TlsSetValue, TLS_OUT_OF_INDEXES,
};

/// Low-level OS thread local storage abstraction with minimal safety guarantees.
///
/// The caller must ensure the following:
/// 1) Each thread, inluding the initializing thread which creates the `ThreadLocal` object, must call [`store`]
/// before the first access to the stored value;
/// 2) Each thread may not call [`store`] more than once until the call to [`take`];
/// 3) Each thread may not access the stored value after the call to [`take`] in that thread;
/// 4) Each thread must call [`take`] to drop the stored value and reclaim allocated memory;
/// 5) [`free_index`] must be called once after last use to free the internal thread local storage index.
///
/// [`store`]: #method.store
/// [`take`]: #method.take
/// [`free_index`]: #method.free_index
#[derive(Copy)]
pub struct ThreadLocal<T> {
    index: DWORD,
    _marker: PhantomData<T>,
}

impl<T> Clone for ThreadLocal<T> {
    fn clone(&self) -> Self {
        Self {
            index: self.index,
            _marker: PhantomData,
        }
    }
}

impl<T> ThreadLocal<T> {
    /// Called once by the initializing thread.
    /// Allocates a thread local storage index the object will use to store values.
    ///
    /// # Panics
    ///
    /// Panics if the OS runs out of TLS indices. The upper limit depends on the OS version.
    /// It's not recommended to create more than a handful of `ThreadLocal` objects.
    pub fn new() -> Self {
        let index = unsafe { TlsAlloc() };

        if index == TLS_OUT_OF_INDEXES {
            panic!("Out of thread local storage indices.");
        }

        Self {
            index,
            _marker: PhantomData,
        }
    }

    // Takes ownership of the provided value and stores it in this thread's local slot.
    ///
    /// # Panics
    ///
    /// Panics if the thread's slot was already occupied by a previous call to [`store`].
    ///
    /// [`store`]: #method.store
    pub fn store(&self, t: T) {
        assert!(
            self.get_ptr().is_null(),
            "Tried to store a new value into an occupied thread local storeage slot."
        );
        let boxed = Box::new(t);
        self.set_ptr(Box::into_raw(boxed));
    }

    /// Retrieves the value stored in this thread's local slot by a previous call to [`store`]
    /// and clears the slot allowing to call [`store`] again.
    ///
    /// # Panics
    ///
    /// Panics if the thread's slot is empty.
    ///
    /// [`store`]: #method.store
    pub fn take(&self) -> T {
        let ptr = self.get_ptr();
        assert!(
            !ptr.is_null(),
            "Tried to take an empty thread local storage slot."
        );
        let boxed = unsafe { Box::from_raw(ptr) };
        self.set_ptr(ptr::null_mut());
        *boxed
    }

    /// Returns a mutable reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or `None` if the slot is empty.
    ///
    /// [`store`]: #method.store
    pub fn try_as_mut(&self) -> Option<&mut T> {
        self.as_mut_impl()
    }

    /// Returns a reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or `None` if the slot is empty.
    ///
    /// [`store`]: #method.store
    pub fn try_as_ref(&self) -> Option<&T> {
        self.as_mut_impl().map(|r| r as &T)
    }

    /// Returns a mutable reference to the value stored in this thread's local slot by a previous call to [`store`].
    ///
    /// # Panics
    ///
    /// Panics if the thread's slot is empty.
    ///
    /// [`store`]: #method.store
    pub fn as_mut(&self) -> &mut T {
        self.as_mut_impl()
            .expect("Tried to access an empty thread local storage slot.")
    }

    /// Returns a reference to the value stored in this thread's local slot by a previous call to [`store`].
    ///
    /// # Panics
    ///
    /// Panics if the thread's slot is empty.
    ///
    /// [`store`]: #method.store
    pub fn as_ref(&self) -> &T {
        self.as_mut_impl()
            .map(|r| r as &T)
            .expect("Tried to access an empty thread local storage slot.")
    }

    /// Frees the thread's local storage slot, disallowing further use of the `ThreadLocal` object.
    /// Unsafe to call from multiple threads as the operation is not atomic.
    ///
    /// # Panics
    ///
    /// Panics if the thread local storage index was already freed by a previous call to [`free_index`].
    /// Panics if the value stored in the thread's local slot was not retrieved and was leaked.
    /// Panics if the OS failed to free the index, possibly because of a thread-unsafe previous call to [`free_index`].
    ///
    /// [`free_index`]: #method.free_index
    pub fn free_index(&mut self) {
        assert!(
            self.index != TLS_OUT_OF_INDEXES,
            "`ThreadLocal::free_index` called more than once."
        );
        assert!(
            self.get_ptr().is_null(),
            "Leaked a thread local object in the finalizing thread."
        );

        unsafe {
            if TlsFree(self.index) == 0 {
                panic!("Failed to free a thread local storage index.");
            }
        }

        self.index = TLS_OUT_OF_INDEXES;
    }

    fn as_mut_impl(&self) -> Option<&mut T> {
        let ptr = self.get_ptr();
        if !ptr.is_null() {
            Some(unsafe { &mut *ptr })
        } else {
            None
        }
    }

    fn set_ptr(&self, ptr: *const T) {
        assert!(
            self.index != TLS_OUT_OF_INDEXES,
            "Tried to store a value to a freed thread local storage index."
        );
        unsafe {
            if TlsSetValue(self.index, ptr as LPVOID) == 0 {
                panic!("Failed to store to thread local storage.");
            }
        }
    }

    fn get_ptr(&self) -> *mut T {
        let ptr = unsafe { TlsGetValue(self.index) };
        if ptr == 0 as LPVOID {
            if unsafe { GetLastError() } == ERROR_SUCCESS {
                ptr as *mut T
            } else {
                panic!("Error getting the value in the thread local storage slot.");
            }
        } else {
            ptr as *mut T
        }
    }
}

unsafe impl<T> Send for ThreadLocal<T> {}
unsafe impl<T> Sync for ThreadLocal<T> {}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    use std::thread;

    use super::*;

    struct ThreadLocalResource<'a> {
        reference: &'a AtomicUsize,
        value: usize,
    }

    impl<'a> ThreadLocalResource<'a> {
        fn new(reference: &'a AtomicUsize, value: usize) -> Self {
            reference.fetch_add(1, Ordering::SeqCst);
            Self { reference, value }
        }

        fn load(&self) -> (usize, usize) {
            (self.reference.load(Ordering::SeqCst), self.value)
        }
    }

    impl<'a> Drop for ThreadLocalResource<'a> {
        fn drop(&mut self) {
            self.reference.fetch_sub(1, Ordering::SeqCst);
        }
    }

    #[test]
    fn single_thread() {
        let mut counter = AtomicUsize::new(0);

        let mut t = ThreadLocal::<ThreadLocalResource>::new();

        assert!(t.try_as_ref().is_none());
        assert!(t.try_as_mut().is_none());

        t.store(ThreadLocalResource::new(&mut counter, 7));
        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.try_as_ref().is_some());
        assert!(t.try_as_mut().is_some());

        assert_eq!(t.as_ref().load(), (1, 7));
        assert_eq!(t.as_mut().load(), (1, 7));

        t.take();

        assert_eq!(counter.load(Ordering::SeqCst), 0);

        assert!(t.try_as_ref().is_none());
        assert!(t.try_as_mut().is_none());

        t.free_index();
    }

    #[test]
    fn multiple_threads() {
        let counter = Arc::new(AtomicUsize::new(0));

        let mut t = ThreadLocal::<ThreadLocalResource>::new();

        assert!(t.try_as_ref().is_none());
        assert!(t.try_as_mut().is_none());

        t.store(ThreadLocalResource::new(&*counter, 7));

        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.try_as_ref().is_some());
        assert!(t.try_as_mut().is_some());

        assert_eq!(t.as_ref().load(), (1, 7));
        assert_eq!(t.as_mut().load(), (1, 7));

        let counter_clone = counter.clone();
        let t_clone = t.clone();
        let thread = thread::spawn(move || {
            t_clone.store(ThreadLocalResource::new(&*counter_clone, 9));
            assert_eq!(counter_clone.load(Ordering::SeqCst), 2);

            assert!(t_clone.try_as_ref().is_some());
            assert!(t_clone.try_as_mut().is_some());

            assert_eq!(t_clone.as_ref().load(), (2, 9));
            assert_eq!(t_clone.as_mut().load(), (2, 9));

            t_clone.take();

            assert_eq!(counter_clone.load(Ordering::SeqCst), 1);

            assert!(t_clone.try_as_ref().is_none());
            assert!(t_clone.try_as_mut().is_none());
        });

        thread.join().unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.try_as_ref().is_some());
        assert!(t.try_as_mut().is_some());

        assert_eq!(t.as_ref().load(), (1, 7));
        assert_eq!(t.as_mut().load(), (1, 7));

        t.take();

        assert_eq!(counter.load(Ordering::SeqCst), 0);

        assert!(t.try_as_ref().is_none());
        assert!(t.try_as_mut().is_none());

        t.free_index();
    }
}
