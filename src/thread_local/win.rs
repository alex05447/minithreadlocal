use {
    std::{
        error::Error,
        fmt::{Display, Formatter},
        io,
        marker::PhantomData,
        ptr,
    },
    winapi::{
        shared::{minwindef::DWORD, winerror::ERROR_SUCCESS},
        um::{
            errhandlingapi::GetLastError,
            processthreadsapi::{TlsAlloc, TlsFree, TlsGetValue, TlsSetValue, TLS_OUT_OF_INDEXES},
        },
    },
};

#[derive(Debug)]
pub enum ThreadLocalError {
    /// Failed to create the thread local storage index.
    /// Contains the OS error.
    FailedToCreate(io::Error),
    /// Tried to store the value into an occupied thread local slot.
    ThreadLocalSlotOccupied,
    /// Tried to use the thread local index after it was freed.
    UseAfterFree,
    /// Failed to store the value into the thread local slot.
    /// Contains the OS error.
    FailedToStore(io::Error),
    /// Failed to retrieve a value from the thread local slot.
    /// Contains the OS error.
    FailedToGet(io::Error),
    /// Leaked a thread local value in the finalizing thread.
    ObjectLeaked,
    /// Failed to free the thread local storage index.
    /// Contains the OS error.
    FailedToFree(io::Error),
}

impl Error for ThreadLocalError {}

impl Display for ThreadLocalError {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        use ThreadLocalError::*;

        match self {
            FailedToCreate(err) => write!(
                f,
                "failed to create the thread local storage index: {}",
                err
            ),
            ThreadLocalSlotOccupied => {
                "tried to store the value into an occupied thread local slot".fmt(f)
            }
            UseAfterFree => "tried to use the thread local index after it was freed".fmt(f),
            FailedToStore(err) => write!(f, "failed to store the value into the thread local slot: {}", err),
            FailedToGet(err) => write!(f, "failed to retrieve a value from the thread local slot: {}", err),
            ObjectLeaked => "leaked a thread local value in the finalizing thread".fmt(f),
            FailedToFree(err) => {
                write!(f, "failed to free the thread local storage index: {}", err)
            }
        }
    }
}

/// Low-level OS thread local storage abstraction with minimal safety guarantees.
///
/// This is a POD object that may be safely copied / cloned, passed to and used by multiple threads.
///
/// However, the user must ensure the following:
/// 1) each thread which called [`store`] on the `ThreadLocal` object must call [`take`] to drop the stored value and reclaim allocated memory;
/// 2) [`free_index`] must be called only once, from one thread, after last use of the `ThreadLocal` object by any thread
/// to free the internal thread local storage index.
///
/// [`store`]: #method.store
/// [`take`]: #method.take
/// [`free_index`]: #method.free_index
pub struct ThreadLocal<T> {
    index: DWORD,
    _marker: PhantomData<T>,
}

impl<T> Copy for ThreadLocal<T> {}

impl<T> Clone for ThreadLocal<T> {
    fn clone(&self) -> Self {
        Self {
            index: self.index,
            _marker: PhantomData,
        }
    }
}

impl<T> ThreadLocal<T> {
    /// Creates a new empty thread local storage object.
    /// Allocates an OS thread local storage index the object will use to store values.
    ///
    /// # Errors
    ///
    /// Returns an error if the OS runs out of TLS indices. The upper limit depends on the OS version.
    /// It's not recommended to create more than a handful of `ThreadLocal` objects.
    pub fn new() -> Result<Self, ThreadLocalError> {
        let index = unsafe { TlsAlloc() };

        if index == TLS_OUT_OF_INDEXES {
            Err(ThreadLocalError::FailedToCreate(io::Error::last_os_error()))
        } else {
            Ok(Self {
                index,
                _marker: PhantomData,
            })
        }
    }

    /// Takes ownership of the provided value, boxes it and stores it in this thread's local slot.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    /// Returns an error if the thread's slot was already occupied by a previous call to [`store`].
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn store(&self, t: T) -> Result<(), ThreadLocalError> {
        if !self.get_ptr()?.is_null() {
            return Err(ThreadLocalError::ThreadLocalSlotOccupied);
        }

        self.store_impl(t).map(|_| ())
    }

    /// Tries to retrieve the value stored in this thread's local slot by a previous call to [`store`].
    ///
    /// On success returns `Some` and clears the slot, allowing [`store`] to be called again.
    /// Returns `None` if the slot is empty.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn take(&self) -> Result<Option<T>, ThreadLocalError> {
        let ptr = self.get_ptr()?;

        if ptr.is_null() {
            Ok(None)
        } else {
            let boxed = unsafe { Box::from_raw(ptr) };
            self.set_ptr(ptr::null_mut())?;
            Ok(Some(*boxed))
        }
    }

    /// Like [`take`], but panics on error or if the thread local storage slot is empty.
    ///
    /// [`take`]: #method.take
    pub unsafe fn take_unchecked(&self) -> T {
        self.take().unwrap().unwrap()
    }

    /// Returns an immutable reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or `None` if the slot is empty.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn as_ref(&self) -> Result<Option<&T>, ThreadLocalError> {
        self.as_ref_impl()
    }

    /// Like [`as_ref`], but panics on error or if the thread local storage slot is empty.
    ///
    /// [`as_ref`]: #method.as_ref
    pub unsafe fn as_ref_unchecked(&self) -> &T {
        self.as_ref().unwrap().unwrap()
    }

    /// Returns an immutable reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or, if the slot is empty, [`store`]s a new value returned by `f` and returns a reference to it.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn as_ref_or<F: FnOnce() -> T>(&self, f: F) -> Result<&T, ThreadLocalError> {
        if let Some(val) = self.as_ref()? {
            Ok(val)
        } else {
            let ptr = self.store_impl(f())?;
            debug_assert!(!ptr.is_null());
            Ok(unsafe { &*ptr })
        }
    }

    /// Returns a mutable reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or `None` if the slot is empty.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn as_mut(&self) -> Result<Option<&mut T>, ThreadLocalError> {
        self.as_mut_impl()
    }

    /// Like [`as_mut`], but panics on error or if the thread local storage slot is empty.
    ///
    /// [`as_mut`]: #method.as_ref
    pub unsafe fn as_mut_unchecked(&self) -> &mut T {
        self.as_mut().unwrap().unwrap()
    }

    /// Returns a reference to the value stored in this thread's local slot by a previous call to [`store`],
    /// or, if the slot is empty, stores a new value returned by `f` and returns a mutable reference to it.
    ///
    /// # Errors
    ///
    /// Returns an error if [`free_index`] has been called on this `ThreadLocal`.
    ///
    /// [`store`]: #method.store
    /// [`free_index`]: #method.free_index
    pub fn as_mut_or<F: FnOnce() -> T>(&self, f: F) -> Result<&mut T, ThreadLocalError> {
        if let Some(val) = self.as_mut()? {
            Ok(val)
        } else {
            let ptr = self.store_impl(f())?;
            debug_assert!(!ptr.is_null());
            Ok(unsafe { &mut *ptr })
        }
    }

    /// Frees the thread's local storage slot, disallowing further use of the `ThreadLocal` object.
    /// Unsafe to call from multiple threads as the operation is not atomic.
    ///
    /// # Errors
    ///
    /// Returns an error if the thread local storage index was already freed by a previous call to `free_index`.
    /// Returns an error if the value stored in the thread's local slot was not retrieved and was leaked.
    /// Returns an error if the OS failed to free the index, possibly because of a thread-unsafe previous call to `free_index`.
    pub fn free_index(&mut self) -> Result<(), ThreadLocalError> {
        if self.index == TLS_OUT_OF_INDEXES {
            return Err(ThreadLocalError::UseAfterFree);
        }

        if !self.get_ptr()?.is_null() {
            return Err(ThreadLocalError::ObjectLeaked);
        }

        let res = unsafe { TlsFree(self.index) };

        if res == 0 {
            Err(ThreadLocalError::FailedToFree(io::Error::last_os_error()))
        } else {
            self.index = TLS_OUT_OF_INDEXES;
            Ok(())
        }
    }

    fn store_impl(&self, t: T) -> Result<*mut T, ThreadLocalError> {
        let boxed = Box::new(t);
        let ptr = Box::into_raw(boxed);
        self.set_ptr(ptr)?;
        Ok(ptr)
    }

    fn as_ref_impl(&self) -> Result<Option<&T>, ThreadLocalError> {
        let ptr = self.get_ptr()?;

        Ok(if !ptr.is_null() {
            Some(unsafe { &*ptr })
        } else {
            None
        })
    }

    fn as_mut_impl(&self) -> Result<Option<&mut T>, ThreadLocalError> {
        let ptr = self.get_ptr()?;

        Ok(if !ptr.is_null() {
            Some(unsafe { &mut *ptr })
        } else {
            None
        })
    }

    fn set_ptr(&self, ptr: *const T) -> Result<(), ThreadLocalError> {
        if self.index == TLS_OUT_OF_INDEXES {
            return Err(ThreadLocalError::UseAfterFree);
        }

        let res = unsafe { TlsSetValue(self.index, ptr as _) };

        if res == 0 {
            Err(ThreadLocalError::FailedToStore(io::Error::last_os_error()))
        } else {
            Ok(())
        }
    }

    fn get_ptr(&self) -> Result<*mut T, ThreadLocalError> {
        if self.index == TLS_OUT_OF_INDEXES {
            return Err(ThreadLocalError::UseAfterFree);
        }

        let ptr = unsafe { TlsGetValue(self.index) };

        if ptr == 0 as _ {
            if unsafe { GetLastError() } == ERROR_SUCCESS {
                Ok(ptr as _)
            } else {
                Err(ThreadLocalError::FailedToGet(io::Error::last_os_error()))
            }
        } else {
            Ok(ptr as _)
        }
    }
}

unsafe impl<T> Send for ThreadLocal<T> {}

#[cfg(test)]
mod tests {
    use {
        super::*,
        std::{
            sync::{
                atomic::{AtomicUsize, Ordering},
                Arc,
            },
            thread,
        },
    };

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
        let counter = AtomicUsize::new(0);

        let mut t = ThreadLocal::<ThreadLocalResource>::new().unwrap();

        assert!(t.as_ref().unwrap().is_none());
        assert!(t.as_mut().unwrap().is_none());

        t.store(ThreadLocalResource::new(&counter, 7)).unwrap();
        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.as_ref().unwrap().is_some());
        assert!(t.as_mut().unwrap().is_some());

        unsafe {
            assert_eq!(t.as_ref_unchecked().load(), (1, 7));
            assert_eq!(t.as_mut_unchecked().load(), (1, 7));
        }

        t.take().unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 0);

        assert!(t.as_ref().unwrap().is_none());
        assert!(t.as_mut().unwrap().is_none());

        let res = t
            .as_ref_or(|| ThreadLocalResource::new(&counter, 9))
            .unwrap();

        assert_eq!(res.load(), (1, 9));
        assert_eq!(res.load(), (1, 9));

        t.take().unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 0);

        assert!(t.as_ref().unwrap().is_none());
        assert!(t.as_mut().unwrap().is_none());

        t.free_index().unwrap();
    }

    #[test]
    fn multiple_threads() {
        let counter = Arc::new(AtomicUsize::new(0));

        let mut t = ThreadLocal::<ThreadLocalResource>::new().unwrap();

        assert!(t.as_ref().unwrap().is_none());
        assert!(t.as_mut().unwrap().is_none());

        t.store(ThreadLocalResource::new(&*counter, 7)).unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.as_ref().unwrap().is_some());
        assert!(t.as_mut().unwrap().is_some());

        unsafe {
            assert_eq!(t.as_ref_unchecked().load(), (1, 7));
            assert_eq!(t.as_mut_unchecked().load(), (1, 7));
        }

        let counter_clone = counter.clone();

        let thread = thread::spawn(move || {
            assert!(t.as_ref().unwrap().is_none());
            assert!(t.as_mut().unwrap().is_none());

            t.store(ThreadLocalResource::new(&*counter_clone, 9))
                .unwrap();
            assert_eq!(counter_clone.load(Ordering::SeqCst), 2);

            assert!(t.as_ref().unwrap().is_some());
            assert!(t.as_mut().unwrap().is_some());

            unsafe {
                assert_eq!(t.as_ref_unchecked().load(), (2, 9));
                assert_eq!(t.as_mut_unchecked().load(), (2, 9));
            }

            t.take().unwrap();

            assert_eq!(counter_clone.load(Ordering::SeqCst), 1);

            assert!(t.as_ref().unwrap().is_none());
            assert!(t.as_mut().unwrap().is_none());
        });

        thread.join().unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 1);

        assert!(t.as_ref().unwrap().is_some());
        assert!(t.as_mut().unwrap().is_some());

        unsafe {
            assert_eq!(t.as_ref_unchecked().load(), (1, 7));
            assert_eq!(t.as_mut_unchecked().load(), (1, 7));
        }

        t.take().unwrap();

        assert_eq!(counter.load(Ordering::SeqCst), 0);

        assert!(t.as_ref().unwrap().is_none());
        assert!(t.as_mut().unwrap().is_none());

        t.free_index().unwrap();
    }
}
