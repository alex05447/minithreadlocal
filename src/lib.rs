//! # minifiber
//!
//! Thin wrapper around the Windows thread local API.
//!
//! Technically provides a portable API, but implemented only for Windows at the moment.
//!
//! See [`Thread Local Storage`](https://docs.microsoft.com/en-us/windows/win32/procthread/thread-local-storage) on MSDN for the description of the concept.
//!
//! Run `cargo --doc` for documentation.
//!
//! Uses [`winapi`](https://docs.rs/winapi/0.3.8/winapi/).

mod thread_local;

pub use thread_local::ThreadLocal;
