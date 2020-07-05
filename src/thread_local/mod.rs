#[cfg(windows)]
mod win;

#[cfg(windows)]
pub use win::{ThreadLocal, ThreadLocalError};
