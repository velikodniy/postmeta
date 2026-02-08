//! Filesystem abstraction for WASM compatibility.
//!
//! The `MetaPost` interpreter needs to read files (for `input` commands),
//! but must not access the filesystem directly for WASM compatibility.
//! This trait abstracts file reading so that different implementations
//! can be provided:
//! - `OsFileSystem` in the CLI crate (reads from disk)
//! - A virtual filesystem for WASM (files provided in-memory)

/// A filesystem abstraction for reading source files.
///
/// Implementations must resolve file names (possibly adding `.mp` extension)
/// and return file contents as strings.
pub trait FileSystem {
    /// Read a file by name, returning its contents.
    ///
    /// The implementation should:
    /// 1. Try the exact filename first
    /// 2. If not found, try appending `.mp`
    /// 3. Search in configured directories
    ///
    /// Returns `None` if the file cannot be found.
    fn read_file(&self, name: &str) -> Option<String>;
}

/// A no-op filesystem that never finds any files.
///
/// Used as the default when no filesystem is configured (e.g., in tests).
pub struct NullFileSystem;

impl FileSystem for NullFileSystem {
    fn read_file(&self, _name: &str) -> Option<String> {
        None
    }
}
