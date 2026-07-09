//! Filesystem abstraction for WASM compatibility
//!
//! The interpreter reads files for `input` but must not touch the OS filesystem directly.
//! Implementations: `OsFileSystem` in the CLI crate (disk) and an in-memory virtual filesystem for WASM.

/// A filesystem abstraction for reading source files
///
/// Implementations resolve file names (possibly appending `.mp`) and return contents as strings.
pub trait FileSystem {
    /// Read a file by name, returning its contents
    ///
    /// The implementation should:
    /// 1. Try the exact filename first
    /// 2. If not found, try appending `.mp`
    /// 3. Search in configured directories
    ///
    /// Returns `None` if the file cannot be found.
    fn read_file(&self, name: &str) -> Option<String>;

    /// Read a single line from an opened file
    ///
    /// Returns `None` at EOF or if unsupported.
    fn read_line(&mut self, _name: &str) -> Option<String> {
        None
    }

    /// Write a string to a file, opening or appending to it
    ///
    /// # Errors
    /// Returns an error if the underlying filesystem fails to write the data.
    fn write_line(&mut self, _name: &str, _text: &str) -> Result<(), std::io::Error> {
        Ok(())
    }
}

/// A no-op filesystem that never finds any files
///
/// The default when no filesystem is configured (e.g. in tests).
pub struct NullFileSystem;

impl FileSystem for NullFileSystem {
    fn read_file(&self, _name: &str) -> Option<String> {
        None
    }
}
