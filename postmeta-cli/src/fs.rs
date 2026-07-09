//! Filesystem access: disk-backed [`FileSystem`] and source reading

use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::PathBuf;

use postmeta_core::filesystem::FileSystem;

use crate::args::Cli;

/// Filesystem implementation that reads from disk
///
/// Searches configured directories, trying the exact name first, then `.mp` appended.
pub struct OsFileSystem {
    search_dirs: Vec<PathBuf>,
    /// Open file readers for `readfrom`
    read_files: HashMap<String, std::io::Lines<BufReader<fs::File>>>,
}

impl OsFileSystem {
    pub fn new(search_dirs: Vec<PathBuf>) -> Self {
        Self {
            search_dirs,
            read_files: HashMap::new(),
        }
    }
}

impl FileSystem for OsFileSystem {
    fn read_file(&self, name: &str) -> Option<String> {
        let candidates = [name.to_owned(), format!("{name}.mp")];

        for dir in &self.search_dirs {
            for candidate in &candidates {
                let path = dir.join(candidate);
                if let Ok(contents) = fs::read_to_string(&path) {
                    return Some(contents);
                }
            }
        }
        None
    }

    fn read_line(&mut self, name: &str) -> Option<String> {
        if !self.read_files.contains_key(name) {
            let candidates = [name.to_owned(), format!("{name}.mp")];
            let mut file = None;
            for dir in &self.search_dirs {
                for candidate in &candidates {
                    let path = dir.join(candidate);
                    if let Ok(f) = fs::File::open(&path) {
                        file = Some(f);
                        break;
                    }
                }
                if file.is_some() {
                    break;
                }
            }
            if file.is_none() {
                if let Ok(f) = fs::File::open(name) {
                    file = Some(f);
                }
            }

            if let Some(f) = file {
                self.read_files
                    .insert(name.to_owned(), BufReader::new(f).lines());
            } else {
                return None;
            }
        }

        let lines = self.read_files.get_mut(name)?;
        match lines.next() {
            Some(Ok(line)) => Some(line),
            _ => Some("\0".to_string()),
        }
    }

    fn write_line(&mut self, name: &str, text: &str) -> Result<(), std::io::Error> {
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(name)?;
        writeln!(file, "{text}")
    }
}

/// Read the program source from `--eval` or the input file
///
/// Prints an error to stderr and returns `None` if no source is available.
pub fn read_source(cli: &Cli) -> Option<String> {
    if let Some(ref expr) = cli.eval {
        return Some(expr.clone());
    }
    if let Some(ref file) = cli.file {
        match fs::read_to_string(file) {
            Ok(s) => return Some(s),
            Err(e) => {
                eprintln!("Error reading {file}: {e}");
                return None;
            }
        }
    }
    eprintln!("No input file or expression specified");
    None
}
