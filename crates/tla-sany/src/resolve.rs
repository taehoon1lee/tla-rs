//! Port of `util/SimpleFilenameToStream.java` (+ `util/*ResourceLocator.java`): where a module's source comes from.
//!
//! Java search order (`SimpleFilenameToStream.locate`):
//!   1. the user directory (`ToolIO.getUserDir()`: TLC sets it to the spec's directory; standalone SANY leaves it
//!      unset, so the process working directory is used)
//!   2. `-DTLA-Library` paths (unused by the harness)
//!   3. the standard modules inside tla2tools.jar (`tla2sany/StandardModules/`)  -> [`crate::stdlib`]
//!   4. the bare classpath, in classpath order (CommunityModules-deps.jar, reference/tla-library)
//!      -> the CLI's `--lib DIR` options, in the order given
//! Modules found in 3. or 4. are "library" modules (Java: `TLAFile.isLibraryModule()`).

use std::path::{Path, PathBuf};

/// Where a module was found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Origin {
    /// A file on disk in the user directory (or a TLA-Library path).
    User(PathBuf),
    /// One of the embedded standard modules.
    Standard,
    /// A file in one of the `--lib` directories (Java: a classpath resource).
    Library(PathBuf),
}

#[derive(Debug, Clone)]
pub struct Located {
    pub module: String,
    pub origin: Origin,
    pub source: String,
}

impl Located {
    /// Java `TLAFile.isLibraryModule()`.
    pub fn is_library_module(&self) -> bool {
        !matches!(self.origin, Origin::User(_))
    }
}

#[derive(Debug, Clone, Default)]
pub struct Resolver {
    pub user_dir: PathBuf,
    pub tla_library: Vec<PathBuf>,
    pub lib_dirs: Vec<PathBuf>,
}

impl Resolver {
    pub fn new(user_dir: impl Into<PathBuf>, lib_dirs: Vec<PathBuf>) -> Self {
        Resolver { user_dir: user_dir.into(), tla_library: Vec::new(), lib_dirs }
    }

    /// Java `SimpleFilenameToStream.resolve(name, isModule=true)`: `module` is a module name without `.tla`.
    pub fn locate(&self, module: &str) -> Option<Located> {
        let file = format!("{module}.tla");
        let read = |p: &Path| std::fs::read(p).ok().map(|b| String::from_utf8_lossy(&b).into_owned());
        for dir in std::iter::once(&self.user_dir).chain(self.tla_library.iter()) {
            let p = dir.join(&file);
            if p.is_file() {
                if let Some(src) = read(&p) {
                    return Some(Located { module: module.to_string(), origin: Origin::User(p), source: src });
                }
            }
        }
        if let Some(src) = crate::stdlib::standard_module(module) {
            return Some(Located { module: module.to_string(), origin: Origin::Standard, source: src.to_string() });
        }
        for dir in &self.lib_dirs {
            let p = dir.join(&file);
            if p.is_file() {
                if let Some(src) = read(&p) {
                    return Some(Located { module: module.to_string(), origin: Origin::Library(p), source: src });
                }
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn standard_modules_are_found_after_user_dir() {
        let r = Resolver::new(std::env::temp_dir().join("tla-sany-no-such-dir"), vec![]);
        let n = r.locate("Naturals").expect("Naturals is embedded");
        assert_eq!(n.origin, Origin::Standard);
        assert!(n.is_library_module());
        assert!(n.source.contains("MODULE Naturals"));
        assert!(r.locate("NoSuchModule").is_none());
    }
}
