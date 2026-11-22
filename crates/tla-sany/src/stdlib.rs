//! The TLA+ standard modules shipped inside tla2tools.jar (`tla2sany/StandardModules/*.tla`, TLC 1.8.0).
//! Java resolves them after the user directory and before the bare classpath (see `resolve.rs`).

/// (module name, source text) for every embedded standard module.
pub const STANDARD_MODULES: &[(&str, &str)] = &[
    ("_CBORTrace", include_str!("../lib/_CBORTrace.tla")),
    ("_DotTrace", include_str!("../lib/_DotTrace.tla")),
    ("_JsonTrace", include_str!("../lib/_JsonTrace.tla")),
    ("_Possible", include_str!("../lib/_Possible.tla")),
    ("_TLAPlusCounterExample", include_str!("../lib/_TLAPlusCounterExample.tla")),
    ("_TLCActionTrace", include_str!("../lib/_TLCActionTrace.tla")),
    ("_TLCTESpec", include_str!("../lib/_TLCTESpec.tla")),
    ("_TLCTrace", include_str!("../lib/_TLCTrace.tla")),
    ("_TLCTracePlain", include_str!("../lib/_TLCTracePlain.tla")),
    ("Bags", include_str!("../lib/Bags.tla")),
    ("FiniteSets", include_str!("../lib/FiniteSets.tla")),
    ("Integers", include_str!("../lib/Integers.tla")),
    ("Json", include_str!("../lib/Json.tla")),
    ("Naturals", include_str!("../lib/Naturals.tla")),
    ("Randomization", include_str!("../lib/Randomization.tla")),
    ("Reals", include_str!("../lib/Reals.tla")),
    ("RealTime", include_str!("../lib/RealTime.tla")),
    ("Sequences", include_str!("../lib/Sequences.tla")),
    ("TLC", include_str!("../lib/TLC.tla")),
    ("TLCExt", include_str!("../lib/TLCExt.tla")),
    ("Toolbox", include_str!("../lib/Toolbox.tla")),
];

/// Source of the standard module `name` (without `.tla`), if TLC ships one.
pub fn standard_module(name: &str) -> Option<&'static str> {
    STANDARD_MODULES.iter().find(|(n, _)| *n == name).map(|(_, s)| *s)
}
