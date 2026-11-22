//! TLC core: values, evaluation, configuration, built-in modules, messages.
//!
//! Java packages -> Rust modules (fill in as you port; keep `docs/JAVA_MAP.md` in sync):
//!   tlc2.output.EC, EC.ExitStatus                 -> `ec` (done, generated)
//!   tlc2.output.MP                                -> `mp` (framing done; templates as needed)
//!   tlc2.TLC (handleParameters)                   -> `options` (+ tlc-cli)
//!   tlc2.value.*, tlc2.value.impl.*               -> `value` (Value enum, ordering, printing, FP64 fingerprints)
//!   tlc2.tool.impl.ModelConfig, tlc2.tool.impl.ModelConfig lexer -> `config` (.cfg parser)
//!   tlc2.tool.impl.SpecProcessor, Spec            -> `spec` (constants, overrides, definitions, ASSUME)
//!   tlc2.tool.impl.Tool (eval, getInitStates, getNextStates, enabled) -> `eval`
//!   tlc2.tool.TLCState(Mut), Action, StateVec     -> `state`
//!   tlc2.module.* (Naturals, Integers, Sequences, FiniteSets, Bags, TLC, TLCExt, Randomization, Json, ...)
//!                                                 -> `stdmod`
//!   CommunityModules tlc2.overrides.* (reference/community-modules/modules/tlc2/overrides) -> `community`

pub mod actions;
pub mod compile;
pub mod config;
pub mod ec;
pub mod eval;
pub mod liveness;
pub mod ir;
pub mod jrandom;
pub mod natives;
pub mod mp;
pub mod options;
pub mod pprint;
pub mod spec;
pub mod symmetry;
pub mod value;

pub use mp::Reporter;
pub use options::TlcOptions;
