# Java → Rust map

Roots: `TT` = `reference/tlaplus/tlatools/org.lamport.tlatools`, `S` = `TT/src`,
`CM` = `reference/community-modules/modules`. Sizes are Java line counts (to plan how many iterations a port
takes). Update the Rust column as you go.

## SANY front-end → `crates/tla-sany`
| Java | lines | Rust | notes |
|---|---|---|---|
| `TT/javacc/tla+.jj` | 4417 | `lexer.rs`, `parser.rs` | THE grammar (tokens at the top, productions below). `S/tla2sany/parser/TLAplusParser.java` (10790) is generated from it |
| `S/tla2sany/parser/Operators.java`, `Operator.java`, `OperatorStack.java` | ~900 | `parser.rs` | precedence ranges + associativity, resolved with an operator stack after parsing |
| `S/tla2sany/parser/JunctionListContext.java` | | `parser.rs` | column-aligned `/\` `\/` bullet lists |
| `S/tla2sany/parser/SyntaxTreeNode.java` | 835 | `syntax.rs` | syntax tree; kinds in `S/tla2sany/st/SyntaxTreeConstants.java` |
| `S/tla2sany/drivers/SANY.java` | 774 | `lib.rs` | `frontEndMain`, `SANYmain`, which lines are printed, exit codes (`SanyExitCode.java`) |
| `S/tla2sany/modanalyzer/SpecObj.java`, `ParseUnit.java` | 1104+693 | `modules.rs` | module loading, dependency order, "Parsing file", missing modules |
| `S/tla2sany/semantic/Generator.java` | 9736 | `semantic/*.rs` | syntax tree → semantic graph (name resolution, arity, instances) |
| `S/tla2sany/semantic/{Context,SymbolTable,ExternalModuleTable}.java` | ~1100 | `semantic/` | scopes |
| `S/tla2sany/semantic/{ModuleNode,OpDefNode,OpApplNode,OpDeclNode,SubstInNode,InstanceNode,LetInNode,...}.java` | ~7000 | `semantic/` | semantic node kinds |
| `S/tla2sany/semantic/LevelNode.java`, `LevelConstants.java`, `BuiltInOperators.java` | 2787+ | `semantic/level.rs` | level checking |
| `S/tla2sany/semantic/Errors.java`, `ErrorCode.java` | ~480 | `error.rs` | error report format |
| `S/tla2sany/linter/Linter.java` | 201 | | "Linting of module" (warnings) |
| `S/util/SimpleFilenameToStream.java` (+ `*ResourceLocator`) | | `resolve.rs` | DONE: module lookup order |
| `S/util/UniqueString.java`, `InternTable.java` | | `intern.rs` | interned names; `tok` order = comparison order of strings in TLC! |
| `S/tla2sany/StandardModules/*.tla` | | `lib/*.tla`, `stdlib.rs` | DONE: embedded |

## TLC → `crates/tlc-core`
| Java | lines | Rust | notes |
|---|---|---|---|
| `S/tlc2/output/EC.java` | | `ec.rs` | DONE (generated): all codes + `ExitStatus.errorConstantToExitStatus` |
| `S/tlc2/output/MP.java` | 2039 | `mp.rs` | DONE framing; message templates (`getMessage0` switch) port as needed |
| `S/tlc2/output/StatePrinter.java` | 152 | `mp.rs`/`state.rs` | how 2217 state messages are built |
| `S/tlc2/TLC.java` | 1982 | `options.rs` + tlc-check `run` | `handleParameters` (flags), `process()` (phase order) |
| `S/tlc2/tool/impl/ModelConfig.java` | 832 | `config.rs` | .cfg grammar + errors |
| `S/tlc2/tool/impl/SpecProcessor.java`, `Spec.java` | 2516+749 | `spec.rs` | constants, overrides, defns, ASSUME, Init/Next/temporal extraction |
| `S/tlc2/tool/impl/Tool.java` | 4136 | `eval/*.rs` | eval, getInitStates, getNextStates, enabled, isInModel |
| `S/tlc2/tool/{TLCState,TLCStateMut,Action,StateVec}.java` | ~800 | `state.rs` | |
| `S/tlc2/value/impl/*.java` | 14430 | `value/*.rs` | all value kinds: compareTo, member, normalize, toString, fingerprint |
| `S/tlc2/value/Values.java`, `S/tlc2/util/FP64.java` | | `value/` | `ppr` pretty printer, fingerprints |
| `S/tlc2/module/{Naturals,Integers,Sequences,FiniteSets,Bags,TLC,TLCExt,TLCGetSet,Randomization,Json,Strings,TransitiveClosure}.java` | 4673 | `stdmod/*.rs` | built-in overrides of standard modules |
| `CM/tlc2/overrides/*.java` | | `community/*.rs` | CommunityModules overrides (Functions, SequencesExt, FiniteSetsExt, IOUtils, ...) |

## Model checker → `crates/tlc-check`
| Java | lines | Rust | notes |
|---|---|---|---|
| `S/tlc2/tool/ModelChecker.java`, `AbstractChecker.java`, `Worker.java` | 1264+742+678 | `bfs.rs` | BFS, invariants, deadlock, statistics, success message |
| `S/tlc2/tool/fp/*`, `S/tlc2/tool/queue/*` | | `fpset.rs`, `queue.rs` | in-memory structures are fine |
| `S/tlc2/tool/TLCTrace.java` | 573 | `trace.rs` | counterexample reconstruction |
| `S/tlc2/tool/liveness/*` | 12403 | `liveness/*.rs` | Liveness (formula processing), LiveCheck/LiveWorker (SCC), TBGraph/Tableau |
| `S/tlc2/tool/impl/SymmetryTable`, `TLCStateMut` (symmetry), `S/tlc2/tool/coverage` | | | symmetry; coverage is not needed |
