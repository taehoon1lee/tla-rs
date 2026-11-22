# TASKS — TLC/SANY (Java) → Rust port

Work top to bottom. One `[ ]` per iteration. Split big tasks into sub-bullets when you start them.
Each milestone ends with a harness acceptance criterion; a milestone is done when it is met.
Scores come from `python harness/check.py` (see CLAUDE.md). Java paths are relative to
`reference/tlaplus/tlatools/org.lamport.tlatools/` (abbrev: `TT`; `S` = `TT/src`).

## M0 — Environment (done by the environment builder)
- [x] Java oracle (TLC 1.8.0 `-tool`, SANY full and `-s`), goldens, corpus (1140 SANY modules, 384 TLC models),
      judge, loop driver
- [x] Rust workspace skeleton; CLI implements the protocol; `Resolver` (module lookup), embedded StandardModules,
      `tlc_core::ec` (all EC codes + exit-status mapping), `mp::Reporter` (tool-mode framing)

## M1 — SANY lexer + parser (crate `tla-sany`)
Reference: `TT/javacc/tla+.jj` (READ THIS, not the generated TLAplusParser.java), `S/tla2sany/parser/{Operators,
OperatorStack,JunctionListContext,SyntaxTreeNode,Token}.java`, `S/tla2sany/st/SyntaxTreeConstants.java` (N_* kinds).
- [ ] M1.1 Lexer (`lexer.rs`): all TOKEN/SPECIAL_TOKEN rules of tla+.jj — module begin `----+ MODULE`, end `====+`,
      identifiers, numbers (`123`, `\b101`, `\o17`, `\h1F`, `1.5`), strings with escapes, comments (`\*`, nested
      `(* *)`), every operator in ASCII form and its synonyms, `WF_`/`SF_`, `<<`/`>>`, `_`, `@`, `!`, `::`, prime,
      keywords. Positions (line, col) 1-based like SANY. Unit test that lexes every `reference/**/*.tla` without error.
- [ ] M1.2 Syntax tree (`syntax.rs`): arena of nodes with kinds named after `SyntaxTreeConstants` (N_Module,
      N_OperatorDefinition, N_InfixExpr, N_ConjList, ...) + source span (begin/end line+col, needed for messages
      and TLC action labels `line L, col C to line L2, col C2 of module M`).
- [ ] M1.3 Expression parser: precedence/associativity from `Operators.java` + `OperatorStack.java` (SANY resolves
      precedence AFTER parsing with an operator stack — mirror it), junction lists by column (`JunctionListContext`),
      IF/CASE/LET, quantifiers (bounded/unbounded, tuples `\E <<x, y>> \in S`), CHOOSE, set/function/record
      constructors, `[S -> T]`, `[a : S]`, EXCEPT (`!.a`, `![i]`, `@`), tuples, `[A]_v`, `<<A>>_v`, WF/SF, ENABLED,
      UNCHANGED, `\cdot`, instance refs `I!Op(x)`, labels `l::`, LAMBDA, `-.` prefix minus. Unit tests of tricky trees.
- [ ] M1.4 Module units: EXTENDS, CONSTANT(S) (incl. `F(_, _)`, `_ ++ _`), VARIABLE(S), operator/infix/function
      definitions, RECURSIVE, LOCAL, INSTANCE ... WITH, `I == INSTANCE`, ASSUME/AXIOM, THEOREM/LEMMA/COROLLARY with
      full proof syntax (many Examples carry TLAPS proofs: `<1>1.`, `BY`, `OBVIOUS`, `QED`, `SUFFICES`, `PICK`,
      `USE`, `HIDE`, `DEFINE`...), nested modules, `----` separators.
- [ ] M1.5 `sany -s` (parse only, Java `SANY -s`): load EXTENDS/INSTANCE modules recursively through `Resolver`,
      print one `Parsing file <path>` line per file in Java's discovery order (`modanalyzer/SpecObj.java`), exit codes
      and markers as Java for syntax errors (`***Parse Error***`, `Fatal errors`, `Could not parse module`, exit -1;
      missing modules: `Cannot find source file for module`).
      Acceptance: **syntax ≥ 1130/1140** (`python harness/check.py --kind parse`, level `syntax`).

## M2 — SANY modules, semantic analysis, level checking (parse level parity)
Reference: `S/tla2sany/drivers/SANY.java` (frontEndMain, output lines), `S/tla2sany/modanalyzer/{SpecObj,ParseUnit}.java`
(load order, "Parsing file", missing modules, cycles), `S/tla2sany/semantic/Generator.java` (symbol resolution,
~10k lines: read by grep), `Context.java`, `ModuleNode.java`, `OpDefNode.java`, `SymbolTable.java`, `Errors.java`,
`LevelNode.java` (levelCheck), `BuiltInOperators.java`.
- [ ] M2.1 `sany_main`/`frontend` print "Parsing file …" / "Semantic processing of module X" / "Linting of module X"
      in Java's order; missing module → Java's "Cannot find source file for module" report and exit code.
- [ ] M2.2 Semantic graph: modules, EXTENDS merge, CONSTANT/VARIABLE decls, OpDef with arity & params (incl.
      higher-order), built-ins, LET, INSTANCE substitution (implicit `x <- x`), LOCAL, RECURSIVE, theorems/assumptions,
      proof step names. Resolves every name; arity checks.
- [ ] M2.3 Semantic errors exactly like Java: `Semantic errors:` / `*** Errors: N` / `line L, col C to line L2, col C2
      of module M` / message (unknown operator, multiply-defined symbol, arity mismatch ...).
- [ ] M2.4 Level checking (constant / state / action / temporal) + level errors as Java.
- [ ] M2.5 Acceptance: **parse ≥ 1135/1140** (`python harness/check.py --kind parse`).

## M3 — Values (crate `tlc-core`, module `value`)
Reference: `S/tlc2/value/impl/*.java` (Value.java, BoolValue, IntValue, StringValue, ModelValue, SetEnumValue,
IntervalValue, TupleValue, RecordValue, FcnRcdValue, FcnLambdaValue, SetOfFcnsValue, SetOfRcdsValue,
SetOfTuplesValue, SubsetValue, UnionValue, SetCupValue, SetCapValue, SetDiffValue, SetPredValue, LazyValue),
`S/tlc2/value/Values.java`, `S/util/UniqueString.java`, `S/tlc2/util/FP64.java`.
- [ ] M3.1 `Value` enum (cheap clone) for all kinds above; enumerable lazy sets; `member`, `size`, `normalize`.
- [ ] M3.2 `compareTo` identical to Java (ints numerically; strings/model values by UniqueString INTERN ORDER, see
      NOTES; sets by size then elements; ...): needed for set normalization, printing order and CHOOSE.
- [ ] M3.3 Printing identical to Java (`toString`/`PrettyPrint`, used in state prints): `{1, 2}`, `<<1, 2>>`,
      `[a |-> 1]`, `(1 :> 2 @@ 3 :> 4)`, strings, model values, nested multi-line layout (spaces matter after `(`/`[`).
- [ ] M3.4 Fingerprints only if needed (Rust may use its own hash for the state set).

## M4 — Config, spec processing, evaluator, initial states (front + init levels)
Reference: `S/tlc2/tool/impl/ModelConfig.java` (.cfg grammar), `SpecProcessor.java` (constants, overrides,
ASSUME, SPECIFICATION analysis), `Spec.java`, `Tool.java` (eval, getInitStates), `S/tlc2/module/*.java`
(Naturals, Integers, Sequences, FiniteSets, Bags, TLC, TLCExt, Randomization, Json, Strings, TransitiveClosure),
`S/tlc2/TLC.java` (`process()`: what is printed in which order).
- [ ] M4.1 .cfg parser: CONSTANT(S) `c = v` / `c <- op` / model values / sets of model values, `c <- [M] op`, INIT,
      NEXT, SPECIFICATION, INVARIANT(S), PROPERTY/PROPERTIES, CONSTRAINT(S), ACTION_CONSTRAINT(S), SYMMETRY, VIEW,
      ALIAS, POSTCONDITION, CHECK_DEADLOCK; comments; errors (CFG_* codes → exit 151).
- [ ] M4.2 TLC `process()` skeleton with Java's message order (2262, 2187, 2220/2219 around SANY, 2185, 2189 ...) and
      config/spec errors (TLC_CONFIG_* → exit 151, parse errors → 3002 + exit 150).
- [ ] M4.3 Constant-level evaluator: literals, arithmetic (Int is 32-bit with TLC's overflow error), sets, functions,
      records, tuples, sequences, strings, quantifiers, CHOOSE (first in normalized order), IF/CASE/LET, recursion,
      INSTANCE substitution, higher-order operators, LAMBDA; ASSUME evaluation (2104 / exit 10).
- [ ] M4.4 Initial states (`Tool.getInitStates`): conjunct-by-conjunct enumeration exactly like Java (`x \in S`,
      `x = e`, disjunctions, `\E`, IF, LET, operator calls), "not completely specified" errors (2106).
      Acceptance: **init ≥ 90% of models**.

## M5 — BFS model checking: safety verdicts
Reference: `S/tlc2/tool/impl/Tool.java` (getNextStates, isInModel/constraints, enabled), `S/tlc2/tool/ModelChecker.java`,
`AbstractChecker.java`, `Worker.java`, `TLCTrace.java`, `S/tlc2/output/StatePrinter.java`, `MP.java` templates.
- [ ] M5.1 Next-state generation (`getNextStates`) with primed variables, `x' \in S`, UNCHANGED, action splitting
      into named sub-actions (labels for traces), action constraints.
- [ ] M5.2 BFS: state set + FIFO queue, statistics (2199 / 2194 / 2268 outdegree), success message 2193, CONSTRAINT.
- [ ] M5.3 Invariants (2107 initial / 2110 behavior), deadlock (2114), `-continue`, `-deadlock`, CHECK_DEADLOCK.
- [ ] M5.4 Counterexample traces: 2121 + one 2217 per state (`N: <Action line L, col C to line L2, col C2 of module M>`
      / `<Initial predicate>`), shortest path reconstruction like `TLCTrace`.
- [ ] M5.5 Evaluation errors during init/next/invariants (1000 + 2103 nested positions, exit 75/76) like Java.
      Acceptance: **verdict ≥ 90% of models without PROPERTY**.

## M6 — Liveness (PROPERTY, fairness) and action properties
Reference: `S/tlc2/tool/liveness/{Liveness,LiveCheck,LiveWorker,OrderOfSolution,TBGraph,TBPar,Tableau*}.java`.
- [ ] M6.1 Temporal formula processing: `Liveness.processLiveness` (fairness WF/SF, `[]<>`, `<>[]`, `~>`, tableau for
      general formulas), errors for unsupported formulas (2213/2214 ...).
- [ ] M6.2 Behavior graph during BFS + SCC check at the end (`-lncheck final`), lasso counterexample
      (2116, 2264, 2217..., 2122 back-to-state / 2218 stuttering).
- [ ] M6.3 Action properties `[][A]_v` in PROPERTY (2112) checked during BFS like Java.
      Acceptance: **verdict ≥ 90% of all models**.

## M7 — Remaining features
- [ ] M7.1 SYMMETRY (`Permutations`, canonical representative like `TLCStateMut.generateSymmetricStates`), VIEW, ALIAS.
- [ ] M7.2 TLCGet/TLCSet, Print/PrintT order, Assert (exit 14), POSTCONDITION, `-inv`, `-maxSetSize`, warnings.
- [ ] M7.3 Community modules used by the corpus (Functions, SequencesExt, FiniteSetsExt, Folds, IOUtils, CSV, SVG,
      Bitwise, ...): evaluate their TLA+ definitions where TLC does, port the Java overrides
      (`reference/community-modules/modules/tlc2/overrides/*.java`) where TLC uses them.
- [ ] M7.4 Acceptance: **verdict == all scored models** (drive the failure list to 0).

## M8 — Exact output parity (trace + parse_msg levels)
- [ ] M8.1 Trace level: identical counterexamples (requires Java's exact successor enumeration order), error texts,
      Print output, warnings, statistics at the moment of the violation.
- [ ] M8.2 parse_msg level: SANY error text (incl. JavaCC-style "Was expecting ... Encountered ..." reports).

## M9 — Performance (Rust must not be slower than Java)
- [ ] M9.1 Profile the slowest models (`--perf`, top of the perf failure list); compact state representation,
      hashing, interning, avoid re-evaluating constant expressions (Java precomputes constant definitions).
- [ ] M9.2 `--heavy` models (Java > 60 s) pass verdict and perf.
- [ ] M9.3 Acceptance: **perf == verdict**.
