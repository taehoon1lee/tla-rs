# PROGRESS — append-only iteration log (max 6 lines per entry)

## 2026-11-22 M0 — environment built (Opus)
parse 0/1140, front 0, init 0, verdict 0, trace 0, perf 0 (Rust reports "not ported" everywhere)
next: M1.1 lexer

## 2026-11-22 M1+M2 — SANY lexer/parser/module loader/semantic analyzer (Opus-level session, Sonnet 5.5)
syntax 1140/1140, parse 1132/1140, parse_msg 1126/1140 (all 436 ex/ modules pass; remaining = tt/ error-message cases), front 1, init 1, verdict 1
code: crates/tla-sany/src/{lexer,parser,ast,ops,modules,sem,analyze,analyze_expr,driver}.rs (see docs/JAVA_MAP.md)
next: TLC side — values (M3), config + spec processing (M4), evaluator, BFS (M5)
