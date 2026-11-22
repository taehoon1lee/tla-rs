# Harness protocol: how tlc-rs is invoked and what is compared

The judge runs Java and Rust with the SAME arguments and parses both outputs with the SAME code
(`harness/tlcout.py`). tlc-rs therefore has to print **TLC/SANY-compatible text** and exit with **the same
exit code**. Nothing else (JSON, files) is read.

## Invocations
```
# SANY (corpus "parse"), cwd = directory of FILE; run twice: full, and with -s (parse only)
java  ... tla2sany.SANY            [-s] -error-codes <abs>/FILE.tla
tlc-rs --lib <community-modules> --lib <tla-library> sany [-s] -error-codes <abs>/FILE.tla

# TLC (corpus "check"), cwd = a fresh empty temp dir
java  ... tlc2.TLC  <ARGS>
tlc-rs --lib <community-modules> --lib <tla-library> tlc <ARGS>
ARGS = -tool -workers 1 -fp 0 -seed 1 -lncheck final -noGenerateSpecTE -metadir <tmp>/meta
       [-deadlock] [entry extra args: -continue -nowarning -view -maxSetSize N -inv EXPR]
       -config <abs>/X.cfg <abs>/Spec.tla
```
Module lookup order (both): spec directory (TLC) / working directory (standalone SANY) -> built-in standard
modules -> `reference/community-modules/modules` -> `reference/tla-library`.
Java gets the last two on the classpath (as CommunityModules-deps.jar, which contains the same .tla files,
plus its Java overrides) — Rust must implement those overrides natively where TLC uses them.

Java runs with `-XX:+UseParallelGC -Xmx6g` and an isolated `user.home` that opts out of TLC's execution
statistics (no network traffic).

## TLC output (`-tool`)
Every message is framed:
```
@!@!@STARTMSG <code>:<class> @!@!@
<text>
@!@!@ENDMSG <code> @!@!@
```
`code` = `tlc2.output.EC` constant (Rust: `tlc_core::ec`), `class` = 0 none, 1 error, 2 TLC bug, 3 warning,
4 state. Text outside messages that appears after message 2185 ("Starting...") is program output
(Print/PrintT) and is compared line by line (whitespace-normalized).

Extracted by `parse_tlc` (and compared at the level in brackets):

| field | from | level |
|---|---|---|
| `exit_code` | process exit code (`EC.ExitStatus`) | front/init/verdict |
| `reached_init` | message 2189 "Computing initial states..." present | front |
| `init_distinct` | 2190 "... N distinct states generated" / 2191 "... N states generated, with M of them distinct" | init |
| `first_error` | code of the first class-1 message except framing codes 2121/2264/2103 | front/init/verdict |
| `violation` | name in "Invariant X is violated", "Temporal property X was violated", ... | verdict |
| `generated`,`distinct`,`depth` | 2199 "G states generated, D distinct states found, L states left on queue." / 2194 | verdict (when Java succeeded), trace (always) |
| `trace` | each 2217 state: `N: <label>` + `/\ var = value` lines | verdict: length (BFS exits 11,12,14,75,76); trace: everything |
| `trace_tail` | 2122 "Back to state" / 2218 stuttering | trace |
| `errors` | code + normalized text of every class-1 message | trace |
| `warnings`, `output`, `left`, `outdegree` (2268), `init_generated` | | trace |

Normalization (`tlcout.norm`): runs of whitespace collapse to one space; the repository path becomes `<ROOT>`;
the harness temp dir becomes `<TMP>`. So line breaks in pretty-printed values do not matter, but the tokens and
the spaces between them do (e.g. TLC prints `( p0 :> ...` with a space when the value spans several lines).

The text of 2193 (success, contains fingerprint-collision estimates), 2185/2186/2190 timestamps and progress
messages (2200) are never compared.

## SANY output (`-error-codes`)
`parse_sany` extracts: exit code (0 ok, 2 syntax, 4 semantic, -1 other — note SANY returns -1 for many
parse failures), error markers (`***Parse Error***`, `Semantic errors:`, `Cannot find source file for module`,
`Fatal errors`, `*** Warnings:` ...), the ordered list of `Semantic processing of module X` lines, and the
normalized error text starting at the first marker, and the module names of the `Parsing file X` lines (in
order). Level `syntax` (the `-s` run) = exit code + markers + parsed-file list; level `parse` (full run) = exit
code + markers + "Semantic processing" module list; `parse_msg` = also the error text.

## Codes only tlc-rs prints
| code | meaning | exit code |
|---|---|---|
| 9999 (class 1) | "not ported yet: ..." — honest failure for a feature that is not implemented | 199 |
| 9998 (class 1) | Rust panic caught by the CLI | 198 |
Never print these for something Java would accept; never fake a Java code for something you did not compute.
