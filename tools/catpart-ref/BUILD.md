# Building and running catpart (reference implementation)

This is catpart, version 0.2 -- Matthew Fairtlough's 1990s category-partition
test generation tool, written in Standard ML -- rebuilt and running again
under SML/NJ 110.99.9 (MacPorts, November 2025) on this machine.

Read this together with `../../docs/catpart-reference-build.md`, which
records exactly what was changed and why, the fidelity comparison against
the preserved 1990s outputs, and the answers to the open archaeological
questions. This file only gives the commands.

## Prerequisites

- `/opt/local/bin/sml` -- Standard ML of New Jersey, version 110.99.9
  (confirmed installed on this machine; MacPorts package `smlnj`).
- `/opt/local/bin/ml-yacc` and `/opt/local/bin/ml-lex` -- both symlinks to
  the same `sml` binary (SML/NJ dispatches on `argv[0]`), also confirmed
  installed.
- No MLton is needed or used.

Everything below assumes a working directory of `tools/catpart-ref/src/`
(all `use`/`ml-yacc`/`ml-lex` invocations use paths relative to that
directory).

## What's in `src/`

`src/` is a copy of `/Users/matthew/Backup/Sheffield/ml_orig/catpart/`
(the earlier, unmodified source tree -- see
`docs/catpart-reference-build.md` S1 for why `ml_orig/` rather than `ml/`
was the starting point), plus `permlist2.sml` and `interface.sml` copied
in from one directory up (`ml_orig/`), plus a handful of small new files
that make it build under a modern SML/NJ:

- `compat.sml` -- shim re-binding the pre-1997 SML/NJ "old I/O" names
  (`std_out`, `open_in`, `output`, `input_line`, ...) and two old
  SML/NJ Library list functions (`nth`, `fold`) to their modern Standard
  Basis Library equivalents, so the *original* source files can be
  loaded completely unmodified.
- `load_ref.sml` -- the loader, in dependency order (replaces
  `catpart0.2_load_most.sml`, which used dead absolute paths).
- `run_all.sml` -- batch driver: runs every `.tsl` spec in the directory
  and writes `<name>.out.frm` (never overwrites the preserved
  `<name>.frm` files).
- `experiments.sml` -- reproduces the answers to the four open
  archaeological questions (see the docs report, S5).
- `compare.sh` -- byte-for-byte fidelity check of `<name>.out.frm`
  against the preserved `<name>.frm`.
- `flag_error.tsl`, `flag_single.tsl`, `flagcrash_min.tsl` -- small,
  purpose-built specs used by `experiments.sml`.

Only one original file needed hand-editing: `catpart0.2.lex` (two small
edits, both forced by the pre-1997-to-1997 Standard Basis Library
transition; see below and the docs report S2). Every other `.sml` file
in this directory is byte-identical to its counterpart in
`ml_orig/catpart/` -- verified with `diff`.

## Rebuilding from scratch

If you want to reproduce this from the read-only sources yourself
(rather than trusting the copy already in `src/`):

1. Copy the sources:
   ```
   cp -R /Users/matthew/Backup/Sheffield/ml_orig/catpart/. src/
   cp /Users/matthew/Backup/Sheffield/ml_orig/permlist2.sml src/
   cp /Users/matthew/Backup/Sheffield/ml_orig/interface.sml src/
   chmod -R u+rw src/
   ```

2. Apply the two required edits to `src/catpart0.2.lex` (both are forced
   by the basis changing between when this was written and 1997's
   Definition-conformant `char` type; see docs report S2 for the full
   explanation):

   ```diff
   -                    => (CAP(hd(explode yytext),!line,!line));
   +                    => (CAP(String.str(hd(explode yytext)),!line,!line));
   ```
   ```diff
   -			  (List.fold (fn (a,r) => ord(a)-ord("0")+10*r)
   -				      (rev(explode yytext)) 0,
   +			  (List.foldr (fn (a,r) => ord(a)-ord(#"0")+10*r) 0
   +				      (rev(explode yytext)),
   ```

3. Regenerate the parser and lexer with the *installed* ml-yacc/ml-lex
   (do not reuse the `.grm.sml`/`.grm.sig`/`.lex.sml` files that are
   already sitting in `ml_orig/catpart/` -- those were built by a 1990s
   ml-yacc/ml-lex and are not what you get from the modern tool):
   ```
   cd src
   /opt/local/bin/ml-yacc catpart_val.grm
   /opt/local/bin/ml-lex catpart0.2.lex
   ```
   This produces `catpart_val.grm.sml`, `catpart_val.grm.sig`, and
   `catpart0.2.lex.sml`. No shift/reduce conflicts are reported.

4. `compat.sml` and `load_ref.sml` are new files, already provided in
   this tree (see above); copy them in too if starting completely from
   scratch.

## Running it

### Interactively

```
cd tools/catpart-ref/src
/opt/local/bin/sml load_ref.sml
```

This loads everything (including pulling in ML-Yacc's runtime support
library via `CM.make "$/ml-yacc-lib.cm"` -- see docs report S2 for why
that one piece has to go through CM even though nothing else does) and
ends with `catpart 0.2 reference build loaded OK.`. Then, at the `-`
prompt:

```
- process ("find.frm", "find.tsl");
```

`process (out_file, in_file)` is the tool's only entry point: it parses
`in_file` and writes the generated test frames to `out_file`. Note this
**overwrites** `out_file` if it exists -- use a different name (e.g.
`find.my.frm`) if you don't want to touch the preserved `find.frm`.

### Non-interactively, one file

```
cd tools/catpart-ref/src
printf 'use "load_ref.sml";\nprocess ("myfile.out.frm", "myfile.tsl");\n' \
  | /opt/local/bin/sml
```

### Non-interactively, the whole test suite

```
cd tools/catpart-ref/src
/opt/local/bin/sml run_all.sml
```

Writes `<name>.out.frm` for all fifteen `.tsl` specs in the directory
and prints OK/FAIL per file. Then check fidelity against the preserved
outputs:

```
./compare.sh
```

### The open-question experiments

```
cd tools/catpart-ref/src
/opt/local/bin/sml experiments.sml
```

Reproduces, with printed commentary, the fully-flagged-category crash,
the zero-byte `test6.frm.frm` mechanism, the `bad.tsl` == `find.tsl`
identity, and the `[error]`/`[single]` indistinguishability. See the
docs report S5 for the full write-up.

## What was NOT rebuilt

- `catpart0.1`, the surviving 1990s binary in this directory, is a SunOS
  SPARC `a.out` (`file catpart0.1` -> `a.out SunOS SPARC pure
  executable`) and cannot execute on this machine (`exec format error`
  when run directly; `incorrect byte order in heap image` if you try to
  hand it to `sml` as though it were a heap image). Only a source
  rebuild -- what this directory now is -- can work here.
- `testgen_*.sml`/`.grm` in this directory belong to a separate, related
  tool ("testgen") that also lived in the original `catpart/` directory.
  It was out of scope for this task and was not touched or loaded.
- A CM group file (`catpart.cm`) and an `ml-build` heap image were
  attempted, to give a plain `catpart myfile` shell command instead of
  loading a script into the `sml` REPL. This did not work: CM's
  separate-compilation model rejects the file-scope `open` declarations
  this codebase relies on throughout (e.g. `open Parse; open Absyn; open
  PermList;` at the top of `catpart0.2_frame.sml`), with errors like:
  ```
  pretty2.sml:4.1-4.12 Error: toplevel open
  catpart0.2_frame.sml:4.1-4.11 Error: toplevel open
  catpart.cm:22.3-22.23 Error: no module exports from (catpart.cm):catpart0.2_frame.sml
  ```
  Fixing this would mean wrapping the original files' logic in
  structures/functors -- a real restructuring, not a compatibility fix,
  and out of step with the "change as little as possible" brief. The
  `use`-chain approach above (`sml load_ref.sml`, `sml run_all.sml`, ...)
  is the delivered, verified way to run the tool, and it does run from
  a plain shell command as shown above.
