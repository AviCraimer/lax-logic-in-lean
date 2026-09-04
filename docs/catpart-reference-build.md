# catpart reference build report

Matthew Fairtlough's 1990s category-partition test generation tool
("catpart"), rebuilt and run again from source under SML/NJ 110.99.9 as
a reference implementation. This report records what was changed and
why, the fidelity check against the preserved 1990s outputs, and the
experimental answers to the open archaeological questions.

Working tree: `tools/catpart-ref/src/`. Build/run commands:
`tools/catpart-ref/BUILD.md`. Sources are read-only under
`/Users/matthew/Backup/Sheffield/`; nothing there was modified.

**Result: it runs.** `find.tsl` and 11 of the other 13 comparable specs
reproduce their preserved 1990s `.frm` output byte-for-byte, including
the full 735-frame `fileinfo.frm` (234,174 bytes). One spec
(`find_routes.tsl`) produces output where the original is an empty
file, for reasons explained in S5. Two specs (`comment.tsl`,
`comment2.tsl`) have no preserved `.frm` to compare against.

## S0. Toolchain and sources used

- `/opt/local/bin/sml` -- Standard ML of New Jersey, version 110.99.9,
  64-bit, November 4, 2025 (MacPorts `smlnj` port). No MLton involved.
- `/opt/local/bin/ml-yacc`, `/opt/local/bin/ml-lex` -- symlinks to the
  same `sml` binary (it dispatches on `argv[0]`).
- Source tree: `/Users/matthew/Backup/Sheffield/ml_orig/catpart/`, the
  earlier, unmodified copy -- **not**
  `/Users/matthew/Backup/Sheffield/ml/catpart/` (the 2013 partial
  resurrection attempt), because the latter had already stripped
  ML-Yacc's `%header` clause and commented out `open Absyn` from
  `catpart_val.grm` without replacing it, which is unrecoverable short
  of rewriting the grammar action code (the actions reference `Some`,
  `F{...}`, `Cat{...}`, etc. as unqualified identifiers from `Absyn`).
  `ml_orig/catpart/catpart_val.grm` still has both, and was used
  as-is (verified: `diff` against the read-only original is empty).
- Also copied in: `permlist2.sml` and `interface.sml`, from one
  directory up (`ml_orig/`, not `ml/`), as the loader scripts expect.
- Generation: used the "0.2" file set (`catpart0.2.lex`,
  `catpart0.2_frame.sml`) throughout, per the task's recommendation --
  it is the latest of the three parallel copies present
  (unversioned / `0.1` / `0.2`) in the source directory. It worked
  cleanly; there was no need to fall back to `0.1`.

## S1. Why `ml_orig/`, and what's actually still in `ml_orig/catpart/`

The directory holds three parallel generations of the lexer/frame-generator
pair (`catpart.lex`/`catpart_frame.sml`, `catpart0.1.lex`/`catpart0.1_frame.sml`,
`catpart0.2.lex`/`catpart0.2_frame.sml`), all sharing one grammar
(`catpart_val.grm`) and one parser-value layer (`catpart_parse_val.sml`,
`catpart_link.sml`). It also holds a second, unrelated tool ("testgen",
`testgen_*.sml`/`.grm`) that was out of scope here and was not touched
or loaded.

## S2. The build, step by step

### S2.1 Regenerating the parser and lexer

`ml_orig/catpart/catpart_val.grm` already carries the `%header` clause
and `open Absyn;` line the task flagged as critical:

```
open Absyn;
type result = result
type 'a Option = 'a Option
%%
%name catpart
%header (functor catpartLrValsFun (structure Token : TOKEN
			           structure Absyn : ABSYN ) : catpart_LRVALS)
```

Running the *installed* `ml-yacc` (not reusing the `.grm.sml`/`.grm.sig`
already sitting in the source directory, which were built by a 1990s
ml-yacc) regenerates `catpart_val.grm.sml`/`.grm.sig` cleanly, with no
shift/reduce conflicts reported. The generated `catpart_TOKENS`
signature and `catpartLrValsFun` functor match what `catpart_link.sml`
already expects unmodified.

`catpart0.2.lex` needed two edits before `ml-lex` would produce
type-correct output (see S3.1 below); after those, `ml-lex
catpart0.2.lex` regenerates `catpart0.2.lex.sml` cleanly too (54
states, no warnings).

### S2.2 ML-Yacc's runtime library only exists as a compiled CM library

The task's diagnosis expected `catpart_link.sml`'s
`Join(structure ParserData = ... structure Lex = ... structure LrParser
= ...)` call to need updating for "modern ML-Yacc's different Join
argument shape." That turned out not to be true -- the installed
ml-yacc-lib's `Join` functor (confirmed against the upstream source,
`lib/mlyacc-lib/join.sml`) takes exactly
`(structure Lex : LEXER structure ParserData : PARSER_DATA structure
LrParser : LR_PARSER)`, which is what `catpart_link.sml` already calls
with, unmodified.

What *is* different, and unavoidable: this SML/NJ installation ships
`ml-yacc-lib` (the `LrParser`/`Join`/`TOKEN`/`LEXER`/... runtime support
code that `base.sml` used to provide via `use`) only as a precompiled CM
library --
`/opt/local/share/smlnj/lib/SMLNJ-ML-YACC-LIB/.cm/amd64-unix/ml-yacc-lib.cm`
is a binary blob; there is no source tree to `use` directly (confirmed
by `find`). So `load_ref.sml`'s very first line is
```
CM.make "$/ml-yacc-lib.cm";
```
which pulls the library's structures into the interactive top-level
environment. Everything else in the loader is a plain `use`, exactly as
in the original `catpart0.2_load_most.sml`. This is the one place CM is
unavoidable; see S6 for why a *full* CM build (to get a shell-invocable
heap image) was attempted and abandoned.

One consequence worth recording: the modern `LR_PARSER`'s error-context
record shape is
`{is_keyword, noShift, preferred_change, errtermvalue, showTerminal,
terms, error}`, where the old `base.sml`/`base2.sml` (in the 2013 `ml/`
copy) had `preferred_subst`/`preferred_insert` instead of the single
`preferred_change`. This confirms the task's diagnosis that
`base2.sml`'s hand-written signature doesn't match current ML-Yacc's
output -- but it isn't something we have to fix by hand: since both the
installed `ml-yacc` (code generator) and the installed `ml-yacc-lib.cm`
(runtime) come from the same SML/NJ 110.99.9 distribution, the code
`ml-yacc` generates already matches the library's expectations by
construction.

## S3. Change list

### S3.1 Genuine language/basis changes forced by SML evolution (1 file, 2 edits)

Both are in `src/catpart0.2.lex` (the ml-lex source, hand-edited before
regeneration -- the generated `catpart0.2.lex.sml` is a build product,
not hand-edited). This is the **only** original source file that needed
any editing at all; every other `.sml`/`.grm` file in `src/` is
byte-identical to its counterpart in the read-only
`ml_orig/catpart/` (verified with `diff`).

1. **`explode` changed meaning between the Definition catpart was
   written against and the 1997 Definition's `char` type.**
   Pre-1997, `explode : string -> string list` (single-character
   strings); the modern Standard Basis has
   `explode : string -> char list`. `catpart0.2.lex` line 58 built a
   `CAP` token (declared `CAP of string` in the grammar) as
   `hd(explode yytext)`, which under the old basis is a 1-character
   `string` and under the modern basis is a bare `char` -- a type
   error. Fixed by wrapping in `String.str`:
   ```diff
   -                    => (CAP(hd(explode yytext),!line,!line));
   +                    => (CAP(String.str(hd(explode yytext)),!line,!line));
   ```

2. **The same `explode` change, plus the removal of the old SML/NJ
   Library's `List.fold`, plus `ord` changing from `string -> int` to
   `Char.ord : char -> int`.** `catpart0.2.lex` lines 69-72 built a
   `NUMBER` token from the digit characters of `yytext` via
   `List.fold (fn (a,r) => ord(a)-ord("0")+10*r) (rev(explode yytext)) 0`.
   `List.fold` (three curried arguments: function, list, initial value
   -- the old SML/NJ Library's foldr) does not exist in the modern
   Standard Basis (only `List.foldl`/`List.foldr`, with the initial
   value and list swapped relative to `fold`'s convention); and
   `ord("0")` passed a string where the modern `ord` wants a `char`.
   Fixed by switching to `List.foldr` (arguments reordered to match)
   and a character literal:
   ```diff
   -			  (List.fold (fn (a,r) => ord(a)-ord("0")+10*r)
   -				      (rev(explode yytext)) 0,
   +			  (List.foldr (fn (a,r) => ord(a)-ord(#"0")+10*r) 0
   +				      (rev(explode yytext)),
   ```
   Both changes preserve the exact original algorithm (same digit
   traversal order, same positional weighting); they only adapt it to
   the modern types. Verified: catpart correctly parses multi-digit
   category numbers in `fileinfo.tsl` (which has categories numbered up
   to at least two digits) with byte-identical output.

Everything else the archaeology flagged as a likely basis-compatibility
problem turned out to need **no source edits**, because:

- `ord`/`chr` (on `char`), `explode`/`implode` (on `char list`), `nonfix`
  on arbitrary symbolic identifiers (`|-`, `|=`, `/\`, `\/`), and
  user-defined `'a Option`/`Some`/`None` (a datatype the codebase rolls
  itself in `Absyn`, entirely distinct from the pervasive `'a
  option`/`SOME`/`NONE`, so there is no name clash with the modern
  `Option` structure or the built-in `option` type) all still work
  exactly as the original code expects, confirmed by direct probing of
  the installed `sml` before touching any source file.
- The old-I/O identifiers (`std_out`, `open_in`, `open_out`, `close_in`,
  `close_out`, `output`, `input`, `input_line`, `makestring`) and the two
  missing list functions (`nth`, `fold`) are supplied by a **new**
  compatibility shim (`compat.sml`, S3.2) rather than by editing the
  files that use them.

### S3.2 Build-system changes (all additive; nothing original was removed)

- **`compat.sml`** (new) -- re-binds `std_out`, `std_in`, `open_in`,
  `open_out`, `close_in`, `close_out`, `output`, `input`, `input_line`,
  `makestring`, `nth`, `fold` to their modern `TextIO`/`List` Basis
  Library equivalents. This is what lets `interface.sml`,
  `catpart_parse_val.sml`, and `catpart0.2_frame.sml` load completely
  unmodified. It must load *after* `pretty2.sml` (which does `open
  TextIO`, and so would otherwise leave the modern 1-argument
  `TextIO.input` bound to the bare name `input`, breaking the old
  2-argument `input(stream, n)` call in `catpart_parse_val.sml`) and
  before anything that calls the old-style names. `load_ref.sml`
  enforces this order; see its header comment.
- **`load_ref.sml`** (new) -- replaces `catpart0.2_load_most.sml`,
  which cannot be `use`d unmodified because it references
  `/home/matt/ml/permlist.sml` and `/home/matt/ml/interface.sml` by
  dead absolute path, and because it predates needing `CM.make
  "$/ml-yacc-lib.cm"` (S2.2). Same file list, same order, otherwise.
- **`run_all.sml`**, **`experiments.sml`**, **`compare.sh`** (new) --
  batch driver, open-question experiment reproducer, and fidelity
  diff script; see BUILD.md.
- **`flag_error.tsl`, `flag_single.tsl`, `flagcrash_min.tsl`** (new,
  small) -- minimal specs purpose-built for the S5 experiments.
- ml-yacc/ml-lex were re-run to regenerate `catpart_val.grm.sml`,
  `catpart_val.grm.sig`, `catpart0.2.lex.sml` from the (almost
  unmodified) `.grm`/`.lex` sources, overwriting the 1990s-generated
  copies that were sitting in the directory. These are build products;
  nothing in them was hand-edited.
- A CM group file and `ml-build` heap image were attempted, to give a
  plain-shell `catpart myfile` command instead of loading a script into
  the `sml` REPL. This was **not completed** -- see S6.

### S3.3 Bug fixes

None. Every behavioural difference found (S5) is either (a) a bug
already present in the original 1990s tool, now reproduced exactly
rather than fixed, or (b) attributable to the error-correcting parser's
recovery strategy possibly differing between the 1990s ml-yacc and the
2025 one (also not something in *our* code to fix -- see S5.3). No
defect in the original logic was patched.

### S3.4 Anything that changes behaviour

**None, as far as could be verified.** The two `catpart0.2.lex` edits
(S3.1) are type-driven basis translations of the original algorithm,
not behaviour changes; fidelity testing (S4) found byte-identical
output on every spec where a preserved 1990s output exists and the
1990s and 2025 error-correcting parsers appear to agree on how to
recover from a syntax error -- 12 of 14 comparable files (`comment.tsl`,
`comment2.tsl` have no preserved `.frm` to compare against). The one
file where output differs from the preserved (`find_routes.tsl`, S5.3)
is flagged loudly there: it is the one place this port's behaviour may
genuinely differ from the original's, and the likely cause is outside
this port's control (a difference in error-correction strategy between
1990s and 2025 ml-yacc, not a bug in the ported code).

## S4. Fidelity comparison

All commands: `cd tools/catpart-ref/src && sml run_all.sml && ./compare.sh`.
Output written to `<name>.out.frm`, preserved originals never touched.

| spec | preserved `.frm` | generated `.out.frm` | result |
|---|---|---|---|
| `find.tsl` | 9,533 bytes | 9,533 bytes | **byte-identical** |
| `fileinfo.tsl` | 234,174 bytes (735 frames) | 234,174 bytes | **byte-identical** |
| `bad.tsl` | 9,533 bytes | 9,533 bytes | **byte-identical** (also identical to `find.frm` itself -- S5.2) |
| `harrison.tsl` | 499 bytes | 499 bytes | **byte-identical** |
| `mid_test.tsl` | 210 bytes | 210 bytes | **byte-identical** |
| `test2.tsl` | 68 bytes | 68 bytes | **byte-identical** |
| `test3.tsl` | 26 bytes | 26 bytes | **byte-identical** |
| `test5.tsl` | 15 bytes | 15 bytes | **byte-identical** |
| `test6.tsl` | 44 bytes | 44 bytes | **byte-identical** (despite a genuine parse error -- S5.2) |
| `test.tsl` | 0 bytes | 0 bytes (crash) | **byte-identical** (crash reproduced -- S5.1) |
| `find_route.tsl` | 0 bytes | 0 bytes (crash) | **byte-identical** (crash reproduced -- S5.1) |
| `find_route_altered.tsl` | 0 bytes | 0 bytes (crash) | **byte-identical** (crash reproduced -- S5.1) |
| `find_routes.tsl` | 0 bytes | 10,839 bytes | **differs** -- see S5.3 |
| `comment.tsl` | *(none preserved)* | 91 bytes | no ground truth; output inspected, looks correct (S5.4) |
| `comment2.tsl` | *(none preserved)* | 91 bytes | no ground truth; byte-identical to `comment.out.frm` |

`find.tsl` and `fileinfo.tsl` -- the two specs the task singled out --
are both **byte-identical**. 12 of the 13 specs with a preserved,
comparable `.frm` reproduce it exactly; the sole exception is discussed
in full below.

## S5. The open questions, answered by experiment

Reproducible with `sml experiments.sml` (S1-S4 below) plus the
`run_all.sml`/`compare.sh` run above (which is what actually surfaced
S5.1 and S5.3, by running every spec and diffing).

### S5.1 Why are six `.frm` files 0 bytes?

All six, individually:

| file | cause |
|---|---|
| `find_route.frm` | fully-flagged-category crash (category 3, `total_route_distance`: its two choices carry `[error]` and `[if...][single]` -- both flagged, so it has zero *unflagged* choices) |
| `find_route_altered.frm` | same mechanism (category 4, `number_of_town_route_details_to_be_read`: both choices `[single]`) |
| `test.frm` | same mechanism (category "foo": its one choice is `* bar [single]`, so it has zero unflagged choices) |
| `find_routes.frm` | **not** the fully-flagged-category crash -- the unparenthesised-`not(...)` parse error (S5.3) |
| `test6.frm.frm` | not a generator crash at all -- reproduces as a wrong-argument mistake (S5.1.2) |
| `file.frm` | cannot be determined -- no `file.tsl` survives to test against (S5.1.3) |

So: the task's hypothesis (a), "the fully-flagged category crash," is
confirmed for three of the six (`find_route.frm`,
`find_route_altered.frm`, `test.frm`); hypothesis (b), "the
unparenthesised `not(...)` parse error," is confirmed for
`find_routes.frm` as the trigger, though not certainly as the *cause of
the empty file* (S5.3); and the remaining two are "something else"
entirely unrelated to the generator's logic.

#### S5.1.1 The fully-flagged-category crash, mechanically

`partition_spec` (`catpart0.2_frame.sml:37-69`) splits every category's
choice list into a *flagged* half (`[error]`/`[single]`) and an
*unflagged* half, and the unflagged halves are cross-multiplied to
produce most of the frames (`generate_unflagged`,
`catpart0.2_frame.sml:256-281`). If every choice in some category
carries a flag, that category's unflagged half has **zero** choices.
`generate_unflagged` still assumes every category has a choice at index
0 -- `first m` (`catpart0.2_frame.sml:229-230`) builds the starting
combination `[0,0,...]` unconditionally, and `extract`
(`catpart0.2_frame.sml:204-215`, the crashing line is 211,
`(nth(chs, n)) :: (comb cats t)`) indexes into each category's choice
list with `nth`. For a 0-choice category, `nth([], 0)` raises
`Subscript` ("subscript out of bounds" as `exnMessage` renders it).
Reproduced directly with a 6-line minimal spec,
`src/flagcrash_min.tsl`:
```
B Function: flagcrash
  Categories:
  1 onlyflagged
    * only_choice [single]
  2 plain
    * a
    * b
EndFunction;
```
`process ("flagcrash_min.frm", "flagcrash_min.tsl")` raises exactly
`subscript out of bounds`, and `flagcrash_min.frm` is left 0 bytes
(created by `open_out`, never written to because the exception happens
before any output). This is a genuine bug in the original 1990s logic,
present from the start -- not something introduced by the port, and not
fixed here (S3.3/S3.4: the brief was fidelity, not correctness).

#### S5.1.2 `test6.frm.frm`

The double `.frm.frm` extension is the tell: `cp_make.sml`'s driver
called `process(root^".frm", root^".tsl")`. If catpart was once invoked
as `catpart test6.frm` (passing the filename instead of the basename),
`root` becomes `"test6.frm"`, so the tool writes to `test6.frm.frm` and
looks for input `test6.frm.tsl` -- which does not exist. Reproduced
directly:
```
- process ("test6.frm.frm.repro", "test6.frm.tsl");
process raised: Io: openIn failed on "test6.frm.tsl", No such file or directory
```
`open_out` runs first (truncating/creating the output file), so the
result is exactly a stray 0-byte `<name>.frm.frm` file, matching what's
preserved. Not a generator bug -- a historical typo at the command line.

#### S5.1.3 `file.frm`

No `file.tsl` survives anywhere in either preserved source tree, so
this one cannot be reproduced or explained by experiment. It's either
the same kind of command-line slip as `test6.frm.frm` (someone typed
`catpart file` against a spec that either never existed or was later
deleted) or the last remains of a `file.tsl` that once existed and
crashed for its own, now unrecoverable, reason. Left unexplained; this
is the one item in this report that is honestly not resolved.

### S5.2 What does `test6.tsl` (a category with zero choice lines) do?

```
B Function: test
  Categories:
  1 foo {this is the first category}
  2 bar {this is the second category}
    * foo [property free]
    * bar [property free]
EndFunction;
```
Category "foo" has *no* `* ...` lines at all. The grammar requires at
least one (`one_categ : NUMBER categ_name NEWLINE choices`, and
`choices` is one-or-more `choice`), so this is a genuine grammar-level
syntax error, not merely a semantic zero-length list. Running it
produces:
```
Line 6: syntax error: replacing  NUMBER with  STAR
```
ML-Yacc's error corrector substitutes the `NUMBER` token that starts
category "2 bar" with a (semantically empty) `STAR` token, so the
parser treats "2" as though it were a `*` -- and everything downstream
of that follows the grammar happily: the `VAR` "bar" that was meant to
be category 2's *name* gets consumed as `ch_name` for this synthesized
choice instead, so category 2 never actually starts as its own
category. The two real choice lines meant for category "bar" (`* foo
[property free]`, `* bar [property free]`) simply continue as more
choices of category "foo". The result -- confirmed by running it, and
byte-identical to the preserved `test6.frm` -- is a single category
named "foo" with three choices:
```
1
foo = bar

2
foo = foo

3
foo = bar
```
(the first frame's choice, "bar", is the stolen category-2 name). A
single token substitution silently merges what was meant to be two
categories into one -- and the fact that this exact, slightly bizarre
recovery matches the preserved 1990s output byte-for-byte is itself
strong evidence this port's parser and the original's agree on how
error correction resolves ambiguity, at least here.

(Aside, uncovered while tracing this: the `!line` value ML-Yacc's error
corrector reports lags the physical source line the actual problem is
on, because it reflects the lexer's lookahead cursor rather than the
parser's, and this grammar's LALR lookahead is 15 tokens
(`parse (15, ...)` in `catpart_parse_val.sml`) -- enough to span several
physical lines given how many tokens a line of `.tsl` typically has.
"Line 6" above is accurate for `test6.tsl` because the error is close to
the top of a short file; S5.3's reported line numbers for
`find_routes.tsl` are off by roughly ten lines for the same reason.
This is a property of the error-correcting parser design, present in
the original tool too -- not a port artifact.)

### S5.3 Does `bad.tsl` really produce output identical to `find.tsl`'s?

Yes, confirmed exactly: `bad.out.frm`, `find.frm`, and `find.out.frm`
are all byte-identical (`cmp` exit 0). `bad.tsl` differs from
`find.tsl` by exactly two deliberate typos:
```diff
-  Categoies:
+  Categories:
-    ** empty[property empty]
+    * empty[property empty]
```
These are fixed by **two different mechanisms**, not one:

1. **`Categoies` (missing `r`)** is fixed at the *parser* level.
   `Categoies` doesn't match the lexer's keyword table (which has the
   literal string `"Categories"`), so it lexes as an ordinary `VAR`
   token. The grammar expects `CATEGORIES` there
   (`categ_specs : CATEGORIES COLON NEWLINE categs`), so this is a
   syntax error; ML-Yacc's corrector reports
   `Line 2: syntax error: replacing  VAR with  CATEGORIES` and literally
   substitutes the token. This substitution is semantically free: the
   grammar action for `categ_specs` is `(categs)` -- it never looks at
   the `CATEGORIES` token's value (it has none; `CATEGORIES` carries no
   `of type` in the `%term` declaration) -- so swapping in a synthetic
   `CATEGORIES` token changes nothing about the resulting parse tree.

2. **The doubled `**`** is fixed at the *lexer* level, not the parser.
   The first `*` matches `<MAIN>\*{space}*`, switching lexer state to
   `CHOICE` and emitting `STAR`. The second `*`, now scanned in `CHOICE`
   state, matches none of that state's real rules (`\[`, newline,
   `{chvar}`, whitespace, `\{`) and falls through to the catch-all
   `<CHOICE>.  => (error(...); lex())`, which is exactly the
   `Line 4: ignoring illegal character*` message seen at runtime --
   `Interface.error` only *prints*, it doesn't raise, and `lex()` is
   called again immediately, silently discarding the stray `*` and
   resuming the scan. The parser never even sees a second `STAR` token
   to correct.

So "the error-correcting parser" language undersells it slightly: one
typo is fixed by ML-Yacc's LR error correction, the other by the
hand-written lexer's own illegal-character recovery, and both happen to
be semantically invisible for unrelated reasons (an unused token value,
and a character that was never going to be part of any token).

### S5.4 `find_routes.tsl`: the one real discrepancy

`find_routes.tsl` contains a genuine grammar violation at (physical)
lines 24-25 and 27-28:
```
* one route     [if ((a_exist) and (b_exist)) and not(no_route)]
```
The grammar's binary-connective rule requires **both** operands of
`and`/`or` to be individually parenthesized:
`cond : LRBR cond RRBR log_op LRBR cond RRBR`, i.e. syntactically
`(cond1) and (cond2)`. Here the right operand, `not(no_route)`, is not
wrapped in its own outer parentheses -- it needed to be
`... and (not(no_route))`. This is exactly the task's hypothesis (b),
"the unparenthesised `not(...)` parse error," and it is real: running
this port's parser on the file reports (line numbers shifted by the
lookahead lag noted in S5.2)
```
Line 14: syntax error: deleting  NOT
Line 15: syntax error: deleting  VAR RRBR AND
Line 15: syntax error: inserting  RRBR
Line 17: syntax error: deleting  NOT
Line 18: syntax error: deleting  NOT
```
-- multiple corrections, but the 2025 ml-yacc's error corrector
recovers, and `process` succeeds, writing a 10,839-byte
`find_routes.out.frm`.

**What this does not settle:** whether the *original* 1990s catpart,
faced with the same syntax error, would also have recovered (in which
case `find_routes.frm` being 0 bytes has some other explanation -- most
plausibly, the historical `.frm` was simply never regenerated after
this spec was last edited) or whether the original's error corrector
gave up within its lookahead/correction budget and raised an uncaught
`LrParser.ParseError`, aborting `process` before any output was written
(exactly the same 0-byte signature as the S5.1.1 crash, but from a
different exception). Both are consistent with the evidence; the
original SunOS binary cannot be run on this machine to settle it (S6).
Given that this file needed *four separate* corrections to recover
from, an error corrector giving up partway through is entirely
plausible -- error-correction budgets and heuristics are exactly the
kind of implementation detail that can differ between ML-Yacc versions
15+ years apart. This is flagged here as the one place this port's
observed behaviour may genuinely diverge from the original's, rather
than being silently absorbed into the "12/13 byte-identical" headline
number.

### S5.5 Are `[error]` and `[single]` really indistinguishable to the generator?

Confirmed. `catpart0.2_frame.sml`'s only use of the `Flag` datatype is
`is_flagged` (line ~44-51):
```
fun is_flagged
    (Ch{ch_name=_,
        maybe_modifiers=(M{maybe_cond=_, maybe_properties=_,
                           maybe_flag=Some _})})
    = true
  | is_flagged _ = false
```
-- `Some _` is a wildcard: it tests only "is this choice flagged at
all," never *which* flag. A grep of the whole file confirms `Error` and
`Single` (the two `Flag` constructors) never appear anywhere in
`catpart0.2_frame.sml`; they're only referenced in
`catpart_absyn_val.sml`'s `string_of_Flag`, used solely by the
pretty-printer (`print_result`), which `process`/`generate` never call.

Constructed the minimal pair the task asked for --
`src/flag_error.tsl` and `src/flag_single.tsl`, identical except that
the one flagged choice is `[error]` in one and `[single]` in the other:
```
B Function: flagtest
  Categories:
  1 cat1
    * choice_a [error]     (or [single] in the other file)
    * choice_b
EndFunction;
```
`process`ing both and comparing the outputs:
```
CONFIRMED: identical output -- the generator only tests
`maybe_flag = Some _` (is a choice flagged at all?); it
never inspects *which* flag.  [error] and [single] are
indistinguishable to the frame generator.
```
(byte-for-byte identical `.frm` files). If `[error]` and `[single]` were
ever meant to be treated differently by the frame generator (as opposed
to just being documentation for the human reading the spec, or intended
for some downstream tool that doesn't exist in this codebase), that
distinction was never implemented.

## S6. What was not completed: a shell-invocable `catpart` binary

The task suggested, optionally, "a modern `catpart.cm` and/or an
`ml-build` heap image so the tool can be invoked from the shell." This
was attempted and abandoned; the working, verified way to run the tool
remains the `use`-chain scripts (`sml load_ref.sml`,
`sml run_all.sml`, ..., all real, tested shell commands -- see
BUILD.md).

A `catpart.cm` group file was written listing the source files in
dependency order (mirroring `load_ref.sml`) plus `$/ml-yacc-lib.cm`, and
built with `ml-build catpart.cm main catpart.heap`. This failed with,
among others:
```
pretty2.sml:4.1-4.12 Error: toplevel open
catpart0.2_frame.sml:4.1-4.11 Error: toplevel open
catpart0.2_frame.sml:6.1-6.11 Error: toplevel open
catpart0.2_frame.sml:8.1-8.14 Error: toplevel open
catpart.cm:14.3-14.14 Error: error(s) in ML source file
catpart.cm:22.3-22.23 Error: no module exports from (catpart.cm):catpart0.2_frame.sml
```
CM's separate-compilation model does not allow a compilation unit's
top level to consist of a bare `open` (as `pretty2.sml`'s `open TextIO`
and `catpart0.2_frame.sml`'s `open Parse; open Absyn; open PermList;`
both do) -- each unit is expected to export tracked
structures/signatures/functors, not splice arbitrary bindings into a
shared namespace the way a `use`-chain session does. This is a real,
structural mismatch between how this codebase is written (1990s
script-style, one big accumulating top-level environment) and how CM
wants files organized (proper modules), not a syntax or version issue
fixable by a small patch. Making it work would mean wrapping the
original logic in structures/functors -- a genuine rewrite of the
module structure, which is exactly the kind of invasive change the
brief asked to avoid ("make any changes needed to get the tool to
compile and work properly," read together with "there should ideally be
none" on behavioural changes, was read as license to fix compilation,
not to restructure the module system). `catpart.cm`/`catpart_main.sml`
were removed from the delivered tree rather than left in a broken
state; this section is the record of the attempt.

The task's own recommended route anticipated exactly this ("forget CM
at first... Once it runs, optionally write a modern catpart.cm") -- the
"once it runs" part is satisfied; the optional CM packaging is not, for
the structural reason above.

## S7. Everything not touched

`catpart0.1`, the surviving 1990s binary, is confirmed a SunOS SPARC
`a.out` (`file catpart0.1` -> `a.out SunOS SPARC pure executable`) and
cannot run here: invoking it directly gives `exec format error`;
attempting to load it as an SML/NJ heap image gives `Fatal error --
incorrect byte order in heap image`. Nothing short of a source rebuild
(what this whole report is about) could have worked.

`testgen_*.sml`/`.grm` (a separate, related tool that happens to share
the same source directory) was not touched, loaded, or evaluated --
out of scope for this task.
