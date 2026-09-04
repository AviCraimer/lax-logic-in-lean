# The catpart tool: an archaeology

This document reconstructs what the `catpart` Standard ML implementation of
category-partition testing actually does and actually is, read directly out
of the surviving source. It does not rely on the published paper (Ostrand
and Balcer, "The Category-Partition Method for Specifying and Generating
Functional Tests", *CACM* 31(6), 1988) except to name the method; the
grammar and semantics below are derived from the code and from the example
`.tsl`/`.frm` files that ship alongside it.

Sources (read-only, not modified):
- `/Users/matthew/Backup/Sheffield/ml/catpart/` — the fullest surviving copy,
  including a resurrection attempt (files `catpart.cm`, `catpart2.cm`,
  `base2.sml`, `permlist.sml`, and edited copies of `catpart_absyn_val.sml`,
  `catpart_revive_load_most.sml`, `catpart_val.grm`, `catpart_val.grm.sml`,
  `pretty2.sml` that exist only here, not in `ml_orig`).
- `/Users/matthew/Backup/Sheffield/ml_orig/catpart/` — the pre-resurrection
  state of the same directory, used below as the diff baseline.
- `/Users/matthew/Backup/Sheffield/ml/` (parent directory) — `interface.sml`,
  `permlist.sml`, `permlist2.sml`, `base.sml`, and the `testgen/` sibling
  project.
- `/Users/matthew/bin/catpart` and
  `/Users/matthew/Backup/Sheffield/ml/catpart/catpart0.1` — the installed
  wrapper script and the compiled binary it points at.

All file:line references below are to the `ml/catpart/` copy unless marked
`ml_orig`.

---

## 1. What the tool does, end to end

`catpart` reads a **T**est **S**pecification **L**anguage (TSL) file
describing a function's input space as *categories* of *choices*, and
writes a **frame** file: one paragraph per generated test case, each
naming, for a subset of the categories, which choice was picked. The
pipeline is:

```
  file.tsl
     |  (catpart0.2.lex : ML-Lex)
     v
  token stream
     |  (catpart_val.grm : ML-Yacc)
     v
  Absyn.catpart value          (catpart_absyn_val.sml : the AST + pretty-printer)
     |  (catpart0.2_frame.sml : the frame generator)
     v
  list of frames
     |  (print_combs, in catpart0.2_frame.sml)
     v
  file.frm
```

The five source files that matter, and what each owns:

| File | Role |
|---|---|
| `catpart0.2.lex` (→ `catpart0.2.lex.sml`) | ML-Lex lexer: tokens, keyword table, three lexer states (`INITIAL`/`MAIN`/`CHOICE`) plus a `COMMENT` state, comment-nesting-return bookkeeping |
| `catpart_val.grm` (→ `catpart_val.grm.sml`, `.sig`, `.desc`) | ML-Yacc grammar: TSL concrete syntax, builds `Absyn` values as semantic actions |
| `catpart_absyn_val.sml` | The `ABSYN` signature (abstract syntax datatypes) and a Wadler/Paulson-style pretty-printer for a parsed spec |
| `catpart_parse_val.sml` | Glues lexer + parser into `file_parse : string -> Absyn.result`, `string_parse`, `top_parse` |
| `catpart0.2_frame.sml` (also `catpart0.1_frame.sml`, `catpart_frame.sml` — near-identical, see §6) | The frame generator: partitions choices into flagged/unflagged, does constrained search over the unflagged cross-product, prints frames |
| `catpart_link.sml` | Wires the generated parser/lexer functors together into concrete structures `Parse`, `Absyn`, etc. |
| `pretty2.sml` / `block.sml` | Larry Paulson's pretty-printing combinators (block/break/string), used by the Absyn pretty-printer |
| `permlist.sml` / `permlist2.sml` | small list utilities: `member`, `delete`, `perm`, `idx`, `uth` (1-based-from-the-end `nth`) |
| `cp_make.sml` | interactive build script: prompts for a version number, `use`s the load chain, and (if confirmed) calls `IO.exportFn` to write a standalone executable |

The exported top-level entry point is `catpart(argv, env)` in `cp_make.sml`
(`ml/catpart/cp_make.sml:53-62`): it takes the second command-line argument
as a file basename `root`, and calls `process(root^".frm", root^".tsl")`.
`process` (`ml/catpart/catpart0.2_frame.sml:303-309`) opens the output file,
parses the input file via `file_parse`, and on a successful parse calls
`generate os tsl`; on a failed parse (`None`) it writes the literal string
`"Empty specification"`.

---

## 2. The TSL grammar, as it actually is

This is read off `ml/catpart/catpart_val.grm:20-134` and cross-checked
against the example `.tsl` files. It differs from the published
Ostrand–Balcer syntax in exactly the ways the source shows (no `Parameters`
vs `Environments` distinction — see §7 — and a specific parenthesization
discipline for compound conditions that the paper's prose is looser about).

### 2.1 Top-level envelope

```
func_spec : CAP FUN COLON VAR NEWLINE categ_specs ENDFUN SEMICOLON NEWLINE
```

i.e.

```
<Letter> Function: <name>
Categories:
  <categ_specs>
EndFunction;
```

Concretely, from `find.tsl:1-2,35`:

```
A Function: find
  Categories:
  ...
EndFunction;
```

`CAP` is a single capital letter used as an identifying tag for the
function (the lexer rule `<INITIAL>{capital}{ws}` at
`ml/catpart/catpart0.2.lex:57-58` matches one capital letter followed by
whitespace and yields its first character). `VAR` after `Function:` is the
function name. `categ_specs` may be empty (`categ_specs : ... | ([])`,
`catpart_val.grm:70-71`), giving a spec with zero categories.

### 2.2 Categories

```
categ_specs : CATEGORIES COLON NEWLINE categs | (* empty *)
categs      : one_categ categs | (* empty *)
one_categ   : NUMBER categ_name NEWLINE choices
```

Concretely (`find.tsl:3-7`):

```
  1 pattern_size
    * empty[property empty]
    * single character[property nonempty]
    * many characters[property nonempty]
    * longer than any line in the file[error]
```

Category numbers (`NUMBER`) are attached to each category (`categ_no`) but
are **not** checked for uniqueness or for matching position in the list —
the grammar accepts any integer literal there and the frame generator never
inspects `categ_no` for consistency (`combine`/`extract`,
`catpart0.2_frame.sml:103-114, 204-215`, walk `categ_specs` and the choice
index list in lock-step by *position*, ignoring the printed number
entirely). The number is cosmetic/documentary only.

A category must have at least one choice: `choices : choice | choice
choices` (`catpart_val.grm:81-82`) has no empty alternative, unlike
`categs`. `test6.tsl` (see §6) violates this and the parser's built-in
error correction visibly does *something* about it, not cleanly.

### 2.3 Choices and modifiers

```
choice : STAR ch_name maybe_modifiers NEWLINE
```

i.e. `* <choice name> <modifiers>`, one per line
(`ml/catpart/catpart_val.grm:84-87`). `ch_name` is an unrestricted `VAR`
(the lexer's `chvar` token, `catpart0.2.lex:55`, allows internal spaces, so
multi-word choice names like `single character` or `no embedded blanks`
lex as one `VAR`).

`maybe_modifiers` is eight alternatives covering every subset of
`{[if cond], [property p,...], [flag]}` in a *fixed order* — `if` first,
`property` second, the error/single flag last
(`catpart_val.grm:89-120`). There is no alternative that allows the three
bracket groups in another order, and no alternative with more than one of
each kind. Concretely, from `find.tsl`:

```
* not applicable[if empty]                                    (if only)
* pattern is quoted[property quoted]                           (property only)
* several embedded quotes[if nonempty][single]                 (if + flag)
```

and from `fileinfo.tsl:5`:

```
* one line   [property notempty,oneline] [single]              (property list + flag)
```

`properties : property | property COMMA properties`
(`catpart_val.grm:128-129`) — a comma-separated list inside one
`[property ...]` bracket, as in the `notempty,oneline` example above.

`flag : ERROR | SINGLE` (`catpart_val.grm:133`) — the keywords `error` and
`single`, lower-case, matched via the lexer's keyword table
(`catpart0.2.lex:14-24`).

### 2.4 Conditions (`if`)

```
cond   : property
       | NOT LRBR cond RRBR
       | LRBR cond RRBR log_op LRBR cond RRBR
log_op : AND | OR
```

(`catpart_val.grm:122-126`.) The important, easy-to-miss fact is that
**a binary condition's two operands must each be individually
parenthesized**, and this is the *only* production for `and`/`or` — there
is no bare-property-and-property form and no way to combine more than two
sub-conditions except by nesting parenthesized pairs. A bare `not(...)`
used as an unparenthesized operand of `and`/`or` is **not** valid TSL under
this grammar (see §6.3 for a spec that gets this wrong).

Well-formed examples, verbatim:

```
[if nonempty]                                    -- find.tsl:10, a bare property
[if (nonempty) and (quoted)]                     -- find.tsl:14, both operands parenthesized
[if not(match)]                                  -- find.tsl:34, NOT LRBR cond RRBR
[if ((wordful)or(twowords))or(oneword)]          -- fileinfo.tsl:25, left-nested chain,
                                                     each `and`/`or` still binding two
                                                     parenthesized operands
[if ((fred) and (sheila)) and (sarah)]           -- test3.tsl:4, three-way conjunction
                                                     built the same way
```

### 2.5 Comments

Comments are `{ ... }` (`catpart0.2.lex:62-63, 81, 90, 93-99`), a distinct
lexer state (`COMMENT`) entered from any of `INITIAL`, `MAIN`, or `CHOICE`
and returning to whichever one it was entered from
(tracked by the `lex_state` ref — see §6.1 for how this differs from
version 0.1). Comments do **not** nest: `comment.tsl:3` says so explicitly
("Note that nested comments are `_not_` allowed") and the lexer rule
`<COMMENT>\{  => (lex())` (line 95) just consumes a `{` inside a comment
without adjusting any nesting counter, so an embedded `{` does not extend
the comment, it is inert. `comment.tsl` and `comment2.tsl` are TSL files
written purely to exercise this (comments before `Function:`, around the
identifying letter, inside a choice line, immediately after a choice name,
between a `[property ...]` bracket and its neighbour), e.g.
`comment.tsl:12`:

```
 {the bar category} * choice c [if b]{sneaky comment}[property c]
```

Neither `comment.tsl` nor `comment2.tsl` has a corresponding `.frm` file in
the directory — they appear to have been used only to drive the
lexer/parser interactively, not to run frame generation.

---

## 3. Frame-generation semantics

Read from `ml/catpart/catpart0.2_frame.sml`. (`catpart0.1_frame.sml` and
`catpart_frame.sml` are the same algorithm; see §6 for the
version-to-version diff, which is one comment toggle.)

### 3.1 Flagged vs unflagged partition

`partition_spec` (`catpart0.2_frame.sml:37-69`) splits **every category's
choice list** into two: choices carrying an `[error]` or `[single]` flag
(`is_flagged`, lines 44-52, tests `maybe_flag=Some _`), and choices
carrying no flag. This yields two whole specs, `tsl_f` (all categories, but
each holding only its flagged choices) and `tsl_u` (all categories, each
holding only its unflagged choices) — `group (map partition_flags cs)` at
line 61-62.

### 3.2 Flagged frames: one choice, one frame, no combination

`flagged_combs` (`catpart0.2_frame.sml:285-293`) turns `tsl_f` into a frame
list by `isolate`: for every category, for every flagged choice in it,
emit a **singleton** frame containing just that one `{categ_no, categ_name,
choice}` triple. Flagged choices are never combined with anything else —
not with each other, not with any unflagged choice. This is exactly why
`find.frm` frames 1–7 (`ml/catpart/find.frm:2-28`) each name only one
category:

```
1
pattern_size = longer than any line in the file

...

4
file_name = no file with this name

5
file_name = omitted
```

`find.tsl` has seven flagged choices (one `[error]` in category 1, one
`[error]` in category 2, one `[single]` in category 4, two `[error]` in
category 5, one `[single]` in category 6, one `[single]` in category 7) and
`find.frm` has exactly seven singleton frames before the combined ones
start. This is Ostrand and Balcer's rule that error and single-choice
categories get "special" one-off test frames rather than being crossed with
the rest of the spec; the code implements it literally as "one flagged
choice = one degenerate frame".

### 3.3 Unflagged frames: guarded search over the cross-product

`generate_unflagged` (`catpart0.2_frame.sml:256-281`) works over `tsl_u`
(unflagged choices only):

- `make_bases tsl` (lines 84-93) computes, per category, the number of
  unflagged choices — a list of integers, the "radix" of each digit.
- A **combination** is a list of integers, one per category, each in
  `0 .. base_i - 1`, i.e. a point in the cross-product
  `∏_i {0,...,base_i-1}`.
- `next bases m l` (lines 195-201) is odometer-style increment on such a
  list (increment the last "digit", carry leftward on overflow, matching
  `uth`'s reversed indexing — see `ml/permlist.sml:47`, `nth(rev l,a)`).
- `valid comb` (lines 176-184) is the **admissibility predicate**: for a
  fully-extracted combination `comb` (a list of `Choice`s, one per
  category), for every category index `m`, `setup_cond m comb`
  (lines 137-154) computes the pair `(properties selected by every *other*
  chosen choice in the combination, the guard condition of the choice at
  position m)`, and `|= ` / `|-` (lines 159-174) evaluate that guard as a
  simple two-valued satisfaction relation: a bare property is satisfied iff
  it is a member of the accumulated property set (`member s V`), `and`/`or`
  and `not` compose in the obvious classical way, and an absent guard
  (`None`) is vacuously satisfied. `valid comb` is the conjunction
  (`fold (op /\) ... true`) of this check over every category — i.e. the
  chosen choice in **every** category must have its guard satisfied by the
  properties supplied by the **other** chosen choices in the same
  combination. This is symmetric in category order: `setup_cond` gathers
  properties from all positions other than `m`, regardless of whether they
  come textually before or after category `m` in the spec, so a guard may
  legally reference a property declared in a category numbered later than
  itself (`mid_test.tsl:9`, category 2's guard `(bar) or (pah)` references
  `bar`, a property set by category 1, and `find.tsl`'s category 7 guards
  reference `match`, a property set by category 6 — both "backward"
  references in spec order; nothing in the algorithm requires "forward"
  references not to occur either).
- `generate_unflagged` does a linear odometer walk from the first
  combination (`first m`, all zeros, lines 229-230) around the whole
  cross-product exactly once (`step` returns `[]` when it revisits `start`,
  line 269-271, which `iterate`, lines 232-234, treats as termination),
  keeping only combinations for which `valid` holds, and maps `combine` to
  turn each surviving index-combination back into a frame
  (`catpart0.2_frame.sml:103-114`).

So **the generated unflagged frame set is exactly**:

> { c ∈ ∏_i Choices_unflagged(category i) | ∀ i . guard(c_i) is satisfiable
> from ⋃_{j≠i} properties(c_j) }

a **constrained cross-product**: full Cartesian product of the per-category
unflagged choice sets, filtered by a per-choice guard predicate evaluated
against the union of properties contributed by the choices selected for
every *other* category in the same tuple. This is not full pairwise
coverage and not any bounded-degree combinatorial coverage — it is the
*entire* admissible cross-product, minus whatever the guards prune away.
`find.tsl`'s unflagged part has bases `[3,2,4,3,1,3,2]` (categories 1–7
after removing flagged choices), a raw cross-product of `3·2·4·3·1·3·2 =
432` combinations, of which 33 survive the guards (`find.frm` frames 8–40,
`ml/catpart/find.frm:29-358`) — plus the 7 flagged singleton frames, giving
`find.frm`'s 40 frames total. `fileinfo.tsl` — 10 categories, up to five
choices each — produces 735 frames (`fileinfo.frm`, 234 KB, verified by
counting frame-number lines) purely from unconstrained-cross-product
growth; this is the concrete evidence cited in the design document (§5
there) for why full expansion does not scale as a spec grows.

### 3.4 Output

`print_combs`/`print_comb` (`catpart0.2_frame.sml:236-249`) write frames as
plain text, one blank-line-separated block per frame, each line
`<categ_name> = <choice_name>`, numbered sequentially starting at 1 across
*all* frames (flagged frames first, then unflagged) — this is what every
`.frm` file above shows. There is no structured (s-expression, CSV, etc.)
output format; `.frm` is exactly this printed text.

### 3.5 Dead code and abandoned three-valued-logic experiment

Lines 311-637 of `catpart0.2_frame.sml` are entirely commented out: ad hoc
test drivers against `tsl1`/`tsl2`/`tsl3`, and — worth flagging
specifically, lines 379-535 — an abandoned redesign of `valid`/`|-` using a
three-valued `Tri = True | False | Maybe` datatype and later a
`Quad = Firm of bool | Weak of bool` datatype, with a matching `extend`/
`next`/`step` search that would prune the odometer walk using partial
(incremental) guard evaluation instead of testing each fully-extracted
combination from scratch. Comment at line 409-415 documents the intended
semantics precisely ("True means this constraint is definitely satisfied
... Maybe means ... could become satisfied if the list were extended").
This was never finished or wired in; the shipped `valid` (§3.3) always
extracts the *whole* combination before testing it, i.e. it does no
incremental pruning at all — every point in the cross-product is fully
materialized and independently checked. This matters for the Lean design
(docs/catpart-lean-design.md §3): a decision-procedure-based reimplementation
gets the incremental-pruning benefit almost for free from `Decidable`
short-circuiting, which the original never achieved.

---

## 4. The ageing report

The `ml_orig/` vs `ml/` diff (`diff -rq`, both directories) shows exactly
six files touched or added during the resurrection attempt: `catpart.cm`,
`catpart2.cm`, `base2.sml`, `permlist.sml` (new, absent from `ml_orig/`),
and edited copies of `catpart_absyn_val.sml`, `catpart_revive_load_most.sml`,
`catpart_val.grm`, `catpart_val.grm.sml`, `pretty2.sml`. Everything else —
critically, `catpart0.2.lex.sml` (the *generated* lexer) and
`catpart_link.sml` (the file that wires the generated parser and lexer
functors together) — is untouched from the mid-1990s state. That
asymmetry is itself evidence, worked out below.

### 4.1 Pre-Basis option constructors: `Some`/`None`, not a basis-library problem here

The codebase does **not** rely on the pre-1997 SML/NJ top-level `Some`/
`None`/`Option` — it defines its own: `datatype 'a Option = Some of 'a |
None` in `ABSYN` (`ml/catpart/catpart_absyn_val.sml:9,47`), plus a local
`exception Option` and `get_option` in the frame generator
(`catpart0.2_frame.sml:17-20`). So the modern basis's `option`/`SOME`/`NONE`
do not collide with this datatype by name clash at the `Some`/`None`
level — but the frame generator's own `exception Option`
(`catpart0.2_frame.sml:17`) **does** collide: the Standard Basis Library
now defines `Option.Option` as a structure and, more sharply, `exception
Option.Option` — actually the basis's exception is spelled `Option` too
(`exception Option.Option : exn`, raised by `Option.valOf`). Declaring a
top-level, unqualified `exception Option` (line 17) shadows any reference
to the basis structure `Option` for the rest of the compilation unit unless
it is always referred to by the qualified name `Option.foo`; the source
never once writes `Option.something`, so this is latent rather than
immediately fatal, but it is exactly the kind of "same name now means
something else" trap the task description asked to look for. The lexer
*does* use the modern basis's real `option`/`SOME`/`NONE` alongside the
homemade `Some`/`None` — see `catpart0.2.lex:28-33,73,87` (`(pos * pos ->
... token) option`, `SOME v`, `NONE`) — the two option types coexist in
the same file, which is confusing to read but not a compile error since
they are spelled differently by case (`Some`/`None` vs `SOME`/`NONE`).

### 4.2 Old imperative I/O: not Basis `TextIO`

Concrete, uncorrected occurrences of the pre-Basis `output`/`open_out`/
`close_out`/`open_in`/`close_in`/`input`/`input_line`/`std_in`/`std_out`
family (removed from the Standard Basis; replaced by `TextIO.output`,
`TextIO.openOut`, `TextIO.closeOut`, `TextIO.openIn`, `TextIO.closeIn`,
`TextIO.inputN`/`TextIO.inputLine`, `TextIO.stdIn`, `TextIO.stdOut`):

- `catpart0.2_frame.sml:236,241,244,247,248,296,303,304,307,308` —
  `print_comb`, `print_combs`, `process`, `generate`, all built on
  unqualified `output`, `open_out`, `close_out`.
- `catpart_parse_val.sml:58,59,71` — `file_parse` uses `open_in`, `input`,
  `close_in`; `top_parse` uses `input_line std_in`.
- `interface.sml:25` (parent dir; `../interface.sml` is `use`d by
  `catpart_revive_load_most.sml:22`) — `output(std_out, "Line " ^
  (makestring line) ^ ...)`; `makestring` is an old SML/NJ pervasive
  ("stringify anything") that has no Basis equivalent at all and must be
  replaced by an explicit `Int.toString`.
- `cp_make.sml:5,34-38` — `input(f,1)`, `open_in`, `close_in`,
  `std_in`.
- `block.sml:31,33,40` (the earlier, un-fixed pretty-printer, still present
  in the tree but not referenced by either `.cm` file) — same `output`
  calls against a bare `outstream` type rather than `TextIO.outstream`.

Contrast: `pretty2.sml` (the revival's fix for `block.sml`/`pretty.sml`)
and `catpart_absyn_val.sml` **were** patched to the modern basis —
`pretty2.sml:32,34,41` use `TextIO.output`, and `catpart_absyn_val.sml:137,
139,141` use `TextIO.stdOut` — confirming the revival's actual working
method was "patch file by file as I use it", and it never reached
`catpart_parse_val.sml`, `catpart0.2_frame.sml`, or `interface.sml`.

### 4.3 `nonfix`, hand-defined `/\`, `\/`, and the entailment operators

`ml/catpart/catpart0.2_frame.sml:10-15`:

```sml
nonfix |-;
nonfix |=;
nonfix /\;
nonfix \/;
fun /\ (b1, b2) = b1 andalso b2;
fun \/ (b1, b2) = b1 orelse b2;
```

with `infix /\; infix \/;` re-declared later (line 156-157) and `infix |-;
infix |=;` re-declared still later (lines 187-188), around a first
definition of `|-`/`|=` as prefix-applied curried functions
(lines 159-174). `/\` and `\/` are SML's ASCII rendering of ∧ and ∨;
`|-` and `|=` are the entailment and semantic-satisfaction turnstiles. None
of these four are basis identifiers — they are legal SML symbolic
identifiers the author chose for readability, made `nonfix` first (because
some are fixity-declared as infix by convention/other libraries and the
author wanted plain prefix application inside the recursive definition),
then declared `infix` again afterward for call-site readability. This
*compiles* under both old and modern SML — it is not a basis-compatibility
problem — but it is exactly the kind of "logic notation smuggled into
identifiers" the task asked to flag, and the author's own comment at line
168-169 records a real fixity/parsing trap he hit doing this:

```sml
	  | |-  (V, Binary(And, c1, c2)) =
        let val b1 = (|- (V, c1))
	    val b2 = (|- (V, c2))
	in b1 andalso b2  (* replacing andalso with /\ gives _strange_
			     syntax error! *)
	end
```

i.e. inside the very definition of `/\`'s sibling clause, substituting the
custom `/\` operator for the built-in `andalso` produces a syntax error he
did not fully diagnose (a plausible cause: at that point in the file `/\`
is still in a `nonfix`/`infix` transition and the parenthesization that
works for `andalso` — a keyword, not an identifier — does not carry over
directly to an infix identifier application). This is folk evidence of the
general design tension in §5: the author repeatedly reaches for
mathematical logical notation and repeatedly finds ML's fixity/parsing
rules push back on it in small, surprising ways.

### 4.4 The `%header` break: the central, reproducible compile error

Compare `ml_orig/catpart/catpart_val.grm` and `ml/catpart/catpart_val.grm`:

```diff
-open Absyn;
+(* open Absyn;
 type result = result
 type 'a Option = 'a Option
+*)

 %%
 %name catpart
-%header (functor catpartLrValsFun (structure Token : TOKEN
-			           structure Absyn : ABSYN ) : catpart_LRVALS)
```

The revival commented out **both** the `%header` directive (which told the
old ML-Yacc to generate the functor
`catpartLrValsFun(structure Token : TOKEN structure Absyn : ABSYN) :
catpart_LRVALS`, taking *two* structure parameters) **and** the `open
Absyn;` inside the grammar's header/prelude section. Re-running ML-Yacc on
the edited `.grm` file (evidenced by the corresponding diff in
`catpart_val.grm.sml`, confirmed independently by the *different runtime
API shape* it now emits — see §4.5) produces, with no `%header`, the
default single-parameter functor:

```sml
functor catpartLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : catpart_TOKENS
   end
 =
struct
structure ParserData=
struct
structure Header =
struct
(* ... comment ... *)
(* open Absyn;
type result = result
type 'a Option = 'a Option
*)

end
```
(`ml/catpart/catpart_val.grm.sml:1-19`.)

The `Header` structure is now **empty** — it contains no bindings at all,
because the one binding it used to contribute (`open Absyn`, bringing
`Some`, `None`, `F`, `Cat`, `Ch`, `M`, `Prop`, `Binary`, `Not`, `And`, `Or`,
`Error`, `Single` into scope) is commented out. But the generated semantic
actions further down the same file still reference exactly those names —
twenty-one occurrences of `Some`/`None`/`F{...}`/`Cat{...}`/`Ch{...}`/
`M{...}` inside three `local open Header in ... end` blocks
(`catpart_val.grm.sml:253,307,320`, confirmed by grep), e.g. line ~from the
diff:

```sml
|  ( 0, ( ( _, ( MlyValue.func_spec func_spec, func_spec1left,
func_spec1right)) :: rest671)) => let val  result = MlyValue.start (
Some func_spec)
```

`Some` here is unbound: `Header` no longer exports it, and nothing else in
scope defines it. **This file, as it sits on disk today, does not
type-check under any SML compiler** — this is not a matter of basis-version
drift, it is a straightforward unbound-identifier error, self-inflicted by
half of a fix (dropping `%header`) without the other half (re-adding
`Absyn`'s bindings some other way, e.g. `structure Absyn = ...; open
Absyn;` outside the functor, or restoring the two-parameter functor and
threading `Absyn` through explicitly).

Independent corroboration from the CM build cache left in
`ml/catpart/.cm/`: `x86-unix/` (compiled object code) contains entries only
for `pretty2.sml` and `catpart_absyn_val.sml` — the two files that *were*
patched and that type-check standalone. `SKEL/` and `GUID/` (dependency
analysis only, no compiled code) additionally list `catpart_val.grm.sml`,
`catpart_val.grm.sig`, `catpart0.2.lex.sml`, `permlist.sml`,
`catpart_link.sml` — i.e. CM got as far as parsing/analyzing every file's
top-level structure but never produced object code for any of them. That
is consistent with a compile-time error occurring at `catpart_val.grm.sml`
that halted the build before reaching the files after it.

### 4.5 The functor call site was never updated to match

`catpart_link.sml:6-8` (untouched by the revival, identical in `ml_orig`
and `ml`):

```sml
structure catpartLrVals : catpart_LRVALS =
    catpartLrValsFun(structure Token = LrParser.Token
		     structure Absyn = Absyn);
```

This still supplies **two** structure arguments (`Token` and `Absyn`) and
ascribes the result to `catpart_LRVALS`, matching the *old* two-parameter
functor. Against the regenerated single-parameter functor of §4.4 this is
a second, independent type error: "functor does not match / too many
structure arguments" (exact phrasing depends on compiler), on top of the
unbound-identifier error inside the functor body itself. Fixing §4.4 alone
would not be enough; `catpart_link.sml` would also need to change, and
nothing in the tree shows that having been attempted.

### 4.6 The `EC` (error-correction) record shape changed between ML-Yacc versions

`base2.sml:80-88` (added by the revival, header comment "Modified to work
with sml-nj v110.75") declares the `LR_PARSER` signature's `ec` field with
the *old* field names:

```sml
ec: {is_keyword : LrTable.term -> bool,
     noShift : LrTable.term -> bool,
     preferred_subst:LrTable.term -> LrTable.term list,
     preferred_insert : LrTable.term -> bool,
     errtermvalue : LrTable.term -> 'b,
     showTerminal : LrTable.term -> string,
     terms: LrTable.term list,
     error : string * 'c * 'c -> unit
    },
```

and `PARSER_DATA`'s `EC` sub-signature the same way
(`base2.sml:123-132`). But the ML-Yacc that regenerated
`catpart_val.grm.sml` (§4.4) emits the *new* shape:

```sml
val preferred_change : (term list * term list) list =
nil
```

(`ml/catpart/catpart_val.grm.sml`, in the `structure EC` block — no
`preferred_subst`/`preferred_insert` at all, a single `preferred_change`
list instead, plus a locally-defined infix `$$` list-builder not present
in the old output). `base2.sml`'s hand-written `LR_PARSER`/`PARSER_DATA`
signatures and the actual generated `EC` structure are for **two different
versions of the ML-Yacc runtime API**; the revival brought in a version of
the base signatures that does not match the version of ML-Yacc that
regenerated the grammar. This is a genuine tool-version-drift problem
(ML-Yacc's own runtime library changed its error-correction record between
whatever version originally built this and version 110.75's bundled
version, or later), independent of the Basis Library issues in §4.2.

### 4.7 The lexer's generated file was never regenerated

`catpart0.2.lex.sml` is byte-identical between `ml_orig/` and `ml/` (absent
from the `diff -rq` output entirely) — the revival regenerated the grammar
via ML-Yacc but did **not** regenerate the lexer via ML-Lex, even though
the lexer's `.lex` source still carries the same kind of `%header`
directive (`catpart0.2.lex:41-42`) that caused trouble in the grammar. The
`.lex.sml` on disk still opens with the old two-parameter functor header
(`catpart0.2.lex.sml:1-2`, `functor catpartLexFun(structure Tokens:
catpart_TOKENS structure Interface: INTERFACE) : LEXER=`), which happens to
still match what `catpart_link.sml:11-13` expects. So the lexer stage is
*not* broken by the same mechanism as the parser stage — the revival simply
had not reached it (or reached it and decided it did not need touching,
which given §4.4 seems premature: nothing downstream of the parser can be
exercised until the parser itself compiles).

### 4.8 CM (Compilation Manager) file format

`catpart.cm` and `catpart2.cm` (both added by the revival; no `.cm` file
exists in `ml_orig/`) use:

```
Library
    structure Catpart is
    permlist.sml
    ...
    catpart_val.grm:MLYacc
    ...
    $/basis.cm
```

and

```
Group
    is
    permlist.sml
    ...
```

respectively (`ml/catpart/catpart.cm:1-11`, `catpart2.cm:1-11`). This is
old-style CM export syntax (`Library ... is`/`Group is`, `$/basis.cm` for
the Basis Library, `file:MLYacc`/`file:MLLex` "class" tags on grammar/lexer
sources). Both files parse as legitimate CM syntax and did get as far as
producing a `.cm/` skeleton/GUID cache (§4.4's corroboration), so this is
*not* by itself what stops the build — but the two files disagree with each
other about the include list (`catpart2.cm` omits nothing that `catpart.cm`
has — they are otherwise the same nine-file list plus `$/basis.cm` — the
only difference is `Library structure Catpart is` vs bare `Group is`, i.e.
whether the whole library exports a single named structure or exports
whatever its last-processed unit exports). Two competing, near-duplicate
`.cm` files for the same nine sources, neither one referencing the fixed
`base2.sml`/`catpart_revive_load_most.sml` load path at all (both still
list `pretty2.sml`, `catpart_val.grm:MLYacc`, etc. directly, CM-style,
rather than going through the `use`-chain in
`catpart_revive_load_most.sml`), is itself evidence of an attempt abandoned
mid-way through deciding *which* build mechanism (`use`-chain vs CM) to
commit to.

### 4.9 Absolute paths baked into the load chain and the make script

- `catpart0.1_load_most.sml:3,20`, `catpart0.2_load_most.sml:3,20`,
  `catpart_load_most.sml:3,20` (all untouched by the revival) — `use
  "/home/matt/ml/permlist.sml"`, `use "/home/matt/ml/interface.sml"` —
  absolute paths to a Linux home directory that does not exist on this
  machine.
- `cp_make.sml:22` — `use
  ("/home/matt/ml/catpart/"^catpart_release^"_load_most.sml")` — same.
- `/Users/matthew/bin/catpart` (the installed wrapper, 36 bytes, plain
  text, not a symlink) — its entire content is:

  ```
  /home/matt/ml/catpart/catpart0.1 $*
  ```

  another reference to the same nonexistent `/home/matt/...` path.

- `catpart_revive_load_most.sml:3,5,17,22` *does* fix this, using paths
  relative to the `catpart/` directory (`use "base2.sml"; use
  "../permlist2.sml"; ... use "../interface.sml";`) — further confirming
  that file specifically is the revival's intended replacement entry point,
  even though (per §4.4-4.6) it still cannot succeed.

- The `catpart0.1` binary itself (`file` reports `a.out SunOS SPARC pure
  executable`) is a SPARC/SunOS object file — it cannot execute on this
  (or any current) machine regardless of the path problem; the two issues
  are independent and both fatal on their own.

### 4.10 Summary table

| Break | Kind | Where | Fixed in revival? |
|---|---|---|---|
| `Some`/`None` vs basis `SOME`/`NONE`/`Option` name clash (`exception Option`) | language/basis | `catpart_absyn_val.sml:9`, `catpart0.2_frame.sml:17` | not needed to fix (latent, not fatal) |
| Old imperative I/O (`output`, `open_in`, `std_in`, `makestring`, ...) | basis | `catpart0.2_frame.sml`, `catpart_parse_val.sml`, `interface.sml`, `cp_make.sml`, `block.sml` | partial — `pretty2.sml`/`catpart_absyn_val.sml` fixed, `catpart0.2_frame.sml`/`catpart_parse_val.sml`/`interface.sml` not |
| `nonfix`/hand-rolled `/\`, `\/`, `|-`, `|=` | style, not a break | `catpart0.2_frame.sml:10-15` | n/a (compiles fine under any era) |
| `%header` dropped, `open Absyn` commented out → unbound identifiers | language/tooling (ML-Yacc version + incomplete edit) | `catpart_val.grm`, `catpart_val.grm.sml` | attempted, left broken — **the central compile error** |
| `catpart_link.sml` still calls the old two-parameter functor | consequence of the above | `catpart_link.sml:6-8` | not fixed |
| `EC` record shape (`preferred_subst`/`preferred_insert` vs `preferred_change`) | tooling (ML-Yacc runtime API version drift) | `base2.sml:80-88,123-132` vs generated `catpart_val.grm.sml` | mismatched, not reconciled |
| Lexer never regenerated | tooling, incomplete | `catpart0.2.lex.sml` (unchanged) | n/a — not reached |
| Old-style CM `Library`/`Group ... is` syntax, two competing `.cm` files | build system | `catpart.cm`, `catpart2.cm` | present but not exercised past dependency analysis |
| Absolute `/home/matt/...` paths | build system / environment | `*_load_most.sml`, `cp_make.sml`, `/Users/matthew/bin/catpart` | fixed only in `catpart_revive_load_most.sml` |
| Binary is SPARC/SunOS `a.out` | environment | `catpart0.1` | irrelevant — would need a full rebuild regardless |

---

## 5. The design tension, in Matthew's own words

The single most important comment in the whole codebase sits at the very
top of the grammar file, and is reproduced verbatim in *two* places —
`ml/catpart/catpart_val.grm:7-13` and, unmodified, in the earlier teaching
exercise `ml/catpart/testgen_val.grm:7-13` (see §7):

```
(* This is what I want to do but I suspect ML won't let me:

   type Categ  = {param_name: string, choices: Choice list}
   type Choice = {ch_name: string, maybe_cond: Cond Option,
	          maybe_property: string list Option,
		  maybe_flag: Flag Option}
*)
```

What this is asking for: a **record type** `Choice` whose `maybe_property`
field is `string list Option` — an optional list of property names, typed
as plain `string`. The comment records a *suspicion*, not a discovered
error — there is no evidence in the surviving files that Matthew actually
tried this and hit a specific ML type-checker rejection; what is certain is
that he did not ship it. What he shipped instead (`ABSYN`,
`catpart_absyn_val.sml:23-29`) is structurally the same record shape:

```sml
datatype Modifiers = M of
    {maybe_cond: Cond Option,
     maybe_properties: string list Option,
     maybe_flag: Flag Option}

datatype Choice = Ch of
    {ch_name: string, maybe_modifiers: Modifiers}
```

So the record *did* ship, wrapped in a one-constructor datatype (`M of
{...}`, `Ch of {...}`) rather than as a bare `type` alias for a record —
ML's structural, width-subtyping-free record types make a bare `type Foo =
{...}` awkward to use polymorphically across a large grammar file (every
site constructing or matching the record has to agree on the *exact* field
set, and ML famously cannot infer which record type is meant from a
partial field list without a type annotation at each use site — this is
the well-known "cannot resolve record type" pain of SML's ad hoc
polymorphism for record labels). Wrapping the record in a single-constructor
datatype sidesteps that inference problem — the constructor name (`M`,
`Ch`, `Cat`, `F`) pins down the type at every construction and pattern-match
site — at the cost of one extra layer of `M {...}`/`Ch {...}` boilerplate
at every use.

But the deeper thing the comment is reaching for, and the thing that is
genuinely **not expressible** in this ML at all, is in the field itself:
`maybe_property: string list Option` types a property name as a bare
`string`. Nothing in the type system connects a property name written in a
`[property foo]` bracket to a property name written in an `[if foo]`
guard — they are both just `string`, checked for equality at *run time* by
`member s V` (`catpart0.2_frame.sml:159`, `PermList.member`,
`permlist.sml:33-34`). A guard that references a property no one ever
declares (a typo, or a property renamed in one place and not the other)
is not a type error, not a parse error, and not even a runtime error: it
silently evaluates to "not present" (`member` returns `false` for a name
absent from `V`) and the guard is simply never satisfiable by that
property, with no diagnostic anywhere. `catpart` has no notion of a closed,
checkable universe of property names — that is exactly the port opportunity
identified in `docs/catpart-lean-design.md` §1: make properties a type
(or a spec-generated finite index type) so that a reference to an
undeclared property is a *typecheck failure*, which is precisely the
guarantee bare ML strings-as-a-record-field cannot give, `Option`-wrapped
or not.

---

## 6. The example corpus: what worked, what didn't, and open questions

### 6.1 Version lineage: 0.1 → 0.2 → (unversioned)

`catpart0.1.lex` → `catpart0.2.lex`: version 0.2 adds a `Lex_state`
datatype (`Lex_initial | Lex_main | Lex_choice`) tracked in a ref cell, so
that a `{...}` comment started from any of the three states returns to the
*correct* state afterward (`catpart0.2.lex:96-99`); version 0.1
unconditionally returned to `MAIN` regardless of where the comment began
(`<COMMENT>\} => (YYBEGIN MAIN; lex())`, per the diff), which would corrupt
lexing of a comment inside a `CHOICE`-state or `INITIAL`-state region. This
is a genuine, documented bug fix between versions, exercised by
`comment.tsl`/`comment2.tsl` (§2.5).

`catpart0.1_frame.sml` → `catpart0.2_frame.sml` → `catpart_frame.sml`: the
only difference across all three is whether a duplicate, dead `fun ord 0 =
[] | ord n = ...` (already defined earlier in the same file, at line
~74-75) is commented out or not — functionally identical algorithms in all
three files. The unversioned `catpart_frame.sml` appears to be the "current
release" name, with `catpart0.1_frame.sml`/`catpart0.2_frame.sml` kept as
version history rather than as functionally distinct code.

### 6.2 `bad.tsl`: probing the parser's error correction

`bad.tsl` is byte-for-byte `find.tsl` with exactly two injected typos:
`Categoies:` for `Categories:` (`bad.tsl:2`) and `**` for `*` on the first
choice line (`bad.tsl:4`). `bad.frm` is **byte-identical** to `find.frm`
(confirmed by `diff`, no output). The grammar has no production that
accepts either typo directly, so this can only be explained by the
ML-Yacc-generated parser's built-in error-correction mechanism (a bounded
lookahead-based token insertion/deletion corrector — see the `lookahead`
parameter threaded through `catpart_parse_val.sml:41-54`, set to 15 at line
59, and the `EC` record's `preferred_subst`/`preferred_insert` fields in
`base2.sml:82-83` that exist specifically to bias this corrector). This
reads as a deliberate test of that error-correction behavior, and on the
evidence of the matching output it succeeded at recovering the intended
parse for both injected typos. This is an inference from the two artifacts
(the diff and the identical output), not something independently confirmed
by running the tool — it is recorded as the best-supported explanation, not
as a verified fact.

### 6.3 The empty `.frm` files: two distinct, non-exclusive hypotheses

Six `.frm` files are 0 bytes: `file.frm`, `find_route.frm`,
`find_route_altered.frm`, `find_routes.frm`, `test.frm`, `test6.frm.frm`
(distinct from the 44-byte `test6.frm`). None of them contain the literal
text `"Empty specification"` that `process` writes on a clean parse failure
(`catpart0.2_frame.sml:307`) — they are genuinely zero bytes. `open_out`
truncates its target immediately on opening (before anything is written),
so a genuinely empty file is consistent either with (a) `process` crashing
with an *uncaught* exception somewhere after opening the output but before
writing/closing it, or (b) `generate` completing normally but finding zero
frames to print (`print_combs os [] _ = output(os,"")`, itself zero bytes).
Both are live possibilities; the source was not run to distinguish them.
Two specific, well-supported (but unconfirmed) explanations were found by
inspection:

**(a) A category with every choice flagged has an empty unflagged choice
list, and the odometer search indexes into it at position 0 regardless.**
`first m` (`catpart0.2_frame.sml:229-230`) unconditionally starts every
category's index at `0`, and `extract`/`combine`
(lines 103-114, 204-215) call `nth(chs, n)` without checking `chs` is
non-empty. `test.tsl` (category `foo`: single choice `bar [single]`, hence
zero unflagged choices in that category) and `find_route.tsl` (category
`total_route_distance`: both choices are `[error]`/`[single]`, zero
unflagged; category `number_of_town_route_details_to_be_read`: both
choices `[single]`, zero unflagged) and `find_route_altered.tsl` (same
category, both choices still `[single]` after every other modifier was
stripped) all have at least one fully-flagged category. `nth([], 0)` (an
index into an empty list) has no defined case and would raise an
out-of-bounds exception uncaught by `iterate`'s `handle Extract => from`
(`catpart0.2_frame.sml:232-234`), which only catches the generator's own
`Extract` exception, not a list-indexing exception — this would abort
`process` before `close_out`, leaving the 0-byte file `open_out` already
produced. This hypothesis is consistent for `test.frm`, `find_route.frm`,
and `find_route_altered.frm`, and not contradicted by anything else in the
source, but it was not confirmed by actually running the code.

**(b) A malformed compound `if` condition that the grammar does not
accept.** `find_routes.tsl` has no fully-flagged category (every category
has at least one unflagged choice), so hypothesis (a) does not apply to it
— but three of its guards use a bare `not(...)` as one operand of a
top-level `and` without its own wrapping parentheses, e.g.
`find_routes.tsl:19-20`:

```
* one route             [if ((a_exist) and (b_exist)) and not(no_route)]
```

Per the grammar (§2.4), the right operand of `and` must itself be
`LRBR cond RRBR` — a condition wrapped in its own parentheses — and a bare
`not(no_route)` immediately after `and` is not that; the well-formed
spelling would be `... and (not(no_route))`. This would produce a parse
error at that token, which the error-correcting parser (§6.2) may or may
not be able to repair depending on how many tokens the repair needs; an
unrepaired parse error raises `LrParser.ParseError`
(`catpart0.2_frame.sml`'s `Parse`/`LR_PARSER` machinery, via `base2.sml:66`)
uncaught by `file_parse`, again aborting `process` after the output file
was already truncated to 0 bytes. This is offered as the best available
explanation for `find_routes.frm` specifically, distinct from hypothesis
(a); it was likewise not confirmed by running the code, and it is possible
the error corrector in fact repairs this case silently, in which case the
true cause of `find_routes.frm`'s emptiness is something else not
identified here.

**`file.frm`** has no corresponding `file.tsl` anywhere in the directory
(only `fileinfo.tsl`, whose own output is the 234 KB `fileinfo.frm`) — its
origin is not recoverable from this snapshot. **Open question, not
resolved.**

**`test6.frm.frm`**, the double-extension file, is best explained as an
invocation artifact rather than a spec bug: `catpart`'s argument handling
(`cp_make.sml:53-62`) always appends `.frm`/`.tsl` to whatever basename it
is given, so `catpart test6.frm` (passing the *output* filename as the
basename by mistake) would look for a nonexistent `test6.frm.tsl` and write
to `test6.frm.frm` — consistent with the empty result, and with there being
no `test6.frm.tsl` in the directory. Not confirmed independently.

`test6.frm` itself (44 bytes, *not* empty) is a separate puzzle worth
recording as open: `test6.tsl` declares category `1 foo` with **zero**
choice lines before category `2 bar` begins, which violates `choices`'
"one or more" requirement (§2.2) and should be a parse error at that point.
The actual output (`test6.frm`) contains three frames, all under the
category name `foo`, with choice values `bar`, `foo`, and (repeating the
first) `bar` again — suggestive of the error corrector deleting the
malformed `2 bar` category header and re-attaching what were textually
category 2's two choices (`* foo [property free]`, `* bar [property
free]`) to category 1, but the presence of a *third*, repeated frame is not
accounted for by that story alone. Working out the exact LALR
error-recovery trace by hand was not attempted — **open question**.

### 6.4 `comment.tsl`/`comment2.tsl` produce no `.frm` at all

Neither has a matching `.frm` file, flagged, or empty. Both appear to have
been used to exercise the lexer/parser interactively (e.g. via
`string_parse`/`top_parse`, `catpart_parse_val.sml:15,19,67,69-71`) rather
than through the `process`/`generate` pipeline that produces `.frm`
output. Consistent with their stated purpose (§2.5) of testing comment
handling, not frame generation.

---

## 7. Lineage: `testgen` (1996 coursework) → `catpart` (production tool)

`ml/testgen/testgen_val.grm` opens with: *"sample grammar file for A7
assignment 3(ii)"* (`testgen_val.grm:1`) — a Sheffield course exercise
("A7" is a course/module code). `testgen.todo` is dated explicitly: *"To do
for testgen 12/6/96"* (`testgen.todo:1`), giving a firm date, 12 June 1996,
for this branch of the work, and effort estimates for each remaining task
("Estimated time for all tasks to date: 20 hours ie 3 days").

`testgen`'s grammar distinguishes **`Params:`** and **`Envs:`** sections
(`testgen_val.grm:24-30,76-96`) — `param_specs`/`env_specs`, each its own
category list — matching Ostrand and Balcer's original distinction between
*environment* categories (properties of the test environment) and
*parameter* categories (properties of the function's actual parameters).
`testgen.todo:55-57` records the exact decision that produced `catpart`'s
simpler grammar:

```
* ?remove distinction between Parameters and Environments, replacing with a
  single keyword "Categories" ?
  (0.5 hrs)
```

`catpart_val.grm`'s single `categ_specs : CATEGORIES COLON NEWLINE categs`
(§2.2) is that to-do item, done. `catpart0.2_frame.sml`'s commented-out
dead code even preserves a fossil of the old two-list shape — a fragment at
`catpart0.2_frame.sml:418-431` (inside the large commented-out block, §3.5)
still pattern-matches `F{fun_letter=_, fun_name=_, param_specs=ps,
env_specs=es}`, the *pre-simplification* field names, abandoned in place
rather than deleted when the fields were unified into `categ_specs`.

`testgen`'s grammar carries other traces of a less mature design that
`catpart` dropped: `ch_name : STAR (STAR)` where `%term ... STAR of string`
(`testgen_val.grm:26,104`) — the `*` marker token itself carries the choice
name as its payload, rather than `catpart`'s `STAR ch_name` (two separate
tokens, `catpart_val.grm:84,87`) — a lexer/grammar split that was
apparently reworked between the two.

---

## 8. What actually built and ran

`/Users/matthew/Backup/Sheffield/ml/catpart/catpart0.1` (524 KB,
`file`-identified as `a.out SunOS SPARC pure executable`) is a compiled,
exported SML/NJ heap image for `catpart` version 0.1, produced by
`cp_make.sml`'s `IO.exportFn` call (`cp_make.sml:71`) on a SunOS/SPARC
machine — so the tool did successfully build and run at some point, on
that platform, from the `catpart0.1_*` file set (not from the later,
revival-touched files). `/Users/matthew/bin/catpart` is a 36-byte plain
text wrapper script, `/home/matt/ml/catpart/catpart0.1 $*`, i.e. it invokes
that same SPARC binary by an absolute Linux-style home-directory path.
Neither piece works today: the wrapper's path does not exist on this
machine, and even if it did, a SunOS/SPARC `a.out` cannot execute on modern
Mac (or Linux/x86) hardware regardless. Both facts are independent of the
source-level breaks catalogued in §4 — even a perfect source fix requires a
full rebuild from scratch, there is no way to make the existing binary or
wrapper work again.

The GTD provenance note *"Unit tests; catpart tool reconstituted?"* under a
"Test generation" heading (as supplied in the task background; not
independently located in this pass) is consistent with everything found
here: a standing intention to bring `catpart` back, arrested partway
through exactly the module-system and generator-tooling changes this
document catalogues.
