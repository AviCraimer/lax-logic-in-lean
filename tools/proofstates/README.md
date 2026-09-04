# `pstates` — a proof-state recorder and replay viewer for Lean 4

`pstates` elaborates a Lean file, walks Lean's own **info trees**, and writes a
single self-contained HTML page that replays every tactic step of every proof
in the file: the tactic as written, its position in the tactic tree, the goals
before it, the goals after it, and the difference between them.

The page can be paused, scrubbed, played at an adjustable speed, navigated by
declaration, and — the point of the exercise — **pinned**: any state can be
saved into a collection with a note, and the collection exported as Markdown or
JSON or printed.

## Why

Reading a proof someone else developed means reconstructing the intermediate
states, and Lean gives those states only through the infoview, one cursor
position at a time, in an editor, with the file elaborated live. A recording
detaches that: the states are captured once and can then be read at whatever
speed the reader wants, on a machine that need not have Lean installed, from a
file that can be attached to an email.

## Build

```sh
lake build pstates
```

The targets are declared at the end of the repository's `lakefile.toml`:

```toml
[[lean_lib]]
name = "proofstates"
globs = ["tools.proofstates.Recorder", "tools.proofstates.Html"]

[[lean_exe]]
name = "pstates"
root = "tools.proofstates.Main"
supportInterpreter = true
```

`supportInterpreter = true` is required: the tool runs the Lean frontend, and
elaborating an arbitrary file means running the elaborators, notations and
tactics that its imports install through `initialize` blocks, which go through
the interpreter.

## Run

```sh
# whole file -> PLLTopTop-states.html in the current directory
lake exe pstates LaxLogic/PLLTopTop.lean

# one declaration, named output
lake exe pstates LaxLogic/PLLTopTop.lean --decl principal \
    --html principal-states.html

# the raw record as well
lake exe pstates LaxLogic/PLLTopTop.lean --json toptop.json
```

Options:

| option | effect |
| --- | --- |
| `--decl PAT` | keep only steps in declarations whose name contains `PAT` |
| `--html PATH` | where to write the viewer (default `<stem>[-PAT]-states.html`) |
| `--json PATH` | also write the raw JSON record |
| `--no-html` | suppress the HTML (use with `--json`) |
| `--template PATH` | use a viewer template from disk instead of the embedded one |
| `--width N` | pretty-printing width for goals (default 100) |
| `--max-steps N` | stop after N recorded steps (default 200000) |
| `--keep-all` | keep the container nodes that are normally dropped (see below) |
| `--quiet` | no progress on stderr |

The file is passed by path, not by module name, and is elaborated from source;
its **imports** must already be built (`lake build` the library first), but the
file itself need not be.

The exit status is 0 whenever a record was produced. A file that does not
elaborate is *not* an error case here: the partial record is the interesting
one, and the page marks the declarations that broke.

## Measured behaviour

On this repository, `LaxLogic/PLLTopTop.lean` (1320 lines, 101 commands, the
`⊤⊤`-lifting strong-normalisation development):

| | |
| --- | --- |
| elaboration | ≈ 14–16 s |
| walk + pretty-print + write | ≈ 4–5 s |
| total | ≈ 19–21 s |
| tactic nodes seen | 3403 |
| steps recorded (after dropping containers) | 1861 |
| distinct goals after interning | 1066 |
| HTML page | 1.13 MiB |
| page load in Chrome | ≈ 35 ms |
| re-render on a step change | ≈ 0.6–1.0 ms |

With `--decl principal` the same file yields 57 steps and a 150 KiB page in
about 6 s (elaboration still dominates: the whole file must be elaborated to
reach the declaration, but only the kept steps are pretty-printed).

A whole-file page of just over a megabyte is comfortable, so no size filter is
forced; `--decl` exists because a *reader* usually wants one proof, not
because the full page is unusable.

## What counts as a step

Every `TacticInfo` node whose syntax is original source text (not the synthetic
output of a macro) is a candidate. Two things are then dropped, because
otherwise every tactic appears three to five times:

* **Container kinds.** `Lean.Parser.Term.byTactic`, the `by` atom,
  `tacticSeq`, `tacticSeq1Indented`, `tacticSeqBracketed`, `Lean.cdotTk`, and
  bare punctuation atoms (whose syntax kind is the token itself, e.g. `«]»`).
  Each tactic block sits under a `byTactic → by → tacticSeq →
  tacticSeq1Indented` chain of four nodes that all share one before/after pair.
* **`null` grouping nodes that have children** — the `with` clause of
  `induction`/`cases`, for instance. A `null` node whose text begins with `|`
  is kept, because it is an alternative header (`| succ n ih =>`) and makes a
  useful case label; a *childless* `null` node is kept too, because it is a
  genuine sub-step, for instance one rule of a `rw [r₁, r₂]`, each of which
  reports its own state.

Children of a dropped node are reattached to the nearest surviving ancestor, so
the recorded tree is isomorphic to the tactic script as written. `--keep-all`
turns the filtering off, which is what to use when the shape of the record
itself is in question.

For `theorem addComm (a b : Nat) : a + b = b + a := by induction a with …` the
recorded tree is

```
induction a with …            1 → 0
  | zero =>                   1 → 0
    simp                      1 → 0
  | succ n ih =>              1 → 0
    have key : … := by …      1 → 1
      omega                   1 → 0
    rw [key, ih]              1 → 1
      key,                    1 → 1
      ih                      1 → 1
    omega                     1 → 0
```

### Ordering: source order, except under `<;>` and backtracking combinators

Steps are emitted in info-tree traversal order. For straight-line and
structured tactic blocks that is exactly source order, and the recorded tree
matches the script.

It is *not* source order where a tactic is evaluated more than once. Under
`t <;> u` the right-hand side runs once per goal produced by `t`, so one source
position recurs several times, and the same holds for the branches of
`first | … | …` and for `try`. Those repetitions are not noise — each carries a
different goal — so the record keeps them, in evaluation order, rather than
sorting them into positional order (sorting would interleave unrelated runs of
the same tactic and destroy the correspondence with what actually happened).

Measured on `PLLTopTop.lean`: 129 of 1860 adjacent step pairs (7%) move
backwards in the file, and every one of them is attributable to `<;>`, `first`
or `try` — for instance line 161–164,

```lean
induction h generalizing Δ <;>
  (try rw [Tm.subst1_rename]) <;>
  (try (simp only [Tm.rename]; rw [← Tm.rename_lift_skip1])) <;>
  mirror
```

which produces 265 steps over four source lines. The viewer always shows the
step's line and highlights it in the source panel, so a jump backwards is
visible rather than confusing.

## The record (JSON)

```
file, declPat, leanVersion, elaborationOk, elapsedMs, elabMs,
nCommands, nRawSteps
goals  : [ { id, t } ]                     -- interned; id is the mvar name
decls  : [ { name, kind, header, l, co, el, n, first, last, broken, sorried } ]
steps  : [ { i, c, d, dep, par, kids, l, co, el, ec, k, e, tx, b, a } ]
msgs   : [ { l, co, el, ec, sev, tx, step } ]
source : [ "line", … ]
```

`b` and `a` are arrays of indices into `goals`. Interning matters: on
`PLLTopTop.lean` the 1861 steps refer to only 1066 distinct goals, and the
goals are by far the bulk of the data.

`msgs[].step` is the index of the innermost recorded step whose source span
contains the message. That is what makes a stuck proof legible: the error is
anchored to the state the prover was in when it failed, and the viewer's
"First error" button jumps straight there.

## The viewer

Everything is inline: no CDN, no web fonts, no `fetch`, no external images, no
network access of any kind. The record is embedded in a
`<script type="application/json">` element (with `</` escaped as `<\/`, a legal
JSON escape). The page is therefore publishable under a strict CSP and works
from `file://`.

* **Replay** — first/previous/play-pause/next/last, a scrubber, and a
  seconds-per-step selector defaulting to a deliberately slow 3 s.
* **Keyboard** — `←`/`→` step, `Shift`+`←`/`→` ten steps, `↑`/`↓` previous and
  next declaration, `Space` play/pause, `Home`/`End` first/last, `P` pin, `N`
  focus the last pin's note, `Esc` stop. The mapping is shown on screen.
* **State display** — goals before and after side by side, the tactic
  highlighted, the source lines in context, and any Lean message anchored here.
  The header of each goal says what happened to it: *unchanged*, *changed*,
  *closed by this step*, *new goal*. Within a changed goal the added and
  removed lines are highlighted, so an added hypothesis or a rewritten
  conclusion is visible at a glance. The step line reads e.g.
  `1 → 2  splits into 2 goals` or `4 → 3  discharges 1 goal(s)`.
* **Goal pairing.** Most tactics *replace* the goal metavariable rather than
  reusing it, so matching goals by metavariable name alone would report every
  rewrite as "one goal closed, one new goal" and no diff would ever appear.
  The viewer matches by name first, then pairs what is left by textual
  similarity (shared lines, best pairs first, threshold 0.34), and finally
  pairs a lone leftover on each side unconditionally.
* **Structure** — declarations with their line ranges, step counts and
  error/`sorry` flags; expanding one shows its tactic tree, indented by depth.
  A filter box matches declaration names and tactic text.
* **Pinning** — `P` or the button saves the current step with a note. Pins are
  listed in a side panel, reorderable, individually removable, click-to-jump,
  and persisted in `localStorage` per file. **Export Markdown** and **Export
  JSON** download the collection (tactic, both goal states, note, position);
  if the download is blocked the same text is offered in a dialog to copy.
* **Print** — "Print sheet" builds a paper version of the pinned collection
  (title, then per pin: heading, note, tactic, goals before, goals after) and
  calls `window.print()`. The print stylesheet hides the whole interface.
* **Layout** — three columns at full width; below 980 px the side panels
  collapse behind *Structure* and *Pins* toggles and the goals stack. Wide
  goals scroll inside their own box; the page body never scrolls sideways.
  Light and dark follow `prefers-color-scheme`.

## Relation to the infoview, LeanInk/Alectryon, and Verso/SubVerso

The data source is exactly the same in every case — Lean's info trees — so
there is no novelty in *what* is extracted. The differences are in what is done
with it.

* **Lean's infoview** shows the goals at the cursor, live, in the editor, with
  the file elaborated in the language server. It is authoritative and
  interactive but it is one state at a time, it requires the editor and a
  working Lean installation, and it cannot be handed to someone else.
  `pstates` records all the states once and produces an artefact.

* **[LeanInk](https://github.com/leanprover/LeanInk) +
  [Alectryon](https://github.com/cpitclaudel/alectryon).** LeanInk is a Lean 4
  CLI that analyses a file and emits Alectryon's fragment JSON; Alectryon then
  renders a static HTML page in which goal states appear on hover or click.
  Its `Alectryon.lean` emits `Token`, `TypeInfo`, `Hypothesis`, `Goal`,
  `Message`, `Sentence`, `Text`, `Fragment`, so goals (hypotheses plus
  conclusion) *are* carried — attached **per sentence**, taking the goals of
  the smallest tactic found within the sentence. So the substantial overlap is
  real: goal capture from info trees, static self-contained-ish HTML output.
  The differences that motivated writing this rather than using that:
  Alectryon's model is a *document* — source text with goals attached to
  spans, read by hovering — whereas this is a *timeline* — an ordered sequence
  of steps with transport controls, a nesting-aware tactic tree, a before/after
  diff, and a pin-and-export workflow. LeanInk records one goal state per
  sentence; this records `goalsBefore` **and** `goalsAfter` per tactic node,
  which is what the diff needs. Alectryon needs Python and a toolchain to
  render; `pstates` writes the finished page. Also, practically:
  the LeanInk repository was **archived read-only in August 2024**, and its own
  README notes that upstream Alectryon does not support LeanInk and points at a
  fork.

* **Verso / SubVerso** (both already present in this repository's
  `.lake/packages`, pulled in through Mathlib's dependency graph). SubVerso
  extracts highlighting and metadata from Lean code across Lean versions so
  that Verso documents can typeset examples with goal information. That is a
  documentation-authoring pipeline: the author chooses examples and writes
  prose around them. It is not a replay of a whole file's proof states, and it
  is not built around pausing and pinning.

Summary: the extraction is standard and deliberately so; what is new here is
the replay-and-pin interface over *all* the tactic states of a file, including
a file that fails to elaborate, in one HTML file with no runtime dependencies.

## Toolchain notes (Lean v4.31.0) — read this before maintaining

* **`Lean.Elab.runFrontend` cannot be used.** On v4.31.0 its signature ends
  `... → IO (Option Environment)`: it returns an environment or nothing, and no
  command state, so no info trees. (Other toolchains return a pair carrying the
  command state; this one does not.) `Recorder.elaborateFile` therefore drives
  the frontend directly with `Lean.Parser.parseHeader`,
  `Lean.Elab.processHeader`, `Lean.Elab.Command.mkState` and
  `Lean.Elab.Frontend.processCommand`.

* **Info trees must be harvested after every command.**
  `Command.elabCommandTopLevel` begins with

  ```lean
  modify fun st => { st with messages := {}, infoState := { enabled := st.infoState.enabled } }
  ```

  so both the messages and the info trees are reset per command. The final
  command state carries only the *last* command's. Anything that loops with
  `Frontend.processCommands` and then reads `commandState.infoState.trees` will
  silently record one command.

* **`Elab.async := false`.** The option defaults to `false`, but `runFrontend`
  and the language server set it to `true`. Under asynchronous elaboration a
  declaration's tactic proof runs in a separate task, its info tree is reported
  lazily through `infoTreeSnap`/`lazyAssignment`, and
  `PartialContextInfo.parentDeclCtx` is *not* generated (see the comment on
  `getInfoTreeWithContext?` in `Lean/Elab/Term/TermElabM.lean`), which would
  cost us the declaration names. We set it explicitly.

* **`Lean.enableInitializersExecution` must run before the first import.**
  Without it `processHeader` fails with ``` `enableInitializersExecution` must
  be run before calling `importModules (loadExts := true)` ```, and the symptom
  is a record with **zero** tactic nodes and one error. This is why `main` is
  `unsafe`.

* **Apply `InfoTree.substitute`.** Trees can contain `hole` nodes for
  metavariables filled in later; `infoState.assignment` closes them.

* **`ContextInfo.runMetaM ctx {} (Meta.ppGoal g)`**, with `ctx.mctx` set to the
  step's `mctxBefore` or `mctxAfter`. Goals discarded by backtracking are no
  longer in the context and throw; `ppGoal?` catches that and drops the goal
  rather than failing the run.

* **`Syntax.getPos? (canonicalOnly := true)` is not enough** to tell source
  from macro output: a `SourceInfo.synthetic` node with `canonical := true`
  still returns a position. `srcSpan?` matches on `SourceInfo.original`
  explicitly.

* **`include_str` is not a Lake build dependency.** `viewer.html` is embedded
  into `Html.lean` at elaboration time, but Lake decides what to rebuild from
  the *content hash* of the `.lean` sources, so editing `viewer.html` alone
  triggers no rebuild — and `touch`ing `Html.lean` does not either. Either
  develop with

  ```sh
  lake exe pstates FILE.lean --template tools/proofstates/viewer.html
  ```

  which reads the template at run time and needs no rebuild at all, or force
  the rebuild:

  ```sh
  rm -f .lake/build/lib/lean/tools/proofstates/Html.olean \
        .lake/build/lib/lean/tools/proofstates/Html.trace
  lake build pstates
  ```

  Expressing this properly needs Lake's `extraDepTargets`, which requires a
  `lakefile.lean`; this repository uses `lakefile.toml`, so the two workarounds
  above are what there is.

* **Version sensitivity.** `String.Pos.Raw`, `Substring.Raw`, the deprecation
  of `String.trim` in favour of `String.trimAscii` (which returns a
  `String.Slice`), and the `HeaderSyntax` shape are all v4.31-era. The info-tree
  API itself (`TacticInfo` with `goalsBefore`/`goalsAfter`/`mctxBefore`/
  `mctxAfter`, `PartialContextInfo.mergeIntoOuter?`, `Info.updateContext?`) has
  been stable for a long time and is the part least likely to move.

## Intended workflow

1. A batch of proof work is developed in the usual way, and lands (or gets
   stuck).
2. A recording is generated for the file, or for the declaration under
   discussion:

   ```sh
   lake build pstates
   lake exe pstates LaxLogic/PLLTopTop.lean --decl principal \
       --html principal-states.html
   ```

3. The single HTML file is handed over. It needs no server, no network and no
   Lean.
4. The reader replays at their own speed, pins the states worth discussing,
   writes a note on each, and exports the collection as Markdown. That Markdown
   — position, tactic, both goal states, note — is a precise agenda for the
   next round: it says *which state* the question is about, which is exactly
   what prose about a proof usually fails to pin down.

When the proof is stuck, generate the recording anyway. The page's badge says
"elaboration incomplete — partial record", the failing declarations carry an
**error** flag in the navigator, "First error" jumps to the failing tactic, and
the message is shown next to the state that the tactic was applied to.

### A `--watch` mode, if it is ever wanted

Not implemented. It did not fall out cheaply, and it would need more than a
loop:

* a file watcher (`IO.FS.Metadata.modified` polling would do; there is no
  portable inotify binding in core);
* **incremental elaboration**, or every save costs a full re-elaboration
  (14 s+ on this file). `Lean.Elab.IO.processCommandsIncrementally` and
  `Language.Lean.processCommands` exist precisely for this and take an `old?`
  snapshot to reuse, so the machinery is there — but that path is the
  asynchronous one, which reintroduces every `Elab.async` problem listed above
  (lazily reported info trees, missing `parentDeclCtx`), so the walker would
  need to handle `lazyAssignment` and recover declaration names another way;
* a way to get the new record into an already-open page without a server and
  without breaking the no-network property. Rewriting the HTML file and
  reloading is the honest answer; preserving pins across the reload already
  works, since they live in `localStorage` keyed by file path.

A simpler 80% version — re-run on save, keep the browser tab, hit reload — is
one `fswatch`/`entr` line away and needs no code here:

```sh
ls LaxLogic/PLLTopTop.lean | entr -r \
  lake exe pstates LaxLogic/PLLTopTop.lean --decl principal --html /tmp/p.html
```

## Files

| file | contents |
| --- | --- |
| `Recorder.lean` | frontend driver, info-tree walk, goal pretty-printing, JSON |
| `Html.lean` | template substitution and `<script>`-safe JSON escaping |
| `viewer.html` | the viewer: inline CSS and JS, two markers substituted at write time |
| `Main.lean` | command line |
| `example-principal-states.html` | a generated sample: `PLLTopTop.principal`, 57 steps |
