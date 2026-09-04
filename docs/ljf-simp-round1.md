# LJF simplification round 1 — the cleanup log

*2026-08-09 evening, branch `ljf-simp-1` (from tag `ljf-ui-v1` = commit
`7aefbdc`). Rule 3 of the round: document the cleanup, why, and any
surprises; Rule 4: log compile times and lines of proof. Companion files:
`docs/ljf-simplification-pass.md` (the §2 work order this executes),
`Archive/ljf-simp-round1-superseded.lean` (everything deleted, verbatim).*

## The rounds

**Round A — delete the superseded layer** (§2.2). `eMin`/`aMin`, the
minimality pair parametrised by the saturated-case statements, deleted:
strictly subsumed by `eMinF`/`aMinF`, which prove the same statements
unconditionally. `qAssemble`/`dykAssemble` deleted: they were literally
`unStable (qAssembleN ·)` / `unStable (dykAssembleN ·)` unfolded, and the
four use sites now say so. The `SatE2`/`SatA2` *statements* stay (they name
the saturated case; the docstrings no longer call them "open obligations").

**Round B — revert `ΩOk` to `PFreeΩ`** (§2.4). The pending-list invariant
carried a disjunct "or an atom already present in `done`" that no proof
ever used once the deep forced patterns handled shifted atoms. Reverting it
deleted the invariant, its three lemmas, four `rcases`-on-a-disjunction
blocks that always took the left branch, and — the surprise of the round —
the `if hd : ↑a ∈ done` branches in `TInv`/`TpInv`'s `.atomL` arms, which
existed only to service the dead disjunct. An invariant weakened past what
the proof needs costs real code at every consumption site.

**Round C — fold the fire blobs** (§2.5). Two discoveries, both instances
of the same fact: `interp`'s `[]`-station equation is *goal-generic* (the
fire test comes before the goal-shape dispatch in the definition), so
nothing that happens at a fire needs to know the goal's shape.

* `aMinF`'s six `[]`-clauses — one per goal shape — were textually
  identical apart from the shape token, including their six copies of the
  `rw [interp]; split; … cases heq` equation dance. They merged into ONE
  clause with `G` a variable; the equation dance works verbatim with
  `some G` in place of each concrete shape, because `interp`'s `[]` clause
  pattern binds the goal as a variable. The cross-call obligation to
  `UEntry` got *easier* abstract: both measures share the atom
  `3 ^ wNeg G`, and omega cancels it.
* `aSound`'s six fire branches (the 14-line `simHyp` term repeated per
  shape) factored into one helper, `fireASound`, with the recursive
  derivation passed as an argument. The six branches are now one line each.

**Round C2 — the farm macros** (§2.3, first half). The census: the file
had **25 `decreasing_by` farms, only 8 distinct bodies**, and the three
big bodies account for 19 of them — the E-side farm (~109 lines × 8), the
A-side farm (~104 lines × 9), and the soundness farm (~42 lines × 2).
These 19 farms are now three tactic macros (`ljf_dec_e`, `ljf_dec_a`,
`ljf_dec_sound`) defined once and invoked by name. Two consequences:
~1,500 lines of duplication gone at zero behavioural risk, and §2.3's
*second* half (shrinking the farm to its ~10 live entries) becomes cheap —
it is now an edit to one macro body instead of seventeen farms.

One Lean point worth recording: tactic macros are hygienic, and the farm
entries name call-site variables (`Q'`, `hXr`, `N_d`, …), so the macros are
defined under `set_option hygiene false in` — the standard escape when a
macro is a textual abbreviation rather than a reusable combinator.

## Round D — designed, not yet executed (§2.1)

The unification of the p-fire eliminator families. The facts, measured:
`TpElim` (60 lines) and `UpElim` (80) have the *same* clause skeleton —
three live arms (atom-station, `q`-implication, Dyckhoff) plus eight
`nomatch` parked-shape exclusions — and the same holds for `TpLF`/`UpLF`
and `TpInv`/`UpInvG`, and one level up for `TStab`/`UStab`, `TLF`/`ULF`,
`TRF`/`URF`, `TInv`/`UInvG`. The E-side emits conjunct fires
(`qAssembleN`/`dykAssembleN` through the `∃p` interpolant); the A-side
emits attack disjuncts (`atkQimp`/`atkDyk` into the `∀p` aggregate). The
plan: one family parametrised by an emission record (the two fire
continuations plus the result-type flavour), instantiated twice.
Estimated saving ~350–500 lines and, more importantly, a single carrier
for the lax flag when the ◯ extension threads it through — the flag will
then touch one family, not two. Risks to respect: the result types differ
(`Stab … P₀` vs goal-indexed `Inv`), the membership-oracle parameters on
the `UStab` side, and the termination indices; the `interpA_*_eq` equation
family stays as the safety net, per §2.6's warning. This is the opening
move of the next session, not a late-evening edit.

## Metrics (Rule 4)

| state | lines | clean `lake build LaxLogic.LJF` |
|---|---|---|
| `ljf-ui-v1` (baseline) | 6,636 | 15 min 53.7 s |
| rounds A+B | 6,247 | 15 min 34.2 s |
| rounds C+C2 (with `interpFire_eq`) | 4,462 | 13 min 52.0 s |

Round 1 total: **−2,174 lines (−33%) and −2 minutes of compile (−13%)**,
with zero statement changes; every crown axiom pin unchanged and passing;
everything deleted preserved in `Archive/` and at the tag. The remaining
compile time is the mega-mutual's WF-compilation and the farms'
failing-alternative search — so the next time win is §2.3's live-entry
shrink, now a one-macro edit, and further out, splitting the mega-mutual.

## The surprise of round C: `rw` at an abstract discriminant

The merged `aMinF` clause failed its first compile with *"Failed to
rewrite using equation theorems for `interp`"*: the equation lemmas of a
well-founded definition are specialised per **fused matcher alternative**,
so `rw [interp]` on `interp p [] done (some G)` with `G` a variable
matches none of them, even though the source clause binds the goal
generically. This is the same fusion that forced the `interpA_*_eq`
restatements, now biting a *read* instead of a restatement. The fix —
`interpFire_eq`, the goal-generic fire equation stated once and proved by
an internal seven-way case split, each case concrete — is what §2.5 should
have said in the first place, and it simplified `eMinF`'s inline dance as
a bonus. Lesson for the ledger: any `rw [f]` at an abstract discriminant
needs a hand-stated generic equation, proved by cases.

## Tactic defects encountered (Rule 3, for filing upstream)

Recorded in full in `docs/ljf-simplification-pass.md` §4 and
`docs/next-session.md` §10; the two worth filing against Lean itself:

1. `omega` silently drops the positivity of a power atom occurring only in
   the goal, reporting unsatisfiable systems satisfiable (the termination
   war's root cause, with the `Prod.Lex` printer deception compounding it).
2. The termination-error printer displays the *reduced first-component
   inequality* when the actual goal is a raw `Prod.Lex` pair — the
   displayed goal is provable, the real one isn't of that type.
