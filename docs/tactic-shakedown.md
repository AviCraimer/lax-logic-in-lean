# Tactic shakedown: retrofitting the normalisation proofs

Before the ⊤⊤-lifting session, the recurring proof patterns of the
normalisation development were distilled into `LaxLogic/PLLTactics.lean`
(132 lines, roughly half documentation, **zero imports** — `solve_by_elim`
is core Lean as of this toolchain) and the two termination files were
reproved with them, as a shakedown under real load.  Everything below is
committed green; `beta_sn`, `assoc_sn` and all their supporting lemmas
prove exactly what they proved before (only `red_pair`/`red_case`/`red_bind`/
`red_lam`/`red_inl`/`red_inr`/`red_val` have *smaller* signatures — the `RSN`
arguments that were only induction fuel are now derived internally).

## The toolkit

| Item | Kind | What it does |
|---|---|---|
| `mirror` | macro | `constructor <;> solve_by_elim`: closes a congruence-mirror case — apply the shape-determined constructor, discharge its premise from hypotheses (instantiating IH quantifiers, e.g. at `ρ.lift`). |
| `lift_cases` | macro | `intro _ v; cases v` with `rfl` in both branches: the binder case of every pointwise σ-algebra law. |
| `Acc.selfInduction` | lemma | Accessibility induction that re-supplies the `Acc` witness to the step case. |
| `Acc.pairInduction` / `Acc.tripleInduction` | lemmas | Simultaneous accessibility induction on 2/3 terms — replaces the nested `induction … with \| intro` + revert/re-intro + `.intro _ hacc` witness-rebuilding dance. |
| `Acc.of_inversion` / `Acc.of_inversion₂` | lemmas | SN transfer along a simulation: from step-inversion for a constructor (or renaming), `Acc` of the pieces gives `Acc` of the compound. |

## Measured effect (proof lines, before → after)

| Theorem | Before | After | Mechanism |
|---|---:|---:|---|
| `AStep.toStep` | 20 | 1 | `induction h <;> mirror` |
| `AStep.weight_lt` | 20 | 1 | `induction h <;> simp only [...] <;> omega` |
| `RStep.toStep` | 25 | 1 | `mirror` |
| `RStep.rename` | 33 | 2 | `(try rw [Tm.subst1_rename]) <;> mirror` |
| `RStep.subst` | 33 | 2 | same, with `subst1_subst` |
| `step_split` | 25 | 7 | `mirror` under an `Or`-split |
| `RSN.rename` | 8 | 5 | `Acc.of_inversion` at `rename_reflect` |
| `red_abort` | 8 | 5 | `Acc.selfInduction` |
| `red_beta_exp` | 26 | 17 | `Acc.pairInduction` |
| `red_lam` | 12 | 3 | `RSN.lam` + term-mode pair |
| `red_pair` | 38 | 21 | `Acc.pairInduction` + `RSN.pair` |
| `red_inl` / `red_inr` / `red_val` | 19/19/16 | 10/10/7 | `RSN.inl/inr/val`, no induction left at all |
| `red_case` | 33 | 22 | `Acc.tripleInduction` |
| `red_bind` | 27 | 15 | `Acc.pairInduction` |
| 10 pointwise `here/there` callbacks | 5 each | 1 each | `lift_cases` |

Net: `PLLStrongNorm.lean` 429 → 393, `PLLReducibility.lean` 1295 → 1117
(−214 lines across the two files, *including* ~45 new lines of reusable
`RSN` congruence lemmas that did not exist before), against +132 lines of
`PLLTactics.lean`.  Line count understates the real gain: the deleted lines
were concentrated in exactly the constructions that caused build-iteration
failures in the original session (motive bugs in nested SN inductions,
`Acc`-witness rebuilding, `clear H` to dodge auto-revert pollution) — all
of which are now impossible at the call sites.

## What resisted (recorded honestly)

* **`RStep.rename_reflect`** (155 lines) is unchanged.  Its per-case body
  `obtain ⟨t', hs, rfl⟩ := ih ρ h'; exact ⟨_, .xCong hs, rfl⟩` is already
  two moves, and the existential's witness must be pinned by the `rfl`
  *before* the constructor is chosen, so `mirror` cannot fire first.  A
  bespoke elaborator could generate the whole induction, but that is a
  session of metaprogramming for one (admittedly recurring) lemma shape.
  The ⊤⊤ file needs the `Step`-version of this lemma; budget it at full
  hand-written length (~170 lines with the two assoc cases).
* **`Tm.step?_none`** (the certified-reducer soundness): its repetition is
  `Option`-match bookkeeping, not one of the four patterns; left alone.

## Traps found (worth knowing before the ⊤⊤ session)

1. **Postponed `by`-blocks escape `first`.**
   `first | exact .inl (by mirror) | …` fails opaquely when the `by`-block
   is postponed: its failure lands *after* `first` has committed.  Use the
   eager form `(refine .inl ?_; mirror)` inside `first` alternatives.
2. **Pin motives on the `Acc` eliminators in term position.**
   Expected-type-driven higher-order unification happily solves `P ?a` with
   the projection solution (`P := Red φ`, `?a := .abort φ t`), producing
   alien type-mismatch errors.  Always write `(P := fun t => …)`, and
   `(f := …)` for `Acc.of_inversion`.
3. **`solve_by_elim` moved to Lean core** — `Mathlib.Tactic.SolveByElim` no
   longer exists as an import; nothing needs importing.
