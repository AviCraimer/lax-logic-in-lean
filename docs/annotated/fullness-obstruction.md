# The fullness obstruction: why the ⊃-clause must be presented the future

Source: `LaxLogic/BeliefRealisability.lean` (promoted from `wip/` 2026-07-18), section `FullnessObstruction`
(the theorem `realS_fullness_obstruction`); the frame is built with the
checker machinery of `LaxLogic/PLLCountermodelEmit.lean`. Audit:
`[propext, Quot.sound]` — no choice. Reading conventions as in
`docs/annotated/README.md`. This is the pivot of the ⊩ᵖ programme: the
machine-checked reason the presented clause family exists at all.

## What is being obstructed

A completeness-by-decoration proof for a realisability relation ⊩ runs a
mutual induction establishing, over a suitable class of models,

* **adequacy** — whatever is ⊩-realised is truth-forced, and
* **fullness** — whatever is truth-forced has a realiser,

each consuming the other at the ⊃-clause. The obstruction shows this
induction *cannot be run* for the strategy relation ⊩ˢ (`realS`): there
is a single three-world frame on which **no evidence assignment
whatsoever** is simultaneously atom-adequate and full — for every
partial applicative structure that can implement finite lookup tables
against the world-coding. So the failure is not a defect of one candidate
decoration; it is a property of the clause family.

## The frame

Built as literal checker data (`FinCM`), so all its forcing facts are
decided by computation (`force_iff` + `decide`):

```lean
abbrev obsM : FinCM :=
  { n := 3, ri := [(0, 1), (0, 2)], rm := [], fall := [],
    val := [(1, "p"), (2, "q"), (1, "t"), (2, "t")] }
```

In words: a root `0` below two incomparable leaves `1` and `2`
(`Rᵢ` is the reflexive closure of the two listed pairs); the constraint
relation `Rₘ` is reflexive only; no fallible worlds; the atom `t` holds
at both leaves, `p` only at leaf 1, `q` only at leaf 2. Two easy
computations pin the two forcing facts the proof needs:

* `◯t` is forced at each leaf (its only future is itself, and its only
  constraint-successor is itself, where `t` holds) but **not at the
  root** (the root's only constraint-successor is itself, and `t` fails
  there);
* consequently `◯t ⊃ (p ∨ q)` **is truth-forced at the root**: vacuously
  at the root itself (the antecedent fails there), and at each leaf via
  its local atom.

## The statement

```lean
theorem realS_fullness_obstruction (P : Pca) (κ : obsC.W → P.Carrier)
    (htab : ∀ g : obsC.W → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i)) :
    ¬ ∃ Ev : Evidence P obsC,
      (∀ (a : String) (w : obsC.W), ∀ x ∈ Ev.E a w, w ∈ obsC.V a) ∧
      (∀ (φ : PLLFormula) (w : obsC.W), obsC.force w φ →
        ∃ x, x ⊩ˢ[Ev, κ, w] φ)
```

In words: fix any applicative structure `P`, any world-coding `κ`, and
assume only that `P` can realise finite tables against `κ` (`htab`: for
every assignment of outputs to the three worlds there is an element
computing it — Kleene's first algebra does this for any injective
coding). Then there is **no** evidence assignment `Ev` on the frame that
is both *atom-adequate* (an atom has evidence only at worlds where it
holds — the first conjunct) and *full* for ⊩ˢ (every forced formula has
a realiser — the second).

Note the quantifier structure: `Ev` is inside the negation. This is what
makes the theorem an obstruction rather than a counterexample to one
decoration.

## The proof, step by step

Suppose `Ev` were atom-adequate and full.

**Step 1 — fullness pays out tokens.** Fullness at the atom `t` at each
leaf hands over elements `m₁ ⊩ˢ t` at leaf 1 and `m₂ ⊩ˢ t` at leaf 2;
by the atom clause (no fallible worlds) these are genuine members of
`Ev.E "t"` at the respective leaves.

**Step 2 — one table serves both leaves.** Apply `htab` to the output
assignment

    leaf 1 ↦ pair (κ 1) m₁ ,   leaf 2 ↦ pair (κ 2) m₂

to obtain a single element `s`. Unfolding the ◯-clause of ⊩ˢ at each
leaf (whose only future is itself, and whose only constraint-successor
is itself), `s` strategy-realises `◯t` **at both leaves
simultaneously**: presented κ(leaf), it answers with that leaf's own
name and that leaf's token. In the Lean this is the pair of `have`s
`hs₁`, `hs₂`, each a three-line unfolding: the future must be the leaf
itself (decided by the narrowing lemmas `key1`/`key2`, themselves
`decide`d), the named witness is the leaf, `fst_pair`/`snd_pair` project
the package, and the token realises the atom.

This is the heart of the matter, so it deserves its own sentence:
**strategies carry no world-marks** — a strategy is a function of the
*presented* future, so one finite table is evidence for ◯t at two
incomparable worlds at once, and nothing about the element `s` betrays
which world it is being used at.

**Step 3 — the clash.** Fullness at `◯t ⊃ (p ∨ q)` at the root hands
over a realiser `x`. Unfold the ⊃-clause of ⊩ˢ — and here is the
critical syntax:

```lean
| .ifThen φ ψ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∀ b, realS P Ev κ φ b v →
        ∃ y, P.app x b = some y ∧ realS P Ev κ ψ y v)
```

`x` is applied to **`b` alone**. The world `v` is quantified in the
clause but never shown to the realiser. Instantiate the clause twice —
at leaf 1 with `b := s`, and at leaf 2 with `b := s` (legitimate both
times by Step 2). Application is a function: both instantiations receive
the *same* answer `y = app x s`. But `y` must realise `p ∨ q` at leaf 1
— whose tag must be *false*, since atom-adequacy empties `Ev.E "q"` at
leaf 1 — and also at leaf 2, where the same reasoning forces the tag
*true*. One Boolean is not two. ∎

(In the mechanised proof the two instantiations are `h1 s hs₁` and
`h2 s hs₂`; `Option.some.inj` identifies the two answers; the tag clash
is `Bool.false_ne_true`. The atom-adequacy steps are the `hA`
applications, each discharged against the frame's valuation by
`decide`.)

## Why the obstruction is ◯-essential

One might hope to rescue ⊩ˢ by choosing cleverer evidence — say,
*world-tagged* atom tokens, so that realisers betray their world after
all and a table-building PCA can case on them. For purely intuitionistic
antecedents this rescue **works**, and the reason is heredity: to feed
the ⊃-clause an antecedent realiser at a branch point, the antecedent
must be forced there, and forcing a disjunction at a branch point
already commits to a disjunct along every future — so the consequent
witness can be chosen uniformly. The rescue fails exactly for
antecedents of the form ◯A, because Step 2 manufactures a *single*
unmarked realiser for two incomparable worlds out of the modality's own
clause. The lax modality itself creates the obstruction to its own
naive completeness.

## What the obstruction forces

The repair is dictated, not chosen: the ⊃-clause must be told the world,
exactly as the ◯-clause already is. That is the single change defining
⊩ᵖ (`realP`, `LaxLogic/PLLEvidence.lean`):

```lean
| .ifThen φ ψ, x, w =>
    ∀ v, C.Ri w v → v ∈ C.F ∨
      (∀ b, realP P Ev κ φ b v →
        ∃ y, P.app x (P.pair (κ v) b) = some y ∧ realP P Ev κ ψ y v)
```

— the realiser now receives `⟨κ v, b⟩`. Step 3's clash dissolves
(`app x ⟨κ 1, s⟩` and `app x ⟨κ 2, s⟩` may differ), and the mutual
induction goes through: that is `realP_adequate_and_full`
(`docs/annotated/adequacy-fullness.md`). The separations of the
triptych are stated for ⊩ˢ and are untouched; ⊩ᵖ is the
completeness-grade refinement the obstruction demands.
