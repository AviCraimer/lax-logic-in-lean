# The finite canonical model: a truth lemma with decided Lindenbaum steps

Source: `LaxLogic/PLLFinComp.lean` (definitions `FTheory`, `MaxIn`,
`extendStep`/`extendAll`/`lindenbaum`, the `MaxIn.*` lemma suite,
`canonFin`, `truth_lemma`, `finite_canonical_countermodel`,
`canonFinCM`, `emitter_completeness`), mirroring the classical
development of `LaxLogic/PLLCompleteness.lean` (F&M §4) case for case.
The audit currently carries `Classical.choice` inherited from named
residues of the decidability infrastructure (ledger §10, footnote);
the construction itself invokes no maximality principle — that is its
point.

## Theories are triples; promises are guarded by ◯

The classical canonical model for PLL does not work with sets of
believed formulas alone. A `Theory` has three components:

```lean
structure Theory where
  val  : Set PLLFormula    -- validated (believed)
  fal  : Set PLLFormula    -- falsified here
  mfal : Set PLLFormula    -- falsified at every Rₘ-successor
```

`mfal` is the semantic record of a *promise*: a formula pledged to fail
at every constraint-successor. Promises are what prevent the fallible
world — which satisfies everything — from trivialising the ◯-clause: a
world that has promised away φ has no constraint-access to any world
satisfying φ, the fallible one included.

Consistency ties the three components together with a carefully shaped
formula (`disjOf`):

    Consistent ⟨V, F, M⟩  iff  for no finite Ds ⊆ F, Ts ⊆ M
    (jointly nonempty):   V ⊢ ⋁Ds ∨ ◯(⋁Ts)

The **◯ guarding the promise part** is the load-bearing subtlety. A
naive reading ("V derives no falsified formula") cannot support the
modal cases of the truth lemma; with the guard, refuting a promise
means deriving *somehow-one-of-the-promised* — and that is exactly what
the elimination behaviour of ◯ lets one manipulate (the classical
lemmas `somehow_bind`, `somehow_mono` do this work, and the finite
development reuses them verbatim through a coercion).

## Finite triples, and consistency becomes one decidable check

`FTheory` is the same structure with `Finset` components; its
consistency is *defined* as consistency of the associated classical
theory, so the entire `disjOf` lemma library is reused rather than
re-proved:

```lean
def Cons (T : FTheory) : Prop := Consistent T.toTheory
```

The first finite dividend (`cons_iff_check`): because `disjOf` is
monotone in both selections, the universally quantified consistency
condition collapses to the **single worst case** — the full selections:

```lean
theorem cons_iff_check (T : FTheory) :
    T.Cons ↔ (T.fal = ∅ ∧ T.mfal = ∅) ∨
      ¬ (↑T.val : Set PLLFormula) ⊩ disjOf T.fal.toList T.mfal.toList
```

In words: a finite triple is consistent exactly when its validated part
fails to derive the one disjunction assembled from *all* its falsified
and *all* its promised formulas. That is one derivability question —
decided by the mechanised decision procedure (`decidablePLL`, through
the Curry–Howard bridge). Consistency of finite triples is decidable.

## Lindenbaum as an iterated decision

The classical development extends a consistent theory to a *maximal*
one by Zorn. The finite development walks the subformula closure once:

```lean
noncomputable def extendStep (T : FTheory) (φ : PLLFormula) : FTheory :=
  if (T.insVal φ).Cons then T.insVal φ else T.insFal φ

noncomputable def extendAll (T : FTheory) (l : List PLLFormula) : FTheory :=
  l.foldl extendStep T
```

In words: at each closure formula, **ask the decision procedure**
whether believing it stays consistent; believe if so, refute if not.
The else-branch is safe by the *extension dichotomy*
(`cons_insVal_or_insFal`): if adding φ to `val` breaks consistency and
adding it to `fal` also breaks consistency, the two failure witnesses
combine — by the same `disjOf_transform`/`rmv` surgery as the classical
`mem_val_or_mem_fal` — into an inconsistency of the original triple.

```lean
theorem lindenbaum {cl : Finset PLLFormula} {T : FTheory}
    (hT : T.Cons) (hIn : InCl cl T) :
    ∃ T', T.le T' ∧ MaxIn cl T' ∧ T'.mfal = T.mfal
```

In words: every consistent triple inside the closure extends to a
**closure-total** one — every closure formula lands in `val` or `fal` —
componentwise above it, with the promises `mfal` *untouched* (the fold
never writes to them; the truth lemma depends on this equality, twice).
`MaxIn` is the finite surrogate for maximality:

```lean
def MaxIn (cl : Finset PLLFormula) (T : FTheory) : Prop :=
  T.Cons ∧ InCl cl T ∧ ∀ φ ∈ cl, φ ∈ T.val ∨ φ ∈ T.fal
```

## The maximal-theory lemmas collapse under totality

The classical Lemma 4.2 suite consumes maximality *only* through
extension-failure witnesses ("adding φ to val breaks consistency"),
each an existentially quantified selection that the proofs then combine
with list surgery. Under totality the witnesses are **singletons**: if
φ ∈ cl is not believed it is refuted, and the selection `[φ]` already
does the damage. Sample, in full (`MaxIn.or_mem`, primeness):

if `φ∨ψ ∈ val` but neither disjunct is, totality puts both in `fal`;
then `val ⊢ φ∨ψ` (it is a member) and the selection `Ds = [φ, ψ]`
derives `disjOf [φ,ψ] []` by ∨-elimination into the two injections —
contradicting consistency. Five lines of Lean where the classical proof
needs thirty. The same pattern gives deductive closure (`ded_closed`),
implication decomposition (`imp_mem`), the falsification laws
(`fal_or`, `fal_and`) and `mfal_sub_fal` (a promised formula is
refuted: were it believed, `val ⊢ ◯(⋁[φ])` via `laxIntro`, hitting
consistency with the selection `Ts = [φ]` — note the guard doing its
work).

## The model and the truth lemma

```lean
def canonFin (cl : Finset PLLFormula) : ConstraintModel where
  W  := {T : FTheory // MaxIn cl T}
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal ⊆ T'.1.mfal
  F  := {T | falsePLL ∈ T.1.val}
  V a := {T | prop a ∉ cl ∨ prop a ∈ T.1.val}
```

In words: worlds are the closure-total consistent triples; inquiry
extends belief (`Rᵢ`); constraint-successors extend belief *and honour
promises* (`Rₘ`); the fallible worlds are the ⊥-believers; atoms
outside the closure hold everywhere (the filtration's convention, which
is what makes the valuation full on fallible worlds without infinite
data). All eight frame conditions are inclusion-structural.

```lean
theorem truth_lemma {cl} (hcl : SubClosed cl) :
    ∀ (φ : PLLFormula), φ ∈ cl → ∀ T : (canonFin cl).W,
      (φ ∈ T.1.val → (canonFin cl).force T φ) ∧
        (φ ∈ T.1.fal → ¬ (canonFin cl).force T φ)
```

In words — and note it is **two-sided**: believing forces, refuting
refutes; totality then determines the whole model. The propositional
cases ride on the lemma suite. The three cases needing a Lindenbaum
extension, each now a decided fold, are the mathematical heart:

**Refuting an implication** (φ⊃ψ ∈ fal): extend the *start triple*
`⟨val + φ, {ψ}, ∅⟩`. Its consistency reduces (via `deduct` and
`bigOr_collapse`) to: if `val, φ ⊢ ψ` then `val ⊢ φ⊃ψ`, contradicting
`not_fal_deriv` at the refuted implication. `lindenbaum` yields a total
extension T′ ⊇ᵢ T believing φ and refuting ψ; the inductive hypotheses
turn that into a future forcing φ but not ψ.

**Forcing a believed ◯φ** (◯φ ∈ val, at an arbitrary future T₁): extend
`⟨val₁ + φ, ∅, mfal₁⟩` — the body added, the promises **carried
across**. Consistency is the ◯-guard's showcase: a violation gives
`val₁ ⊢ φ ⊃ ◯(⋁Ts)` with Ts from mfal₁; but ◯φ ∈ val₁, so `somehow_bind`
(the elimination composite) yields `val₁ ⊢ ◯(⋁Ts)` — precisely a
consistency violation *of T₁ itself* with its own promises. The total
extension T₂ is then a constraint-successor of T₁ (beliefs grew,
promises exactly preserved — the `mfal` equality of `lindenbaum`)
forcing φ. Since T₁ was an arbitrary future, the ∀∃ clause holds.

**Refuting a refuted ◯φ** (◯φ ∈ fal): extend `⟨val, ∅, {φ}⟩` — a
promise **created**. Consistency: a violation gives, via `somehow_mono`
and collapse, `val ⊢ ◯φ`, contradicting `not_fal_deriv` at ◯φ. The
total extension T′ is a *future* of T (only beliefs grew; `Rᵢ` ignores
promises) at which every constraint-successor U honours φ ∈ mfal′ ⊆
mfal(U); by `mfal_sub_fal` and the inductive hypothesis, no U forces φ
— so the ∀∃ clause fails at T′, hence at T. This is the semantic
machinery of promises behind the executable countermodels, derived rather than
posited.

## From the truth lemma to the checker

`finite_canonical_countermodel`: for an underivable Γ ⊢ C, the start
triple `⟨Γ, {C}, ∅⟩` is consistent (a violation would assemble an
actual derivation, contradicting underivability); its total extension
is a world of `canonFin (clOf Γ C)` forcing all of Γ and refuting C.

The remaining distance to the *verified checker* is bookkeeping made
honest: the closure-total triples are enumerated (`worldList`), the
model is rebuilt as literal `FinCM` data (`canonFinCM`), a transfer
lemma identifies the two forcings on closure formulas, and:

```lean
theorem emitter_completeness {Γ : List PLLFormula} {C : PLLFormula}
    (h : ¬ Nonempty (LaxND Γ C)) :
    ∃ (M : FinCM) (w : Nat), FinCM.checkB M w Γ C = true
```

In words: every underivable sequent has a finite countermodel **as
checker data** — the object the decoration theorem
(`docs/annotated/adequacy-fullness.md`) consumes. The composition is
`derivable_iff_no_realP_refutation` (`LaxLogic/PLLRealCompleteness.lean`):
derivability coincides with the absence of a realisability refutation,
and the backward case decision is itself made by the decision procedure
rather than excluded middle.

## What replaced Zorn, exactly

It is worth being precise, since "constructive canonical model" claims
are often looser than this one. The classical proof uses Zorn once, in
Lindenbaum. Here the *same* extension demands are met by
`extendAll` — a fold whose branch condition is a decidable derivability
question — plus the extension dichotomy, whose proof is the classical
combination argument relocated from "maximality" to "totality". Nothing
else changes: the consistency notion, the `disjOf` calculus, the truth
lemma's case analysis and even the three start triples are the
classical ones. The infinitary principle was never load-bearing; what
was load-bearing was the ability to *decide* consistency questions —
and the decider consulted is PLL's own mechanised decision procedure.
To be precise about a formulation it is tempting to overstate: the
completeness proof lives in the metatheory (Lean's type theory), not in
PLL — a propositional, quantifier-free logic cannot even *state* its
completeness. What is true, and worth saying carefully, is that the
metatheoretic proof's only oracle is the object logic's own decision
procedure; PLL's decidability (no embedded arithmetic, no
Gödelian obstruction) is what makes that arrangement possible.
