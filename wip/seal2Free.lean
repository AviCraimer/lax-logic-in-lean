import wip.boxSndTight

/-!
# The γ-head seal is BUDGET-FREE at atomic bodies

`wip/sealLedger.lean` shows that the round's specified route — extend
`cascade_main`'s ledger through the `◯`-clauses — cannot work, for a reason
that is independent of every proof detail: the clause-γ-head seal
(`wip/absorb_base.lean`:3261) hands the holdout back its own room **one budget
lower**, and no ledger can both be entered from the room at `c` and re-supply
the room at `c − 1` (`no_ledger_survives_gamma_seal`).

This file establishes the escape, at the one goal shape where the apparatus
already reaches: **the γ-head seal's target budget need not be financed at
all.**

    Δ ⊢ E@(f+1, e+2)(Γ)                     (the ambient, matched budgets)
    Δ ⊢ A@(f+1, e+2)(Γ, ◯q)                 (the source, matched budgets)
    ─────────────────────────────────────────────────────────────────────
    Δ ⊢ A@(f+2, c+1)(Γ, ◯q)                 for EVERY c

`c` is universally quantified and **no room hypothesis, no ledger and no
defect bound appear**.  So at an atomic body the seal consumes nothing: it can
be crossed at the target budget the caller wants, and the room the caller
holds is untouched.

The content is entirely `PROGRESS §57`'s `boxSnd_tight`
(`wip/boxSndTight.lean`:147), which reaches the boxed goal *clause* at an
arbitrary target budget from a matched-budget source.  What this file adds is
the last step from the clause to the target **value** — one guard conversion
in the fuel (free, `fuelE_le`) and one `orAll` introduction — and the reading:
`boxSnd_tight`'s free target budget is exactly the property the ledger route
lacks.

**Scope.**  `∨`-free `S`, `◯`-subformula-closed `S`, `q ≠ p`, and the goal body
atomic.  Generalising the body from `prop q` to an arbitrary `D ∈ S` is what
would carry this to the full γ-head seal; that generalisation is
`boxSnd_tight`'s own goal-clause case (`boxGoal_remap`), not a new ledger.
-/

open PLLFormula

namespace PLLND
namespace Seal2Free

open PLLND.BoxSnd PLLND.BoxSndTight PLLND.GoalDesc

/-- The target's own goal disjunct, at fuel `f+1` and budget `c+1`. -/
theorem goalDisjunct_mem (p : String) (S : Finset PLLFormula) (f c : Nat)
    (Γ : List PLLFormula) (q : String) :
    ((itpE p S (f + 1) c Γ).ifThen
        (itpA p S (f + 1) (c + 1) Γ (prop q))).somehow
      ∈ itpAfull p S (f + 1) (c + 1) Γ ((prop q).somehow) := by
  simp only [itpAfull, itpAoth, itpAgoal]
  exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (.head _))))

/-- **The γ-head seal, budget-free at an atomic body.**  From the ambient and
the source value at *matched* budgets `e + 2`, the target value at **any**
budget `c + 1` follows.  No room, no ledger, no defect bound. -/
theorem gammaHead_budget_free (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (f e c : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (e + 2) Γ))
    (hsrc : G4c Δ (itpA p S (f + 1) (e + 2) Γ ((prop q).somehow))) :
    G4c Δ (itpA p S (f + 2) (c + 1) Γ ((prop q).somehow)) := by
  have hclause : G4c Δ (tgtClause p S f c Γ q) :=
    boxSnd_tight p S hOr hq hsome (defect S Γ) f e c Γ Γ Δ
      (Nat.le_refl _) hΓS hamb hsrc
  rw [itpA_succ]
  refine G4c.orAll_intro (goalDisjunct_mem p S f c Γ q) ?_
  refine box_remap_free hclause ?_ (G4c.identity_mem (.head _))
  exact consume₁ (G4c.identity_mem (.head _))
    (fuelE_le p S (Nat.le_succ f) c Γ)

/-- The same statement with the target budget displayed as a genuine
universal: **one** matched-budget pair discharges the seal at every budget the
caller could want. -/
theorem gammaHead_all_budgets (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (f e : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (e + 2) Γ))
    (hsrc : G4c Δ (itpA p S (f + 1) (e + 2) Γ ((prop q).somehow))) :
    ∀ c : Nat, G4c Δ (itpA p S (f + 2) (c + 1) Γ ((prop q).somehow)) :=
  fun c => gammaHead_budget_free p S hOr hq hsome f e c Γ Δ hΓS hamb hsrc

/-- **The descent instance**: taking `c + 1 := e + 1` gives the γ-head seal's
own obligation — the target one budget below the matched source — with the
room hypothesis nowhere in sight. -/
theorem gammaHead_descent (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (f e : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (e + 2) Γ))
    (hsrc : G4c Δ (itpA p S (f + 1) (e + 2) Γ ((prop q).somehow))) :
    G4c Δ (itpA p S (f + 2) (e + 1) Γ ((prop q).somehow)) :=
  gammaHead_budget_free p S hOr hq hsome f e e Γ Δ hΓS hamb hsrc

end Seal2Free
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Seal2Free.gammaHead_budget_free' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Seal2Free.gammaHead_budget_free

/--
info: 'PLLND.Seal2Free.gammaHead_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Seal2Free.gammaHead_descent

/-! **The statement is room-free.**  Pinned as a type check: the hypotheses are
the two matched-budget premises and the scope assumptions — no `defect`, no
`jumpGoals`, no budget inequality. -/

/--
info: PLLND.Seal2Free.gammaHead_budget_free (p : String) (S : Finset PLLFormula) (hOr : ∀ (A B : PLLFormula), A.or B ∉ S)
  {q : String} (hq : q ≠ p) (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) (f e c : ℕ) (Γ Δ : List PLLFormula)
  (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hamb : PLLND.G4c Δ (PLLND.itpE p S (f + 1) (e + 2) Γ))
  (hsrc : PLLND.G4c Δ (PLLND.itpA p S (f + 1) (e + 2) Γ (prop q).somehow)) :
  PLLND.G4c Δ (PLLND.itpA p S (f + 2) (c + 1) Γ (prop q).somehow)
-/
#guard_msgs in
#check PLLND.Seal2Free.gammaHead_budget_free
