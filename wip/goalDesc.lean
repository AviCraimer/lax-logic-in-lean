import wip.starve

/-!
# The goal side of the descent, branch by branch

## Why this is the right decomposition

The descent

    Δ ⊢ itpE p S (fl+1) (c+1) Γ ,  Δ ⊢ itpA p S (F+1) (c+1) Γ g
    ───────────────────────────────────────────────────────────
    Δ ⊢ itpA p S (fl+1) c Γ g                        (F ≤ fl)

is proved by eliminating the source disjunction and sending each source
disjunct to *some* target disjunct.  The disjuncts split into three
families (`itpAfull = itpAgoal ++ itpAenv ++ truncation`):

* the **goal** clauses, one family per shape of `g` — this file;
* the **environment** clauses, one family per shape of a context formula;
* the **truncation** disjunct, already discharged by `desc_of_oth`
  (`wip/cascadeBox.lean` §77).

The clause tables (`LaxLogic/PLLG4UITrunc.lean`) have a structural
property worth naming, because it explains what is hard and what is not:

> **every budget-decrementing recursive reference sits at the *same*
> context, and every context-growing reference sits at the *same* budget.**

(The one apparent exception, the `C₁ ∈ Γ` branch of the `⊃`-goal clause,
grows the context by a formula already in it, so the defect is unchanged —
`defect_cons_eq`.)  Consequently the recursion is well-founded on the
lexicographic pair `(defect, budget)` with no pigeonhole argument at all:
each recursive call drops the defect at fixed budget, or drops the budget
at fixed defect.  What the pigeonhole was for is *not* termination — it is
the fact that the budget's base case is **false** (`wip/floorRefute.lean`:
the descent to budget `0`), so a proof must show the low-budget instances
actually reached are harmless.

This file settles that question for the goal side.  Of the seven goal
families, **six close outright**, and each of the six needs only one of
two mechanisms:

| goal `g` | gated? | mechanism | status |
|---|---|---|---|
| `prop q` | no | inject the same disjunct | closed |
| `⊥` | no | no goal clause exists | vacuous |
| `C₁ ∧ C₂` | no | descent at `C₁`, `C₂` (smaller goal) | closed |
| `C₁ ∨ C₂` | no | descent at `C₁` or `C₂` | closed |
| `C₁ ⊃ C₂`, `C₁ ∈ Γ` | yes | ambient ⇒ guard, then descent at `C₂` | closed |
| `◯D` | yes | `box_open`, ambient ⇒ guard, descent at `D` | **closed** |
| `C₁ ⊃ C₂`, `C₁ ∉ Γ` | no | needs the ascent at a fresh antecedent | `FreshAntAscent` |

The two gated rows are the interesting ones.  Both would seem to need the
descent one budget lower, and at `c = 1` that is the refuted descent to
budget `0`.  They do not: the gated goal clause demotes only its
**existential** component to `b−1`, keeping its universal component at `b`
(clause table, `itpAgoal`).  The demoted existential is then supplied by
the *ambient* at budget `c+1` through downward existential monotonicity —
free, unconditional, no ascent and no descent.  **The budget is never
lowered on the universal side by a goal clause at all**; the goal weight
pays instead.  So no goal branch touches the refuted budget-`0` base case,
and the whole low-budget difficulty of the descent lives in the
*environment* clauses.

That is the point of isolating the goal side: it removes six of the seven
goal families from the problem outright, and shows that the seventh needs
one specific thing.

Attribution and novelty, to be exact about what is new here.  These six
branches are *already* discharged inside `oth_descent`
(`wip/cascadeBox.lean`, the `hφ ∈ itpAgoal` half of its case analysis) —
the `◯`-goal branch there uses `box_remap_free` where this file uses
`box_open`, and neither consumes any of that file's four interfaces.  What
this file adds is not a new theorem about the tables but a **public,
standalone, per-branch statement of what each goal family requires**, with
the fuel and budget bookkeeping exposed rather than buried in a
thousand-line induction.  That is what makes the requirement analysis
above checkable, and it is what the remaining work needs.

The one goal family that resists is the **fresh antecedent**.  Its clause
is not budget-gated, so the budget is no help; the *defect* does pay for it
(the descent's side condition `g ∈ S` plus piece-closure gives `C₁ ∈ S`, so
`defect S (C₁::Γ) < defect S Γ`).  What is unpaid is the **ambient at the
grown context**: to fire the source's guard we must raise the introduced
`E@c(C₁::Γ)` to `E@(c+1)(C₁::Γ)`, financed only by the ambient at the
*ungrown* `Γ`.  That is the ambient-relative existential ascent, refuted at
`c = 1` (`wip/ascRefute.lean` §1) and with no certified failure at `c ≥ 2`
(`wip/ascprobe.lean`).  It is isolated here as `FreshAntAscent`.
-/

open PLLFormula

namespace PLLND
namespace GoalDesc

/-! ## 1. Plumbing -/

/-- Consume a one-hypothesis lemma under a deriving context. -/
theorem consume₁ {Δ : List PLLFormula} {X Z : PLLFormula}
    (dX : G4c Δ X) (L : G4c [X] Z) : G4c Δ Z :=
  G4c.cut dX (wksub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) L)

/-- First projection out of a derivable conjunction. -/
theorem projAnd₁ {Δ : List PLLFormula} {X Y : PLLFormula}
    (d : G4c Δ (X.and Y)) : G4c Δ X :=
  G4c.cut d (G4c.andL (List.Perm.refl _) (G4c.identity_mem (.head _)))

/-- Second projection. -/
theorem projAnd₂ {Δ : List PLLFormula} {X Y : PLLFormula}
    (d : G4c Δ (X.and Y)) : G4c Δ Y :=
  G4c.cut d (G4c.andL (List.Perm.refl _)
    (G4c.identity_mem (.tail _ (.head _))))

/-- Fire a derivable implication with a derivable antecedent. -/
theorem fire {Δ : List PLLFormula} {X Y : PLLFormula}
    (dImp : G4c Δ (X.ifThen Y)) (dX : G4c Δ X) : G4c Δ Y :=
  G4c.cut dX (G4c.cut (dImp.weaken X) (wksub (by
    intro ψ hψ
    simp only [List.mem_cons] at hψ ⊢
    tauto) (G4c.mp X Y (X :: Δ))))

/-- Multi-step fuel monotonicity of the existential table (the single-step
form `itp_fuel_mono` is public; this is its `≤`-closure, which
`wip/absorb_base.lean` and `wip/cascadeBox.lean` each keep private). -/
theorem fuelE_le (p : String) (S : Finset PLLFormula) {f f' : Nat}
    (h : f ≤ f') (b : Nat) (Γ : List PLLFormula) :
    G4c [itpE p S f' b Γ] (itpE p S f b Γ) := by
  induction h with
  | refl => exact G4c.iden (.head _)
  | @step m _ ih =>
      exact G4c.cut ((itp_fuel_mono p S m).1 b Γ)
        ((ih.weaken _).perm (List.Perm.swap _ _ _))

/-- **The ambient supplies every weaker existential table.**  From the
ambient at fuel `f'` and budget `b'`, any table at lower fuel, lower budget
and set-equal context follows — the three monotonicity directions that are
free (`itp_fuel_mono`, `itp_budget_mono_le`, `itp_congr`).  This is the
only thing the two budget-gated goal branches need in place of a descent. -/
theorem ambE (p : String) (S : Finset PLLFormula) {f f' b b' : Nat}
    {Γ Γ' : List PLLFormula} {Δ : List PLLFormula}
    (hf : f ≤ f') (hb : b ≤ b') (hΓ : Γ.toFinset = Γ'.toFinset)
    (hamb : G4c Δ (itpE p S f' b' Γ)) : G4c Δ (itpE p S f b Γ') := by
  refine consume₁ hamb ?_
  refine G4c.cut (fuelE_le p S hf b' Γ) ?_
  refine G4c.cut ((((itp_budget_mono_le p S hb f).1 Γ).weaken _).perm
    (List.Perm.swap _ _ _)) ?_
  exact wksub (by
    intro ψ hψ
    rcases List.mem_singleton.mp hψ with rfl
    exact .head _) ((itp_congr p S f).1 b Γ Γ' hΓ)

/-! ## 2. The ungated goal branches -/

/-- **Atom goal.**  The goal clause is the atom itself at every budget, so
the source disjunct *is* the target disjunct. -/
theorem desc_goal_atom {Δ : List PLLFormula} {q : String}
    (hsrc : G4c Δ (prop q)) : G4c Δ (prop q) := hsrc

/-- **Conjunctive goal.**  Both components descend at a strictly smaller
goal, same context, same budget step. -/
theorem desc_goal_and (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {C₁ C₂ : PLLFormula}
    (hrec₁ : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpA p S F (c + 1) Γ C₁) → G4c Δ' (itpA p S fl c Γ C₁))
    (hrec₂ : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpA p S F (c + 1) Γ C₂) → G4c Δ' (itpA p S fl c Γ C₂))
    (hsrc : G4c Δ ((itpA p S F (c + 1) Γ C₁).and
      (itpA p S F (c + 1) Γ C₂))) :
    G4c Δ ((itpA p S fl c Γ C₁).and (itpA p S fl c Γ C₂)) :=
  G4c.andR (hrec₁ Δ (projAnd₁ hsrc)) (hrec₂ Δ (projAnd₂ hsrc))

/-- **Disjunctive goal.**  The two components are *separate* disjuncts of
the table (the enclosing `orAll` supplies the disjunction), so each maps to
its own target disjunct — no case analysis needed. -/
theorem desc_goal_or (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {C : PLLFormula}
    (hrec : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpA p S F (c + 1) Γ C) → G4c Δ' (itpA p S fl c Γ C))
    (hsrc : G4c Δ (itpA p S F (c + 1) Γ C)) :
    G4c Δ (itpA p S fl c Γ C) := hrec Δ hsrc

/-! ## 3. The two budget-gated goal branches

Both are stated at target budget `c + 1` (so the demoted component sits at
`c`, and the *source* is at budget `c + 2`).  In both the demoted component
is existential and comes from the ambient. -/

/-- **`◯`-goal — the γ-goal seal, closed.**

    source   ◯( E@(c+1)(Γ)  ⇢  A@(c+2)(Γ, D) )
    target   ◯( E@c(Γ)      ⇢  A@(c+1)(Γ, D) )

Open the source box against the `◯`-shaped target (`box_open`), firing its
guard `E@(c+1)(Γ)` from the ambient at budget `c + 2` by downward
existential monotonicity; inside, introduce the target's own guard and
finish by the descent at the strictly smaller goal `D`.

No descent at a lower budget is used, so nothing here touches the refuted
budget-`0` base case. -/
theorem desc_goal_box (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {D : PLLFormula}
    (hF : F ≤ fl + 1)
    (hrec : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 2) Γ) →
      G4c Δ' (itpA p S F (c + 2) Γ D) →
      G4c Δ' (itpA p S fl (c + 1) Γ D))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ))
    (hsrc : G4c Δ (((itpE p S F (c + 1) Γ).ifThen
      (itpA p S F (c + 2) Γ D)).somehow)) :
    G4c Δ (((itpE p S fl c Γ).ifThen
      (itpA p S fl (c + 1) Γ D)).somehow) := by
  refine box_open hsrc (ambE p S hF (by omega) rfl hamb) ?_
  refine G4c.laxR (G4c.impR ?_)
  exact hrec _ ((hamb.weaken _).weaken _)
    (G4c.identity_mem (.tail _ (.head _)))

/-- **Presented-antecedent `⊃`-goal, closed.**  With `C₁ ∈ Γ` the clause is
budget-gated, and again only its existential component is demoted:

    source   E@(c+1)(C₁::Γ)  ⇢  A@(c+2)(C₁::Γ, C₂)
    target   E@c(C₁::Γ)      ⇢  A@(c+1)(C₁::Γ, C₂)

`C₁ ∈ Γ` makes `C₁::Γ` set-equal to `Γ`, so the ambient at `Γ` supplies the
source's guard directly (`ambE`, using `itp_congr`); the rest is the descent
at the smaller goal `C₂`. -/
theorem desc_goal_imp_pres (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {C₁ C₂ : PLLFormula}
    (hF : F ≤ fl + 1) (hmem : C₁ ∈ Γ)
    (hrec : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 2) (C₁ :: Γ)) →
      G4c Δ' (itpA p S F (c + 2) (C₁ :: Γ) C₂) →
      G4c Δ' (itpA p S fl (c + 1) (C₁ :: Γ) C₂))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 2) Γ))
    (hsrc : G4c Δ ((itpE p S F (c + 1) (C₁ :: Γ)).ifThen
      (itpA p S F (c + 2) (C₁ :: Γ) C₂))) :
    G4c Δ ((itpE p S fl c (C₁ :: Γ)).ifThen
      (itpA p S fl (c + 1) (C₁ :: Γ) C₂)) := by
  have hset : Γ.toFinset = (C₁ :: Γ).toFinset := by
    simp only [List.toFinset_cons]
    exact (Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hmem)).symm
  refine G4c.impR ?_
  refine hrec _ (ambE p S (Nat.le_refl _) (Nat.le_refl _) hset (hamb.weaken _))
    (fire (hsrc.weaken _)
      (ambE p S hF (by omega) hset (hamb.weaken _)))

/-! ## 4. The fresh-antecedent goal branch: the unpaid seal

    source   E@(c+1)(C₁::Γ)  ⇢  A@(c+1)(C₁::Γ, C₂)
    target   E@c(C₁::Γ)      ⇢  A@c(C₁::Γ, C₂)

This clause is *not* budget-gated (both components stay at `b`), so the
budget is no help; and the context grows by `C₁` with **no `C₁ ∈ S`
requirement** (`itpAgoal`, the `C₁ ∉ Γ` branch — goal-driven growth is
unguarded, the goal weight is supposed to pay).  So the defect need not
drop either.  To fire the source we must raise the introduced guard
`E@c(C₁::Γ)` to `E@(c+1)(C₁::Γ)`, financed by the ambient at the *ungrown*
context: exactly the ambient-relative existential ascent.

It is refuted at `c = 1` (`wip/ascRefute.lean` §1) and has no certified
failure at `c ≥ 2` in any probed configuration (`wip/ascprobe.lean`: the
boundary is flat at `≤ 2` up to four live gates and defect 15).  It is
stated here as a hypothesis rather than assumed silently. -/

/-- The ambient-relative existential ascent at a fresh antecedent — the
same statement as `AmbGuardAscent` of `wip/cascadeBox.lean`, restated here
so this file stands alone. -/
def FreshAntAscent (p : String) (S : Finset PLLFormula) : Prop :=
  ∀ (fl c : Nat) (Γ : List PLLFormula) (C₁ : PLLFormula)
    (Δ : List PLLFormula),
    C₁ ∈ S → C₁ ∉ Γ → (∀ Y ∈ Γ, Y ∈ S) →
    G4c Δ (itpE p S (fl + 1) (c + 1) Γ) →
    G4c (itpE p S fl c (C₁ :: Γ) :: Δ) (itpE p S fl (c + 1) (C₁ :: Γ))

/-- **Fresh-antecedent `⊃`-goal, reduced.**  The branch closes given the
ascent and the descent at the grown context (which is at strictly smaller
defect, since piece-closure puts `C₁` in `S`, so the defect tier pays for
it — what is *not* paid for is the ambient at the grown context, and that
is exactly the ascent). -/
theorem desc_goal_imp_fresh (p : String) (S : Finset PLLFormula)
    (hasc : FreshAntAscent p S)
    {F fl c : Nat} {Γ Δ : List PLLFormula} {C₁ C₂ : PLLFormula}
    (hF : F ≤ fl) (hC₁S : C₁ ∈ S) (hfresh : C₁ ∉ Γ)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hrec : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S fl (c + 1) (C₁ :: Γ)) →
      G4c Δ' (itpA p S F (c + 1) (C₁ :: Γ) C₂) →
      G4c Δ' (itpA p S fl c (C₁ :: Γ) C₂))
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 1) Γ))
    (hsrc : G4c Δ ((itpE p S F (c + 1) (C₁ :: Γ)).ifThen
      (itpA p S F (c + 1) (C₁ :: Γ) C₂))) :
    G4c Δ ((itpE p S fl c (C₁ :: Γ)).ifThen
      (itpA p S fl c (C₁ :: Γ) C₂)) := by
  refine G4c.impR ?_
  have hup : G4c (itpE p S fl c (C₁ :: Γ) :: Δ)
      (itpE p S fl (c + 1) (C₁ :: Γ)) :=
    hasc fl c Γ C₁ Δ hC₁S hfresh hΓS hamb
  exact hrec _ hup
    (fire (hsrc.weaken _)
      (consume₁ hup (fuelE_le p S hF (c + 1) (C₁ :: Γ))))

/-! ## 5. Dropping the budget floor at non-boxed goals

`desc_of_oth` (`wip/cascadeBox.lean`) reduces the full-table descent to the
others-descent, and carries `1 ≤ c`.  That hypothesis is used in exactly one
place: the truncation disjunct, which the table appends **only** for a
`◯`-shaped goal (`itpAfull`).  For every other goal the full table *is* the
others-table, and the reduction is a one-line pass-through needing no budget
at all.

Splitting the wrapper by goal shape therefore replaces the uniform floor
`∀ S Γ g, 1 ≤ need S Γ g` — which killed the gate-count candidate and the
bare product (`wip/descent2.lean` §4) — by a floor **on boxed goals only**.
That is what makes a goal-shape budget law admissible. -/

/-- **The full-table descent at a non-boxed goal, with no budget floor.**
For `g` not of the form `◯D` the full table is the others-table, so the
others-descent transfers directly. -/
theorem desc_of_oth_nonbox (p : String) (S : Finset PLLFormula)
    {F fl c : Nat} {Γ : List PLLFormula} {g : PLLFormula}
    (hg : ∀ D : PLLFormula, g ≠ D.somehow)
    (hoth : ∀ (Δ' : List PLLFormula),
      G4c Δ' (itpE p S (fl + 1) (c + 1) Γ) →
      G4c Δ' (orAll (itpAoth p S F (c + 1) Γ g)) →
      G4c Δ' (orAll (itpAoth p S fl c Γ g)))
    {Δ : List PLLFormula}
    (hamb : G4c Δ (itpE p S (fl + 1) (c + 1) Γ))
    (hhead : G4c Δ (itpA p S (F + 1) (c + 1) Γ g)) :
    G4c Δ (itpA p S (fl + 1) c Γ g) := by
  rw [itpA_succ] at hhead ⊢
  refine G4c.cut hhead (G4c.orAll_elim ?_)
  intro φ hφ
  cases g with
  | somehow D => exact absurd rfl (hg D)
  | prop q =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | falsePLL =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | and C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | or C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))
  | ifThen C₁ C₂ =>
      simp only [itpAfull] at hφ ⊢
      exact hoth (φ :: Δ) (hamb.weaken φ)
        (G4c.orAll_intro hφ (G4c.identity_mem (.head _)))

end GoalDesc
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.GoalDesc.desc_goal_box' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.GoalDesc.desc_goal_box

/--
info: 'PLLND.GoalDesc.desc_goal_imp_pres' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.GoalDesc.desc_goal_imp_pres

/--
info: 'PLLND.GoalDesc.desc_goal_imp_fresh' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.GoalDesc.desc_goal_imp_fresh

/--
info: 'PLLND.GoalDesc.desc_of_oth_nonbox' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.GoalDesc.desc_of_oth_nonbox
