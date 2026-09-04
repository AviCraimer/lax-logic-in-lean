import wip.boxSnd

/-!
# The boxed traversal at the budgets its consumer actually supplies

## Why this file exists

`wip/boxSnd.lean`'s `boxSnd_reaches` runs the boxed second-component traversal with

    ambient  E@(f+1)(c+2)(Γ')        source  A@(f+1)(c+1)(Γ', ◯q)

i.e. **ambient budget = source budget + 1**, and it delivers the target at the one
budget `c` tied to that pair.

The consumer is `GammaPairFloorBox` (`wip/cascadeBox.lean`), one of the four open
interfaces of `cascade_box`.  What it hands its branch is

    ambient  E@(fl+1)(2)(Γ)          second component  A@(F+1)(2)(B::Γ, g)

i.e. **ambient budget = source budget**, both `2`, with the target at budget `1`.
So the apparatus built over PROGRESS §§92–112 does not fit its own interface: it
asks for one more budget of ambient than the descent ever has at the floor, and
`itpA` weakens *upwards* in the budget, so the source at `2` cannot be demoted to
the `1` the coupled statement wants — that demotion **is** the descent.

This is §112's lesson one level up: check that the statement is what the *consumer*
supplies, not only what the traversal supplies.

## What is done here

The traversal is re-run with the two budgets **decoupled**:

    ambient  E@(f+1)(e+2)(Γ')        source  A@(f+1)(e+2)(Γ', ◯q)
    target   ◯( E@(f,c)(Γ) ⇢ A@(f+1,c+1)(Γ, q) )      for ARBITRARY `c`

and it is *easier*, not harder: with the ambient at the source's own budget, every
gated environment disjunct's first component sits exactly at the budget the ambient's
matching conjunct demands, so §107's three budget shifts are not needed at all.  The
target budget is a free rider throughout — the only place the target is produced is
the goal clause, and there the value conversion is `itpA_atom_forces`, which holds at
**every** budget (that is precisely the property §91 was proved for).

The pay-off is `gammaPairFloorBox_boxedAtom`: the boxed γ-pair floor interface, at a
boxed **atom** goal over a `∨`-free space, PROVED — the first instance of any of
`cascade_box`'s four open interfaces to be discharged.
-/

open PLLFormula

namespace PLLND
namespace BoxSndTight

open GoalDesc AtomForce EnvDesc BoxSnd

/-! ## 1. The goal clause, budget-free

`AtomForce.boxGoal_remap` ties the source's guard budget, the source's value budget
and the target's budget together.  None of the three is used: the guard comes from
the grown ambient by downward monotonicity (any budget above the source's guard),
and the value is `itpA_atom_forces`, which ignores the budget entirely. -/

/-- **The boxed goal clause remaps at unrelated budgets.**  `y ≤ x` is the only
budget relation used; `z` and the target budget `c` are free. -/
theorem boxGoal_remap_free (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {f x y z c : Nat} {Γ Γ' Δ : List PLLFormula}
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S) (hyx : y ≤ x)
    (hgrown : G4c Δ (itpE p S f x Γ'))
    (hbox : G4c Δ (((itpE p S f y Γ').ifThen
      (itpA p S f z Γ' (prop q))).somehow)) :
    G4c Δ (tgtClause p S f c Γ q) := by
  refine box_remap_free hbox ?_ ?_
  · exact ambE p S (Nat.le_refl _) hyx rfl (hgrown.weaken _)
  · have hatom : G4c (itpA p S f z Γ' (prop q) ::
        itpE p S f c Γ :: Δ) (prop q) :=
      consume₁ (G4c.identity_mem (.head _))
        (itpA_atom_forces p S hOr hq f z Γ' hΓ'S)
    rw [itpA_succ]
    refine G4c.orAll_intro (φ := prop q) ?_ hatom
    simp only [itpAfull, itpAoth, itpAgoal]
    refine List.mem_append.mpr (Or.inl ?_)
    rw [if_neg hq]
    exact .head _

/-! ## 2. The three gated grown ambients, unshifted

At the tight budgets the ambient's conjunct wants its antecedent at exactly the
budget the source disjunct carries it, so these are `EnvDesc.grownAmb_of_box`'s move
with no `shift_imp`/`shift_box` in front. -/

/-- Jump clause, `B₁⊃D` present. -/
theorem tGrownAmb_jump_pres (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∈ Γ) (hS : (A₁.ifThen B₁).ifThen D ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hfst : G4c Δ ((itpE p S f (c + 1) Γ).ifThen
      (itpA p S f (c + 1) Γ (A₁.ifThen B₁)))) :
    G4c Δ (itpE p S f (c + 2) (D :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_jump_mem_pres p S hmem hD hDS hBD hS)
      (G4c.identity_mem (.head _)))) hfst

/-- Jump clause, `B₁⊃D` fresh. -/
theorem tGrownAmb_jump_fresh (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A₁ B₁ D : PLLFormula}
    (hmem : (A₁.ifThen B₁).ifThen D ∈ Γ) (hD : D ∉ Γ) (hDS : D ∈ S)
    (hBD : B₁.ifThen D ∉ Γ) (hBDS : B₁.ifThen D ∈ S)
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hfst : G4c Δ ((itpE p S f (c + 2) (B₁.ifThen D :: Γ)).ifThen
      (itpA p S f (c + 2) (B₁.ifThen D :: Γ) (A₁.ifThen B₁)))) :
    G4c Δ (itpE p S f (c + 2) (D :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_jump_mem_fresh p S hmem hD hDS hBD hBDS)
      (G4c.identity_mem (.head _)))) hfst

/-- γ-clause continuation, one per `◯x ∈ Γ`. -/
theorem tGrownAmb_gammaCont (p : String) (S : Finset PLLFormula) {f c : Nat}
    {Γ Δ : List PLLFormula} {A B x : PLLFormula}
    (hmem : A.somehow.ifThen B ∈ Γ) (hB : B ∉ Γ) (hBS : B ∈ S)
    (hx : x.somehow ∈ Γ) (hxc : ¬(x ∈ Γ ∨ x ∉ S))
    (hamb : G4c Δ (itpE p S (f + 1) (c + 2) Γ))
    (hbox : G4c Δ (((itpE p S f (c + 2) (x :: Γ)).ifThen
      (itpA p S f (c + 2) (x :: Γ) A.somehow)).somehow)) :
    G4c Δ (itpE p S f (c + 2) (B :: Γ)) := by
  rw [itpE_succ] at hamb
  exact fire (G4c.cut hamb
    (G4c.andAll_elim (amb_gammaCont_mem p S hmem hB hBS hx hxc)
      (G4c.identity_mem (.head _)))) hbox

/-! ## 3. The tight traversal -/

/-- The recursion, at the tight budgets. -/
abbrev TStep (p : String) (S : Finset PLLFormula) (q : String) (f e c : Nat)
    (Γ Γ' Δ : List PLLFormula) : Prop :=
  ∀ (Γ'' : List PLLFormula) (w : PLLFormula),
    (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
    w ∈ S → w ∈ Γ'' → w ∉ Γ' →
    G4c Δ (itpE p S (f + 1) (e + 2) Γ'') →
    G4c Δ (itpA p S (f + 1) (e + 2) Γ'' ((prop q).somehow)) →
    G4c Δ (tgtClause p S f c Γ q)

set_option maxHeartbeats 4000000 in
/-- **The traversal, ambient and source at the same budget, target free.** -/
theorem boxSnd_tight (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) :
    ∀ (d : Nat) (f e c : Nat) (Γ Γ' Δ : List PLLFormula),
      defect S Γ' ≤ d → (∀ Y ∈ Γ', Y ∈ S) →
      G4c Δ (itpE p S (f + 1) (e + 2) Γ') →
      G4c Δ (itpA p S (f + 1) (e + 2) Γ' ((prop q).somehow)) →
      G4c Δ (tgtClause p S f c Γ q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f e c Γ Γ' Δ hd hΓ'S hamb hsnd
  have othersOne : ∀ (Δ₀ : List PLLFormula) (φ : PLLFormula),
      φ ∈ itpAoth p S f (e + 2) Γ' ((prop q).somehow) →
      G4c Δ₀ (itpE p S (f + 1) (e + 2) Γ') → G4c Δ₀ φ →
      G4c Δ₀ (tgtClause p S f c Γ q) := by
    intro Δ₀ φ hoth hA hφd
    simp only [itpAoth] at hoth
    rcases List.mem_append.mp hoth with hgoal | henv
    · simp only [itpAgoal] at hgoal
      rcases List.mem_singleton.mp hgoal with rfl
      exact boxGoal_remap_free p S hOr hq hΓ'S (Nat.le_succ _)
        (ambE p S (Nat.le_succ _) (Nat.le_refl _) rfl hA) hφd
    · cases f with
      | zero => exact zeroFuelCase p S hq (e + 1) c Γ Γ' _ φ henv hφd
      | succ f' =>
          have step : TStep p S q f' e c Γ Γ' Δ₀ := by
            intro Γ'' w hsub hΓ''S hwS hwΓ'' hwΓ' hg'' hs''
            exact ihd (defect S Γ'')
              (by
                have := defect_lt_of_witness hsub hwS hwΓ'' hwΓ'
                omega)
              f' e c Γ Γ'' Δ₀ (Nat.le_refl _) hΓ''S hg'' hs''
          simp only [itpAenv] at henv
          obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp henv
          have hFS : F ∈ S := hΓ'S F hFΓ'
          cases F with
          | prop q' =>
              simp only at hin
              split at hin
              next hc =>
                exfalso
                have h2 : (prop q : PLLFormula).somehow = prop p := hc.2
                exact absurd h2 (by simp)
              next => cases hin
          | falsePLL => cases hin
          | or A B => exact absurd hFS (hOr A B)
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hcond =>
                rcases List.mem_singleton.mp hin with rfl
                -- both boxed: open the grown ambient, open the disjunct against
                -- it (the guard matches EXACTLY at the tight budgets), recurse
                refine G4c.cut (grown_box p S hFΓ' hcond hA)
                  (G4c.laxL (.head _) ?_)
                refine box_open (wksub (fun ψ h => .tail _ (.tail _ h)) hφd)
                  (G4c.identity_mem (.head _)) ?_
                refine tgtClause_fuel_lift p S ?_
                exact ihd (defect S (χ :: Γ'))
                  (by
                    have := defect_lt_of_witness
                      (Γ := Γ') (Γ' := χ :: Γ') (fun y hy => .tail _ hy)
                      (hsome hFS) (List.mem_cons_self ..)
                      (fun h => hcond (Or.inl h))
                    omega)
                  f' e c Γ (χ :: Γ') _ (Nat.le_refl _)
                  (by
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hy
                    · exact hsome hFS
                    · exact hΓ'S y hy)
                  (G4c.identity_mem (.tail _ (.head _)))
                  (G4c.identity_mem (.head _))
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  by_cases hAin : A ∈ Γ'
                  · have hB : B ∉ Γ' := fun hB => h1 ⟨hAin, hB⟩
                    have hBS : B ∈ S := h2.2.resolve_left hB
                    exact step (A :: B :: Γ') B
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hΓ'S _ hAin
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hBS
                        · exact hΓ'S y hy)
                      hBS (.tail _ (.head _)) hB
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                  · have hAS : A ∈ S := h2.1.resolve_left hAin
                    exact step (A :: B :: Γ') A
                      (fun y hy => .tail _ (.tail _ hy))
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hAS
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                        · exact hΓ'S y hy)
                      hAS (.head _) hAin
                      (grown_and p S hFΓ' h1 h2 hA) hφd |> tgtClause_fuel_lift p S
                next => cases hin
          | ifThen A D =>
              cases A with
              | falsePLL => cases hin
              | prop q' =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      split at hin
                      next h3 =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine tgtClause_fuel_lift p S
                          (step (D :: Γ') D (fun y hy => .tail _ hy) ?_ h2
                            (.head _) h1
                            (grown_impAtom_pres p S hFΓ' h1 h2 h3 hA) hφd)
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact h2
                        · exact hΓ'S y hy
                      next h3 =>
                        split at hin
                        next => cases hin
                        next h4 =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine tgtClause_fuel_lift p S
                            (step (D :: Γ') D (fun y hy => .tail _ hy) ?_ h2
                              (.head _) h1
                              (grown_impAtom_fresh p S hFΓ' h1 h2 h3 h4 hA
                                (projAnd₁ hφd)) (projAnd₂ hφd))
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact h2
                          · exact hΓ'S y hy
                    next => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine tgtClause_fuel_lift p S
                        (step (A₁.ifThen (B₁.ifThen D) :: Γ')
                          (A₁.ifThen (B₁.ifThen D)) (fun y hy => .tail _ hy) ?_
                          h2 (.head _) h1
                          (grown_impAnd p S hFΓ' h1 h2 hA) hφd)
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact h2
                      · exact hΓ'S y hy
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      by_cases hAD : A₁.ifThen D ∈ Γ'
                      · have hBD : B₁.ifThen D ∉ Γ' := fun h => h1 ⟨hAD, h⟩
                        have hBDS : B₁.ifThen D ∈ S := h2.2.resolve_left hBD
                        refine tgtClause_fuel_lift p S
                          (step (A₁.ifThen D :: B₁.ifThen D :: Γ')
                            (B₁.ifThen D) (fun y hy => .tail _ (.tail _ hy)) ?_
                            hBDS (.tail _ (.head _)) hBD
                            (grown_impOr p S hFΓ' h1 h2 hA) hφd)
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hΓ'S _ hAD
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hBDS
                        · exact hΓ'S y hy
                      · have hADS : A₁.ifThen D ∈ S := h2.1.resolve_left hAD
                        refine tgtClause_fuel_lift p S
                          (step (A₁.ifThen D :: B₁.ifThen D :: Γ')
                            (A₁.ifThen D) (fun y hy => .tail _ (.tail _ hy)) ?_
                            hADS (.head _) hAD
                            (grown_impOr p S hFΓ' h1 h2 hA) hφd)
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact hADS
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                        · exact hΓ'S y hy
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  by_cases h1 : D ∈ Γ'
                  · simp only [if_pos h1] at hin; cases hin
                  simp only [if_neg h1] at hin
                  by_cases h2 : D ∈ S
                  case neg => simp only [if_neg h2] at hin; cases hin
                  simp only [if_pos h2] at hin
                  by_cases h3 : B₁.ifThen D ∈ Γ'
                  · simp only [if_pos h3, if_pos hFS] at hin
                    rcases List.mem_singleton.mp hin with rfl
                    refine tgtClause_fuel_lift p S
                      (step (D :: Γ') D (fun y hy => .tail _ hy) ?_ h2
                        (.head _) h1
                        (tGrownAmb_jump_pres p S hFΓ' h1 h2 h3 hFS hA
                          (projAnd₁ hφd)) (projAnd₂ hφd))
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hy
                    · exact h2
                    · exact hΓ'S y hy
                  · simp only [if_neg h3] at hin
                    by_cases h4 : B₁.ifThen D ∈ S
                    · simp only [if_pos h4] at hin
                      rcases List.mem_singleton.mp hin with rfl
                      refine tgtClause_fuel_lift p S
                        (step (D :: Γ') D (fun y hy => .tail _ hy) ?_ h2
                          (.head _) h1
                          (tGrownAmb_jump_fresh p S hFΓ' h1 h2 h3 h4 hA
                            (projAnd₁ hφd)) (projAnd₂ hφd))
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact h2
                      · exact hΓ'S y hy
                    · simp only [if_neg h4] at hin; cases hin
              | somehow A₁ =>
                  simp only at hin
                  by_cases h1 : D ∈ Γ'
                  · simp only [if_pos h1] at hin; cases hin
                  simp only [if_neg h1] at hin
                  by_cases h2 : D ∈ S
                  case neg => simp only [if_neg h2] at hin; cases hin
                  simp only [if_pos h2, if_pos hFS] at hin
                  have hgrow : ∀ y ∈ D :: Γ', y ∈ S := by
                    intro y hy
                    rcases List.mem_cons.mp hy with rfl | hy
                    · exact h2
                    · exact hΓ'S y hy
                  rcases List.mem_append.mp hin with hL | hR
                  · rcases List.mem_cons.mp hL with rfl | hL'
                    · exact tgtClause_fuel_lift p S
                        (step (D :: Γ') D (fun y hy => .tail _ hy) hgrow h2
                          (.head _) h1
                          (grownAmb_of_plain p S hFΓ' hFS h1 h2 hA
                            (projAnd₁ hφd)) (projAnd₂ hφd))
                    · rcases List.mem_singleton.mp hL' with rfl
                      exact tgtClause_fuel_lift p S
                        (step (D :: Γ') D (fun y hy => .tail _ hy) hgrow h2
                          (.head _) h1
                          (grownAmb_of_box p S hFΓ' hFS h1 h2 hA
                            (projAnd₁ hφd)) (projAnd₂ hφd))
                  · obtain ⟨X, hXΓ', hXin⟩ := List.mem_filterMap.mp hR
                    cases X with
                    | prop _ => cases hXin
                    | falsePLL => cases hXin
                    | and _ _ => cases hXin
                    | or _ _ => cases hXin
                    | ifThen _ _ => cases hXin
                    | somehow x =>
                        simp only at hXin
                        by_cases hx : x ∈ Γ' ∨ x ∉ S
                        · simp only [if_pos hx] at hXin
                          cases hXin
                        · simp only [if_neg hx] at hXin
                          rcases Option.some_inj.mp hXin with rfl
                          exact tgtClause_fuel_lift p S
                            (step (D :: Γ') D (fun y hy => .tail _ hy) hgrow h2
                              (.head _) h1
                              (tGrownAmb_gammaCont p S hFΓ' h1 h2 hXΓ' hx hA
                                (projAnd₁ hφd)) (projAnd₂ hφd))
  have othersAll : ∀ (Δ₀ : List PLLFormula),
      G4c Δ₀ (itpE p S (f + 1) (e + 2) Γ') →
      G4c Δ₀ (orAll (itpAoth p S f (e + 2) Γ' ((prop q).somehow))) →
      G4c Δ₀ (tgtClause p S f c Γ q) := by
    intro Δ₀ hA hor
    refine G4c.cut hor (G4c.orAll_elim ?_)
    intro φ hφ
    exact othersOne (φ :: Δ₀) φ hφ (hA.weaken φ) (G4c.identity_mem (.head _))
  rw [itpA_succ] at hsnd
  refine G4c.cut hsnd (G4c.orAll_elim ?_)
  intro φ hφ
  have hA : G4c (φ :: Δ) (itpE p S (f + 1) (e + 2) Γ') := hamb.weaken φ
  have hφd : G4c (φ :: Δ) φ := G4c.identity_mem (.head _)
  simp only [itpAfull] at hφ
  rcases List.mem_append.mp hφ with hoth | htr
  · exact othersOne (φ :: Δ) φ hoth hA hφd
  · by_cases he : (itpAoth p S f (e + 2) Γ' ((prop q).somehow)).isEmpty = true
    · rw [if_pos he] at htr; cases htr
    · rw [if_neg he] at htr
      rcases List.mem_singleton.mp htr with rfl
      refine box_open hφd (ambE p S (Nat.le_succ _) (by omega) rfl hA) ?_
      exact othersAll _ (hA.weaken _) (G4c.identity_mem (.head _))

/-! ## 4. The consumer: `GammaPairFloorBox` at a boxed atom goal

`wip/cascadeBox.lean`'s `GammaPairFloorBox` is one of the four open interfaces of
`cascade_box`.  Its data, at target budget `1`:

    F + 1 ≤ fl,  ◯A ⊃ B ∈ Γ ∩ S,  B ∈ S ∖ Γ,  Γ ⊆ S
    ambient            E@(fl+1)(2)(Γ)
    first component    ◯( E@(F+1)(1)(Γ) ⇢ A@(F+1)(1)(Γ, ◯A) )
    second component   A@(F+1)(2)(B::Γ, g)
    ────────────────────────────────────────────────────────
    ⋁ itpAoth@(fl)(1)(Γ, g)

At `g = ◯(prop q)` with `q ≠ p` over a `∨`-free space this closes, and the route uses
**no** defect recursion (the interface's own recursion hypothesis is not consumed):

1. lift the first component to the ambient's fuel — free in both slots
   (`fuelE_le` down on the guard, `fuelA_le` up on the value);
2. fire the ambient's γ-conjunct with it (`grownAmb_of_box`, §98) to get the grown
   ambient `E@(fl)(2)(B::Γ)`;
3. lift the second component to the same fuel and run `boxSnd_tight` at
   `e = 0`, `c = 0`;
4. the result differs from the target's own goal clause by one fuel on the guard,
   free by `fuelE_le`. -/

/-- Multi-step fuel monotonicity of the **universal** table (the `≤`-closure of
`itp_fuel_mono`; `GoalDesc.fuelE_le` is the existential mate). -/
theorem fuelA_le (p : String) (S : Finset PLLFormula) {f f' : Nat}
    (h : f ≤ f') (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    G4c [itpA p S f b Γ C] (itpA p S f' b Γ C) := by
  induction h with
  | refl => exact G4c.iden (.head _)
  | @step m _ ih => exact consume₁ ih ((itp_fuel_mono p S m).2 b Γ C)

/-- **The boxed γ-pair floor interface, at a boxed atom goal.**  The first instance
of any of `cascade_box`'s four open interfaces to be discharged. -/
theorem gammaPairFloorBox_boxedAtom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (F fl : Nat) (Γ : List PLLFormula) (A B : PLLFormula) (Δ : List PLLFormula)
    (hF : F + 1 ≤ fl)
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hBS : B ∈ S) (hB : B ∉ Γ) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hamb : G4c Δ (itpE p S (fl + 1) 2 Γ))
    (hbox : G4c Δ (((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ A.somehow)).somehow))
    (hsnd : G4c Δ (itpA p S (F + 1) 2 (B :: Γ) ((prop q).somehow))) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ ((prop q).somehow))) := by
  obtain ⟨f0, rfl⟩ : ∃ f0, fl = f0 + 1 := ⟨fl - 1, by omega⟩
  have hboxL : G4c Δ (((itpE p S (f0 + 1) 1 Γ).ifThen
      (itpA p S (f0 + 1) 1 Γ A.somehow)).somehow) := by
    refine box_remap_free hbox ?_ ?_
    · exact consume₁ (G4c.identity_mem (.head _)) (fuelE_le p S hF 1 Γ)
    · exact consume₁ (G4c.identity_mem (.head _))
        (fuelA_le p S hF 1 Γ A.somehow)
  have hgrown : G4c Δ (itpE p S (f0 + 1) 2 (B :: Γ)) :=
    grownAmb_of_box p S hmem hS hB hBS hamb hboxL
  have hsndL : G4c Δ (itpA p S (f0 + 1) 2 (B :: Γ) ((prop q).somehow)) :=
    consume₁ hsnd (fuelA_le p S hF 2 (B :: Γ) ((prop q).somehow))
  have hBΓS : ∀ Y ∈ B :: Γ, Y ∈ S := by
    intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hBS
    · exact hΓS Y hY
  have htgt : G4c Δ (tgtClause p S f0 0 Γ q) :=
    boxSnd_tight p S hOr hq hsome (defect S (B :: Γ)) f0 0 0 Γ (B :: Γ) Δ
      (Nat.le_refl _) hBΓS hgrown hsndL
  refine G4c.orAll_intro (φ := (((itpE p S (f0 + 1) 0 Γ).ifThen
    (itpA p S (f0 + 1) 1 Γ (prop q))).somehow)) ?_ ?_
  · simp only [itpAoth, itpAgoal]
    exact List.mem_append.mpr (Or.inl (.head _))
  · refine box_remap_free htgt ?_ ?_
    · exact consume₁ (G4c.identity_mem (.head _))
        (fuelE_le p S (Nat.le_succ f0) 0 Γ)
    · exact G4c.identity_mem (.head _)

/-! ## 5. The same route serves all three floor interfaces

`gammaPairFloorBox_boxedAtom` uses its first component for exactly one thing: to fire
the ambient's matching conjunct and obtain the **grown ambient** at `B::Γ`.  So the
content is one lemma — grown ambient plus second component — and the three interfaces
differ only in which `itpEcls` conjunct their first component fires.  That is §98's
observation applied at the floor. -/

/-- **The floor branch at a boxed atom goal, from the grown ambient.**  The shared
core of all three pair-floor interfaces. -/
theorem floorBox_of_grownAmb (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    {F fl : Nat} {Γ Δ : List PLLFormula} {B : PLLFormula}
    (hF : F + 1 ≤ fl) (hBS : B ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hgrown : G4c Δ (itpE p S fl 2 (B :: Γ)))
    (hsnd : G4c Δ (itpA p S (F + 1) 2 (B :: Γ) ((prop q).somehow))) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ ((prop q).somehow))) := by
  obtain ⟨f0, rfl⟩ : ∃ f0, fl = f0 + 1 := ⟨fl - 1, by omega⟩
  have hBΓS : ∀ Y ∈ B :: Γ, Y ∈ S := by
    intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hBS
    · exact hΓS Y hY
  have hsndL : G4c Δ (itpA p S (f0 + 1) 2 (B :: Γ) ((prop q).somehow)) :=
    consume₁ hsnd (fuelA_le p S hF 2 (B :: Γ) ((prop q).somehow))
  have htgt : G4c Δ (tgtClause p S f0 0 Γ q) :=
    boxSnd_tight p S hOr hq hsome (defect S (B :: Γ)) f0 0 0 Γ (B :: Γ) Δ
      (Nat.le_refl _) hBΓS hgrown hsndL
  refine G4c.orAll_intro (φ := (((itpE p S (f0 + 1) 0 Γ).ifThen
    (itpA p S (f0 + 1) 1 Γ (prop q))).somehow)) ?_ ?_
  · simp only [itpAoth, itpAgoal]
    exact List.mem_append.mpr (Or.inl (.head _))
  · refine box_remap_free htgt ?_ ?_
    · exact consume₁ (G4c.identity_mem (.head _))
        (fuelE_le p S (Nat.le_succ f0) 0 Γ)
    · exact G4c.identity_mem (.head _)

/-- **`GammaPairFloorA` at a boxed atom goal**: the *plain* γ first component fires
the ambient's other γ-conjunct (`grownAmb_of_plain`). -/
theorem gammaPairFloorA_boxedAtom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (F fl : Nat) (Γ : List PLLFormula) (A B : PLLFormula) (Δ : List PLLFormula)
    (hF : F + 1 ≤ fl)
    (hmem : A.somehow.ifThen B ∈ Γ) (hS : A.somehow.ifThen B ∈ S)
    (hBS : B ∈ S) (hB : B ∉ Γ) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hamb : G4c Δ (itpE p S (fl + 1) 2 Γ))
    (hval : G4c Δ (itpA p S (F + 1) 1 Γ A))
    (hsnd : G4c Δ (itpA p S (F + 1) 2 (B :: Γ) ((prop q).somehow))) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ ((prop q).somehow))) :=
  floorBox_of_grownAmb p S hOr hq hsome hF hBS hΓS
    (grownAmb_of_plain p S hmem hS hB hBS hamb
      (consume₁ hval (fuelA_le p S hF 1 Γ A))) hsnd

/-- **`JumpPairFloor` at a boxed atom goal**: the jump first component fires the
ambient's jump-conjunct (`tGrownAmb_jump_pres`). -/
theorem jumpPairFloor_boxedAtom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (F fl : Nat) (Γ : List PLLFormula) (A B D : PLLFormula)
    (Δ : List PLLFormula) (hF : F + 1 ≤ fl)
    (hmem : (A.ifThen B).ifThen D ∈ Γ) (hS : (A.ifThen B).ifThen D ∈ S)
    (hBD : B.ifThen D ∈ Γ) (hDS : D ∈ S) (hD : D ∉ Γ)
    (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hamb : G4c Δ (itpE p S (fl + 1) 2 Γ))
    (hfst : G4c Δ ((itpE p S (F + 1) 1 Γ).ifThen
      (itpA p S (F + 1) 1 Γ (A.ifThen B))))
    (hsnd : G4c Δ (itpA p S (F + 1) 2 (D :: Γ) ((prop q).somehow))) :
    G4c Δ (orAll (itpAoth p S fl 1 Γ ((prop q).somehow))) := by
  refine floorBox_of_grownAmb p S hOr hq hsome hF hDS hΓS ?_ hsnd
  refine tGrownAmb_jump_pres p S hmem hD hDS hBD hS hamb ?_
  refine G4c.impR ?_
  refine consume₁ (fire (hfst.weaken _) ?_) (fuelA_le p S hF 1 Γ (A.ifThen B))
  exact consume₁ (G4c.identity_mem (.head _)) (fuelE_le p S hF 1 Γ)

/-! ## 6. Every floor interface at an **unboxed** atom goal, outright

At `g = prop q` with `q ≠ p` the target's own goal clause is the atom itself at every
budget and every fuel, and `AtomForce.itpA_atom_forces` turns the branch's second
component into it.  Neither the ambient nor the first component is touched, so this
covers all three interfaces at once — and, unlike `AtomForce.floor_branch_atom`, at
**unrelated** source and target budgets, which is what the interfaces supply. -/

/-- **All three floor interfaces at an unboxed atom goal.**  Source and target
budgets independent. -/
theorem floorAny_atom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {F fl b₁ b₂ : Nat} {Γ Δ : List PLLFormula} {B : PLLFormula}
    (hBS : B ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hsnd : G4c Δ (itpA p S F b₁ (B :: Γ) (prop q))) :
    G4c Δ (orAll (itpAoth p S fl b₂ Γ (prop q))) := by
  have hBΓS : ∀ Y ∈ B :: Γ, Y ∈ S := by
    intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hBS
    · exact hΓS Y hY
  have hq' : G4c Δ (prop q) :=
    consume₁ hsnd (itpA_atom_forces p S hOr hq F b₁ (B :: Γ) hBΓS)
  refine G4c.orAll_intro (φ := prop q) ?_ hq'
  simp only [itpAoth, itpAgoal]
  refine List.mem_append.mpr (Or.inl ?_)
  rw [if_neg hq]
  exact .head _

end BoxSndTight
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.BoxSndTight.boxSnd_tight' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSndTight.boxSnd_tight

/--
info: 'PLLND.BoxSndTight.boxGoal_remap_free' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSndTight.boxGoal_remap_free

/--
info: 'PLLND.BoxSndTight.gammaPairFloorBox_boxedAtom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSndTight.gammaPairFloorBox_boxedAtom

/--
info: 'PLLND.BoxSndTight.gammaPairFloorA_boxedAtom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSndTight.gammaPairFloorA_boxedAtom

/--
info: 'PLLND.BoxSndTight.jumpPairFloor_boxedAtom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.BoxSndTight.jumpPairFloor_boxedAtom

/-- info: 'PLLND.BoxSndTight.floorAny_atom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.BoxSndTight.floorAny_atom
