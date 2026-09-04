import wip.goalDesc

/-!
# The universal table at an atom goal forces the atom

## Where this comes from

`wip/boxedBranchS1.lean` closes the descent's residual branch at one
configuration by case analysis on the second component
(`EnvDesc.branch_of_cases`), and every case closes the same way: the case's
*second conjunct* is a universal table at a **larger** context with the same
goal, and at the larger context that table collapses to the goal clause.  On the
two-γ-clause configuration all three cases go through for exactly that reason —
`wip/sealprobe6.lean` and the direct inspection behind PROGRESS §90 show the
cases are

    z ,      (u ∨ ⊥) ∧ (z ∨ ⊥) ,      ◯((s ∧ ⊤) ⊃ ⊥) ∧ (z ∨ ⊥)

and each contains `z ∨ ⊥`.

That is not an accident of the example.  Reading the environment clause table
(`itpAenv`, `LaxLogic/PLLG4UITrunc.lean`) at an **atom** goal `q ≠ p`, every
clause either produces nothing or produces a disjunct with a conjunct

    itpA p S f b Γ' (prop q)      with `Γ'` of strictly smaller defect,

with one exception: the `∨`-clause, whose disjunct is a *conjunction of
implications* and whose consequents cannot be extracted without their guards.
So over contexts with no `∨`-shaped member the whole table collapses, by
induction on the defect.

## The theorem

    itpA_atom_forces :
      (∀ A B, A.or B ∉ S) → q ≠ p → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q)

It holds at **every** fuel and **every** budget — the budget plays no role,
which is what makes it usable at the floor where the descent itself fails.

## What it is for

It is the engine of the case analysis at atom goals: in each case the second
conjunct is a table at a larger context, and this lemma turns it into the atom,
which is the target table's own goal clause.  So the residual branch closes at
atom goals over `∨`-free contexts, uniformly in the configuration — the first
general statement of that kind about the residue.
-/

open PLLFormula

namespace PLLND
namespace AtomForce

open GoalDesc

/-! ## 1. A defect witness -/

/-- If `Γ'` contains everything in `Γ` and also some `w ∈ S ∖ Γ`, its defect is
strictly smaller. -/
theorem defect_lt_of_witness {S : Finset PLLFormula} {Γ Γ' : List PLLFormula}
    (hsub : ∀ y ∈ Γ, y ∈ Γ') {w : PLLFormula}
    (hwS : w ∈ S) (hwΓ' : w ∈ Γ') (hwΓ : w ∉ Γ) :
    defect S Γ' < defect S Γ := by
  have hsubset : S \ Γ'.toFinset ⊆ S \ Γ.toFinset := by
    intro y hy
    simp only [Finset.mem_sdiff, List.mem_toFinset] at hy ⊢
    exact ⟨hy.1, fun h => hy.2 (hsub y h)⟩
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset hsubset]
  refine ⟨w, ?_, ?_⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset]
    exact ⟨hwS, hwΓ⟩
  · simp only [Finset.mem_sdiff, List.mem_toFinset, not_and, not_not]
    exact fun _ => hwΓ'

/-! ## 2. The theorem -/

/-- The recursion is on the defect; the statement is quantified over fuel,
budget and context so that the induction hypothesis applies at the grown
contexts the clauses produce. -/
theorem atom_forces_aux (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) (q : String) (hq : q ≠ p) :
    ∀ (d : Nat) (f b : Nat) (Γ : List PLLFormula),
      defect S Γ ≤ d → (∀ Y ∈ Γ, Y ∈ S) →
      G4c [itpA p S f b Γ (prop q)] (prop q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f b Γ hd hΓS
  cases f with
  | zero =>
      simp only [itpA]
      exact G4c.botL (.head _)
  | succ f' =>
      rw [itpA_succ]
      refine G4c.orAll_elim ?_
      intro φ hφ
      -- `prop q` is not `◯`-shaped, so the full table is goal ++ env
      simp only [itpAfull, itpAoth] at hφ
      rcases List.mem_append.mp hφ with hg | he
      · -- the goal clause: `[prop q]`
        simp only [itpAgoal] at hg
        rw [if_neg hq] at hg
        rcases List.mem_singleton.mp hg with rfl
        exact G4c.init (.head _)
      · -- an environment clause
        simp only [itpAenv] at he
        obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp he
        have hFS : F ∈ S := hΓS F hFΓ
        -- the recursive step, packaged: a table at a context that contains Γ
        -- and one fresh member of S
        have step : ∀ (Γ' : List PLLFormula) (w : PLLFormula),
            (∀ y ∈ Γ, y ∈ Γ') → (∀ y ∈ Γ', y ∈ S) →
            w ∈ S → w ∈ Γ' → w ∉ Γ →
            G4c [itpA p S f' b Γ' (prop q)] (prop q) := by
          intro Γ' w hsub hΓ'S hwS hwΓ' hwΓ
          have hlt : defect S Γ' < defect S Γ :=
            defect_lt_of_witness hsub hwS hwΓ' hwΓ
          exact ihd (defect S Γ') (by omega) f' b Γ' (Nat.le_refl _) hΓ'S
        cases F with
        | prop q' =>
            simp only at hin
            split at hin
            next hc =>
              -- needs `prop q = prop p`, impossible
              exfalso
              have h2 : q = p := by simpa using hc.2
              exact hq h2
            next => cases hin
        | falsePLL => cases hin
        | somehow χ => simp only at hin; cases hin
        | or A B => exact absurd hFS (hOr A B)
        | and A B =>
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                -- a fresh witness among A, B
                by_cases hA : A ∈ Γ
                · have hB : B ∉ Γ := fun hB => h1 ⟨hA, hB⟩
                  have hBS : B ∈ S := h2.2.resolve_left hB
                  exact step (A :: B :: Γ) B
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hΓS _ hA
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hBS
                      · exact hΓS y hy)
                    hBS (.tail _ (.head _)) hB
                · have hAS : A ∈ S := h2.1.resolve_left hA
                  exact step (A :: B :: Γ) A
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hAS
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact (h2.2.elim (fun h => hΓS _ h) id)
                      · exact hΓS y hy)
                    hAS (.head _) hA
              next => cases hin
        | ifThen A D =>
            cases A with
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
                      exact step (D :: Γ) D (fun y hy => .tail _ hy)
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact h2
                          · exact hΓS y hy)
                        h2 (.head _) h1
                    next h3 =>
                      split at hin
                      next => cases hin
                      next h4 =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                        exact step (D :: Γ) D (fun y hy => .tail _ hy)
                          (by
                            intro y hy
                            rcases List.mem_cons.mp hy with rfl | hy
                            · exact h2
                            · exact hΓS y hy)
                          h2 (.head _) h1
                  next => cases hin
            | falsePLL => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact step (A₁.ifThen (B₁.ifThen D) :: Γ)
                      (A₁.ifThen (B₁.ifThen D)) (fun y hy => .tail _ hy)
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact h2
                        · exact hΓS y hy)
                      h2 (.head _) h1
                  next => cases hin
            | or A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    by_cases hAD : A₁.ifThen D ∈ Γ
                    · have hBD : B₁.ifThen D ∉ Γ := fun h => h1 ⟨hAD, h⟩
                      have hBDS : B₁.ifThen D ∈ S := h2.2.resolve_left hBD
                      exact step (A₁.ifThen D :: B₁.ifThen D :: Γ)
                        (B₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hΓS _ hAD
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hBDS
                          · exact hΓS y hy)
                        hBDS (.tail _ (.head _)) hBD
                    · have hADS : A₁.ifThen D ∈ S := h2.1.resolve_left hAD
                      exact step (A₁.ifThen D :: B₁.ifThen D :: Γ)
                        (A₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hADS
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact (h2.2.elim (fun h => hΓS _ h) id)
                          · exact hΓS y hy)
                        hADS (.head _) hAD
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    repeat' split at hin
                    all_goals (try fin_cases hin)
                    all_goals refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                    all_goals exact step (D :: Γ) D (fun y hy => .tail _ hy) (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exacts [h2, hΓS y hy]) h2 (.head _) h1
                  next => cases hin
            | somehow A₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_append.mp hin with hL | hR
                    · -- the gated part (i): two disjuncts, both `_ ∧ A@b(D::Γ)`
                      repeat' split at hL
                      all_goals (try fin_cases hL)
                      all_goals refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                      all_goals exact step (D :: Γ) D (fun y hy => .tail _ hy) (by intro y hy; rcases List.mem_cons.mp hy with rfl | hy; exacts [h2, hΓS y hy]) h2 (.head _) h1
                    · -- part (ii): the per-`◯x` continuation, also `_ ∧ A@b(D::Γ)`
                      obtain ⟨X, hXΓ, hXin⟩ := List.mem_filterMap.mp hR
                      cases X with
                      | somehow x =>
                          simp only at hXin
                          split at hXin
                          next => cases hXin
                          next hx =>
                            rcases Option.some_inj.mp hXin with rfl
                            refine consume₁ (projAnd₂ (G4c.iden (.head _))) ?_
                            exact step (D :: Γ) D (fun y hy => .tail _ hy)
                              (by
                                intro y hy
                                rcases List.mem_cons.mp hy with rfl | hy
                                · exact h2
                                · exact hΓS y hy)
                              h2 (.head _) h1
                      | prop _ => cases hXin
                      | falsePLL => cases hXin
                      | and _ _ => cases hXin
                      | or _ _ => cases hXin
                      | ifThen _ _ => cases hXin
                  next => cases hin

/-- **The universal table at an atom goal forces the atom**, over a context
with no `∨`-shaped member, at every fuel and every budget. -/
theorem itpA_atom_forces (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    (f b : Nat) (Γ : List PLLFormula) (hΓS : ∀ Y ∈ Γ, Y ∈ S) :
    G4c [itpA p S f b Γ (prop q)] (prop q) :=
  atom_forces_aux p S hOr q hq (defect S Γ) f b Γ (Nat.le_refl _) hΓS

/-! ## 3. The floor branches at an atom goal

The three floor branches of the descent — the plain γ-pair, the boxed γ-pair
and the jump-pair (`GammaPairFloorA`, `GammaPairFloorBox`, `JumpPairFloor` of
`wip/cascadeBox.lean`) — all carry the *same* kind of second component: a
universal table at the grown context with the branch's own goal.  At an atom
goal §2 turns that into the atom, and the atom is the target table's own goal
clause.  So all three close at once, and neither the ambient nor the branch's
first component is needed at all. -/

/-- **The floor branch closes at an atom goal**, over a `∨`-free space: the
second component alone reaches the target table.  This covers all three floor
interfaces uniformly, since they differ only in their first component. -/
theorem floor_branch_atom (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {F fl b : Nat} {Γ Δ : List PLLFormula} {B : PLLFormula}
    (hBS : B ∈ S) (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hsnd : G4c Δ (itpA p S F b (B :: Γ) (prop q))) :
    G4c Δ (orAll (itpAoth p S fl b Γ (prop q))) := by
  have hBΓS : ∀ Y ∈ B :: Γ, Y ∈ S := by
    intro Y hY
    rcases List.mem_cons.mp hY with rfl | hY
    · exact hBS
    · exact hΓS Y hY
  have hq' : G4c Δ (prop q) :=
    consume₁ hsnd (itpA_atom_forces p S hOr hq F b (B :: Γ) hBΓS)
  refine G4c.orAll_intro (φ := prop q) ?_ hq'
  simp only [itpAoth, itpAgoal]
  refine List.mem_append.mpr (Or.inl ?_)
  rw [if_neg hq]
  exact .head _

/-- The same conclusion from the *full* table rather than the others-table, for
callers that have the truncation-carrying form. -/
theorem floor_branch_atom_full (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {F fl b : Nat} {Γ Δ : List PLLFormula} {B : PLLFormula}
    (hBS : B ∈ S) (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hsnd : G4c Δ (itpA p S F b (B :: Γ) (prop q))) :
    G4c Δ (itpA p S (fl + 1) b Γ (prop q)) := by
  rw [itpA_succ]
  refine consume₁ (floor_branch_atom p S hOr hq (fl := fl) hBS hΓS hsnd) ?_
  simp only [itpAfull]
  exact orAll_map (fun ψ h => ⟨ψ, h, G4c.iden (.head _)⟩)

/-! ## 4. The boxed goal clause remaps from a grown context

§3 closes the floor branches at an atom goal.  The remaining shape is the boxed
jump goal `◯a`, and PROGRESS §100 closes one on-path instance of it by a route whose
heart is this lemma.

The target's goal clause at `Γ` for the boxed goal `◯a` is

    ◯( E@c(Γ) ⇢ A@(c+1)(Γ, a) )

and the material available is the *same clause at a grown context* `Γ'` — because
that is what the source's second component supplies — together with the **grown
ambient** `E@(c+2)(Γ')`, which §7 of `wip/envDesc.lean` obtains from the ambient and
the branch's own first component.

`box_remap_free` reduces the remap to two conversions inside the box:

* the **guard**, `E@c(Γ') ` from the grown ambient by downward budget monotonicity —
  free;
* the **value**, `A@(c+1)(Γ', a) ⊢ A@(c+1)(Γ, a)`, which looks like context
  *shrinking* and would be unsound in general.  At an **atom** goal it is not:
  §2 turns the left side into `a` itself, and `a` is the goal clause of the right
  side at *every* context.

So the one step that would have needed shrinking is exactly the step §2 licenses. -/

/-- **The boxed goal clause remaps from a grown context**, at an atom goal, over a
`∨`-free space, given the grown ambient. -/
theorem boxGoal_remap (p : String) (S : Finset PLLFormula)
    (hOr : ∀ A B : PLLFormula, A.or B ∉ S) {q : String} (hq : q ≠ p)
    {f c : Nat} {Γ Γ' Δ : List PLLFormula}
    (hΓ'S : ∀ Y ∈ Γ', Y ∈ S)
    (hgrown : G4c Δ (itpE p S f (c + 2) Γ'))
    (hbox : G4c Δ (((itpE p S f c Γ').ifThen
      (itpA p S f (c + 1) Γ' (prop q))).somehow)) :
    G4c Δ (((itpE p S f c Γ).ifThen
      (itpA p S (f + 1) (c + 1) Γ (prop q))).somehow) := by
  refine box_remap_free hbox ?_ ?_
  · -- the guard: the grown ambient is two budgets up
    exact ambE p S (Nat.le_refl _) (by omega) rfl (hgrown.weaken _)
  · -- the value: §2 turns the grown table into the atom, which is the goal
    -- clause of the target table at Γ
    have hatom : G4c (itpA p S f (c + 1) Γ' (prop q) ::
        itpE p S f c Γ :: Δ) (prop q) :=
      consume₁ (G4c.identity_mem (.head _))
        (itpA_atom_forces p S hOr hq f (c + 1) Γ' hΓ'S)
    rw [itpA_succ]
    refine G4c.orAll_intro (φ := prop q) ?_ hatom
    simp only [itpAfull, itpAoth, itpAgoal]
    refine List.mem_append.mpr (Or.inl ?_)
    rw [if_neg hq]
    exact .head _

end AtomForce
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.AtomForce.itpA_atom_forces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.itpA_atom_forces

/--
info: 'PLLND.AtomForce.defect_lt_of_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.defect_lt_of_witness

/--
info: 'PLLND.AtomForce.floor_branch_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.floor_branch_atom

/--
info: 'PLLND.AtomForce.boxGoal_remap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.AtomForce.boxGoal_remap
