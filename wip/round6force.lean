import wip.boxSndTight

/-!
# ROUND 6 — ambient-carrying atom forcing over `∨`-spaces
# (PROGRESS §61(f)(ii), the second named residue of the truncation-tower)

`AtomForce.itpA_atom_forces` — the engine that makes the `◯`-goal descent's
atomic case budget-free (`boxDesc_atom_all`, `gammaHead_budget_free`,
`boxSnd_tight`'s goal-clause landing) — assumes a `∨`-FREE space: the or-row
of the universal table is a conjunction of guarded implications, and without
an ambient there is nothing to fire the guards with.

§61(f)(ii) named the lift: *the or-rows should split against the ambient's
or-conjunct, defect-recursively*.  This file proves it.

    itpA_atom_forces_amb :
      q ≠ p → (∀ Y ∈ Γ, Y ∈ S) →
      Δ ⊢ E@(f, e+2)(Γ) → Δ ⊢ A@(f, e+2)(Γ, q) → Δ ⊢ q

**No `∨`-freeness hypothesis.**  The ambient and the source sit at MATCHED
fuel and budget — exactly the configuration `boxSnd_tight`'s traversal holds
at every step, so the lifted lemma is consumable wherever the `∨`-free one
was, provided the caller carries the ambient (which every consumer in the
`boxSnd` tier does).

The proof is the defect recursion of `AtomForce.atom_forces_aux` with the
ambient threaded through every context growth:

* the growth rows that used to recurse bare now fire the ambient's matching
  conjunct first (`grown_*` / `tGrownAmb_*`, the `boxSnd`/`boxSndTight`
  apparatus, all at the matched budgets where the conjunct's antecedent is
  exactly what the source disjunct carries);
* the or-row — the case that used to be excluded — cuts in the ambient's
  or-conjunct `E(A::Γ) ∨ E(B::Γ)` and splits: in each branch the branch's
  own grown ambient fires the source disjunct's matching component, and the
  defect recursion continues at the grown context.

**What this does and does not do for the tower.**  It removes the `∨`-free
scope restriction from the atomic landings (`boxSnd_tight`'s goal-clause case
consumes `itpA_atom_forces` at the grown context WITH the grown ambient in
hand, so the same replacement goes through there).  It does NOT touch the
financing residue of `wip/round6core.lean` §4 — the two are independent
gates, and this one is now open.
-/

open PLLFormula

namespace PLLND
namespace Round6Force

open GoalDesc AtomForce EnvDesc BoxSnd BoxSndTight

set_option maxHeartbeats 2000000 in
/-- The defect recursion.  `d` bounds the defect; fuel and budgets are
quantified inside so the induction hypothesis applies at every grown
context. -/
theorem atom_forces_amb_aux (p : String) (S : Finset PLLFormula)
    {q : String} (hq : q ≠ p) :
    ∀ (d : Nat) (f e : Nat) (Γ' Δ : List PLLFormula),
      defect S Γ' ≤ d → (∀ Y ∈ Γ', Y ∈ S) →
      G4c Δ (itpE p S f (e + 2) Γ') →
      G4c Δ (itpA p S f (e + 2) Γ' (prop q)) →
      G4c Δ (prop q) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro f e Γ' Δ hd hΓ'S hamb hsrc
  cases f with
  | zero =>
      simp only [itpA] at hsrc
      exact G4c.cut hsrc (G4c.botL (.head _))
  | succ f' =>
      rw [itpA_succ] at hsrc
      refine G4c.cut hsrc (G4c.orAll_elim ?_)
      intro φ hφ
      have hA : G4c (φ :: Δ) (itpE p S (f' + 1) (e + 2) Γ') := hamb.weaken φ
      have hφd : G4c (φ :: Δ) φ := G4c.identity_mem (.head _)
      -- the recursive step, packaged: matched-budget pair at a context that
      -- contains Γ' and one fresh member of S
      have step : ∀ (Δ₀ : List PLLFormula) (Γ'' : List PLLFormula)
          (w : PLLFormula),
          (∀ y ∈ Γ', y ∈ Γ'') → (∀ y ∈ Γ'', y ∈ S) →
          w ∈ S → w ∈ Γ'' → w ∉ Γ' →
          G4c Δ₀ (itpE p S f' (e + 2) Γ'') →
          G4c Δ₀ (itpA p S f' (e + 2) Γ'' (prop q)) →
          G4c Δ₀ (prop q) := by
        intro Δ₀ Γ'' w hsub hΓ''S hwS hwΓ'' hwΓ' hg'' hs''
        exact ihd (defect S Γ'')
          (by
            have := defect_lt_of_witness hsub hwS hwΓ'' hwΓ'
            omega)
          f' e Γ'' Δ₀ (Nat.le_refl _) hΓ''S hg'' hs''
      simp only [itpAfull, itpAoth] at hφ
      rcases List.mem_append.mp hφ with hg | he
      · -- the goal clause: `[prop q]`
        simp only [itpAgoal] at hg
        rw [if_neg hq] at hg
        rcases List.mem_singleton.mp hg with rfl
        exact hφd
      · -- an environment clause
        simp only [itpAenv] at he
        obtain ⟨F, hFΓ', hin⟩ := List.mem_flatMap.mp he
        have hFS : F ∈ S := hΓ'S F hFΓ'
        cases F with
        | prop q' =>
            simp only at hin
            split at hin
            next hc =>
              exfalso
              have h2 : q = p := by simpa using hc.2
              exact hq h2
            next => cases hin
        | falsePLL => cases hin
        | somehow χ => simp only at hin; cases hin
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
                  exact step _ (A :: B :: Γ') B
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hΓ'S _ hAin
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hBS
                      · exact hΓ'S y hy)
                    hBS (.tail _ (.head _)) hB
                    (grown_and p S hFΓ' h1 h2 hA) hφd
                · have hAS : A ∈ S := h2.1.resolve_left hAin
                  exact step _ (A :: B :: Γ') A
                    (fun y hy => .tail _ (.tail _ hy))
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact hAS
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                      · exact hΓ'S y hy)
                    hAS (.head _) hAin
                    (grown_and p S hFΓ' h1 h2 hA) hφd
              next => cases hin
        | or A B =>
            -- THE LIFTED CASE: split against the ambient's or-conjunct
            simp only at hin
            split at hin
            next => cases hin
            next h1 =>
              split at hin
              next h2 =>
                rcases List.mem_singleton.mp hin with rfl
                have hAΓ : A ∉ Γ' := fun h => h1 (Or.inl h)
                have hBΓ : B ∉ Γ' := fun h => h1 (Or.inr h)
                -- the ambient's or-conjunct
                have hOrConj : G4c
                    ((((itpE p S f' (e + 2) (A :: Γ')).ifThen
                        (itpA p S f' (e + 2) (A :: Γ') (prop q))).and
                      ((itpE p S f' (e + 2) (B :: Γ')).ifThen
                        (itpA p S f' (e + 2) (B :: Γ') (prop q)))) :: Δ)
                    ((itpE p S f' (e + 2) (A :: Γ')).or
                      (itpE p S f' (e + 2) (B :: Γ'))) := by
                  rw [itpE_succ] at hA
                  refine projAll hA ?_
                  unfold itpEcls
                  refine List.mem_append.mpr (Or.inr ?_)
                  refine List.mem_flatMap.mpr ⟨A.or B, hFΓ', ?_⟩
                  simp only [if_neg h1, if_pos h2]
                  exact List.mem_singleton.mpr rfl
                refine G4c.cut hOrConj (G4c.orL (List.Perm.refl _) ?_ ?_)
                · -- left branch: the grown ambient at A :: Γ' is in context
                  refine step _ (A :: Γ') A (fun y hy => .tail _ hy)
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact h2.1
                      · exact hΓ'S y hy)
                    h2.1 (.head _) hAΓ
                    (G4c.identity_mem (.head _)) ?_
                  exact fire
                    (consume₁ ((hφd.weaken _))
                      (projAnd₁ (G4c.iden (.head _))))
                    (G4c.identity_mem (.head _))
                · -- right branch
                  refine step _ (B :: Γ') B (fun y hy => .tail _ hy)
                    (by
                      intro y hy
                      rcases List.mem_cons.mp hy with rfl | hy
                      · exact h2.2
                      · exact hΓ'S y hy)
                    h2.2 (.head _) hBΓ
                    (G4c.identity_mem (.head _)) ?_
                  exact fire
                    (consume₁ ((hφd.weaken _))
                      (projAnd₂ (G4c.iden (.head _))))
                    (G4c.identity_mem (.head _))
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
                      exact step _ (D :: Γ') D
                        (fun y hy => .tail _ hy)
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact h2
                          · exact hΓ'S y hy)
                        h2 (.head _) h1
                        (grown_impAtom_pres p S hFΓ' h1 h2 h3 hA) hφd
                    next h3 =>
                      split at hin
                      next => cases hin
                      next h4 =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine step _ (D :: Γ') D
                          (fun y hy => .tail _ hy)
                          (by
                            intro y hy
                            rcases List.mem_cons.mp hy with rfl | hy
                            · exact h2
                            · exact hΓ'S y hy)
                          h2 (.head _) h1
                          (grown_impAtom_fresh p S hFΓ' h1 h2 h3 h4 hA
                            (projAnd₁ hφd)) (projAnd₂ hφd)
                  next => cases hin
            | and A₁ B₁ =>
                simp only at hin
                split at hin
                next => cases hin
                next h1 =>
                  split at hin
                  next h2 =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact step _ (A₁.ifThen (B₁.ifThen D) :: Γ')
                      (A₁.ifThen (B₁.ifThen D)) (fun y hy => .tail _ hy)
                      (by
                        intro y hy
                        rcases List.mem_cons.mp hy with rfl | hy
                        · exact h2
                        · exact hΓ'S y hy)
                      h2 (.head _) h1
                      (grown_impAnd p S hFΓ' h1 h2 hA) hφd
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
                      exact step _
                        (A₁.ifThen D :: B₁.ifThen D :: Γ')
                        (B₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hΓ'S _ hAD
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hBDS
                          · exact hΓ'S y hy)
                        hBDS (.tail _ (.head _)) hBD
                        (grown_impOr p S hFΓ' h1 h2 hA) hφd
                    · have hADS : A₁.ifThen D ∈ S := h2.1.resolve_left hAD
                      exact step _
                        (A₁.ifThen D :: B₁.ifThen D :: Γ')
                        (A₁.ifThen D) (fun y hy => .tail _ (.tail _ hy))
                        (by
                          intro y hy
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact hADS
                          rcases List.mem_cons.mp hy with rfl | hy
                          · exact (h2.2.elim (fun h => hΓ'S _ h) id)
                          · exact hΓ'S y hy)
                        hADS (.head _) hAD
                        (grown_impOr p S hFΓ' h1 h2 hA) hφd
                  next => cases hin
            | ifThen A₁ B₁ =>
                simp only at hin
                by_cases h1 : D ∈ Γ'
                · simp only [if_pos h1] at hin; cases hin
                simp only [if_neg h1] at hin
                by_cases h2 : D ∈ S
                case neg => simp only [if_neg h2] at hin; cases hin
                simp only [if_pos h2] at hin
                have hgrow : ∀ y ∈ D :: Γ', y ∈ S := by
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact h2
                  · exact hΓ'S y hy
                by_cases h3 : B₁.ifThen D ∈ Γ'
                · simp only [if_pos h3, if_pos hFS] at hin
                  rcases List.mem_singleton.mp hin with rfl
                  exact step _ (D :: Γ') D (fun y hy => .tail _ hy)
                    hgrow h2 (.head _) h1
                    (tGrownAmb_jump_pres p S hFΓ' h1 h2 h3 hFS hA
                      (projAnd₁ hφd)) (projAnd₂ hφd)
                · simp only [if_neg h3] at hin
                  by_cases h4 : B₁.ifThen D ∈ S
                  · simp only [if_pos h4] at hin
                    rcases List.mem_singleton.mp hin with rfl
                    exact step _ (D :: Γ') D (fun y hy => .tail _ hy)
                      hgrow h2 (.head _) h1
                      (tGrownAmb_jump_fresh p S hFΓ' h1 h2 h3 h4 hA
                        (projAnd₁ hφd)) (projAnd₂ hφd)
                  · simp only [if_neg h4] at hin; cases hin
            | somehow A₁ =>
                simp only at hin
                by_cases h1 : D ∈ Γ'
                · simp only [if_pos h1] at hin; cases hin
                simp only [if_neg h1] at hin
                by_cases h2 : D ∈ S
                case neg => simp only [if_neg h2] at hin; cases hin
                simp only [if_pos h2] at hin
                have hgrow : ∀ y ∈ D :: Γ', y ∈ S := by
                  intro y hy
                  rcases List.mem_cons.mp hy with rfl | hy
                  · exact h2
                  · exact hΓ'S y hy
                rcases List.mem_append.mp hin with hL | hR
                · -- the gated part: plain and boxed γ-conjuncts
                  by_cases hAS : A₁.somehow.ifThen D ∈ S
                  · simp only [if_pos hAS] at hL
                    rcases List.mem_cons.mp hL with rfl | hL'
                    · exact step _ (D :: Γ') D
                        (fun y hy => .tail _ hy) hgrow h2 (.head _) h1
                        (grownAmb_of_plain p S hFΓ' hAS h1 h2 hA
                          (projAnd₁ hφd)) (projAnd₂ hφd)
                    · rcases List.mem_singleton.mp hL' with rfl
                      exact step _ (D :: Γ') D
                        (fun y hy => .tail _ hy) hgrow h2 (.head _) h1
                        (grownAmb_of_box p S hFΓ' hAS h1 h2 hA
                          (projAnd₁ hφd)) (projAnd₂ hφd)
                  · simp only [if_neg hAS] at hL
                    cases hL
                · -- the per-`◯x` γ-context continuation
                  obtain ⟨X, hXΓ', hXin⟩ := List.mem_filterMap.mp hR
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
                        exact step _ (D :: Γ') D
                          (fun y hy => .tail _ hy) hgrow h2 (.head _) h1
                          (tGrownAmb_gammaCont p S hFΓ' h1 h2 hXΓ' hx hA
                            (projAnd₁ hφd)) (projAnd₂ hφd)

/-- **The universal table at an atom goal forces the atom, over ANY space,
given the ambient at matched fuel and budget.**  The `∨`-freeness hypothesis
of `AtomForce.itpA_atom_forces` is gone; the or-rows split against the
ambient's or-conjunct, defect-recursively (PROGRESS §61(f)(ii)). -/
theorem itpA_atom_forces_amb (p : String) (S : Finset PLLFormula)
    {q : String} (hq : q ≠ p) (f e : Nat) (Γ Δ : List PLLFormula)
    (hΓS : ∀ Y ∈ Γ, Y ∈ S)
    (hamb : G4c Δ (itpE p S f (e + 2) Γ))
    (hsrc : G4c Δ (itpA p S f (e + 2) Γ (prop q))) :
    G4c Δ (prop q) :=
  atom_forces_amb_aux p S hq (defect S Γ) f e Γ Δ (Nat.le_refl _) hΓS
    hamb hsrc

end Round6Force
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round6Force.itpA_atom_forces_amb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6Force.itpA_atom_forces_amb

/-! **The statement carries no `∨`-freeness and no financing.**  Pinned as a
type check. -/

/--
info: PLLND.Round6Force.itpA_atom_forces_amb (p : String) (S : Finset PLLFormula) {q : String} (hq : q ≠ p) (f e : ℕ)
  (Γ Δ : List PLLFormula) (hΓS : ∀ Y ∈ Γ, Y ∈ S) (hamb : PLLND.G4c Δ (PLLND.itpE p S f (e + 2) Γ))
  (hsrc : PLLND.G4c Δ (PLLND.itpA p S f (e + 2) Γ (prop q))) : PLLND.G4c Δ (prop q)
-/
#guard_msgs in
#check PLLND.Round6Force.itpA_atom_forces_amb
