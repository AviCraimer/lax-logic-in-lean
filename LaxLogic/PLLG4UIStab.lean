import LaxLogic.PLLG4UIAdq

/-!
# UI phase 4b: set-congruence of the quantifiers

`interE p fuel Γ` and `interA p fuel Γ C` respect context-set equality
up to provable equivalence: the clause lists for set-equal contexts
have pointwise inter-derivable members (same principals, transported
guards, congruent subcontexts).  One direction suffices — the
statement is ∀-quantified over both lists, so the symmetric instance
supplies contravariant positions.

This is the lemma that lets stabilization treat the finitely many
context-*sets* as the true state space: a same-set clause collapses
onto its own state instead of burning fuel.
-/

open PLLFormula

set_option maxHeartbeats 4000000

namespace PLLND

/-- Project a conjunct out of a bundled `andAll` (list calculus). -/
theorem andAll_project_c {l : List PLLFormula} {φ : PLLFormula}
    (hmem : φ ∈ l) : G4c [andAll l] φ :=
  G4c.andAll_elim hmem (G4c.iden (.head _))

/-- **Set-congruence** of the quantifiers, one direction. -/
theorem inter_congr (p : String) : ∀ (fuel : Nat),
    (∀ Γ₁ Γ₂, Γ₁.toFinset = Γ₂.toFinset →
      G4c [interE p fuel Γ₁] (interE p fuel Γ₂)) ∧
    (∀ Γ₁ Γ₂ C, Γ₁.toFinset = Γ₂.toFinset →
      G4c [interA p fuel Γ₁ C] (interA p fuel Γ₂ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ₁ Γ₂ _
        simp only [interE]
        exact G4c.truePLL_intro _
      · intro Γ₁ Γ₂ C _
        simp only [interA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- E-side
        intro Γ₁ Γ₂ hset
        have hg : ∀ (G : PLLFormula), G ∈ Γ₁ ↔ G ∈ Γ₂ := by
          intro G
          simp only [← List.mem_toFinset]
          rw [hset]
        have hset1 : ∀ (X : PLLFormula),
            (X :: Γ₁).toFinset = (X :: Γ₂).toFinset := by
          intro X
          rw [List.toFinset_cons, List.toFinset_cons, hset]
        have hset2 : ∀ (X Y : PLLFormula),
            (X :: Y :: Γ₁).toFinset = (X :: Y :: Γ₂).toFinset := by
          intro X Y
          simp only [List.toFinset_cons, hset]
        simp only [interE]
        refine G4c.andAll_intro ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- ⊥ clause
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.andAll_elim ?_ (G4c.botL (.head _))
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos ((hg _).mpr hbot)]
                            exact .head _))))
            next => cases hφ
          · -- atom clauses
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine G4c.andAll_elim ?_ (G4c.init (.head _))
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr
                      ⟨prop q, (hg _).mpr hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          have hF₁ : F ∈ Γ₁ := (hg _).mpr hFΓ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.andAll_elim ?_
                (ihE (A :: B :: Γ₁) (A :: B :: Γ₂) (hset2 A B))
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.and B, hF₁, .head _⟩))
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.andAll_elim ?_
                (or_mono (ihE (A :: Γ₁) (A :: Γ₂) (hset1 A))
                  (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.or B, hF₁, .head _⟩))
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.andAll_elim ?_
                (box_mono (ihE (χ :: Γ₁) (χ :: Γ₂) (hset1 χ)))
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨χ.somehow, hF₁, .head _⟩))
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hq₂ =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4c.andAll_elim ?_
                      (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B))
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop q).ifThen B, hF₁, ?_⟩))
                    simp only
                    rw [if_pos ((hg _).mpr hq₂)]
                    exact .head _
                  next hq₂ =>
                    split at hin
                    next => cases hin
                    next hqp =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4c.andAll_elim ?_
                        (imp_mono (G4c.iden (.head _))
                          (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(prop q).ifThen B, hF₁, ?_⟩))
                      simp only
                      rw [if_neg (fun hc => hq₂ ((hg _).mp hc)), if_neg hqp]
                      exact .head _
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.andAll_elim ?_
                    (ihE (A₁.ifThen (B₁.ifThen B) :: Γ₁)
                      (A₁.ifThen (B₁.ifThen B) :: Γ₂) (hset1 _))
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.and B₁).ifThen B, hF₁, .head _⟩))
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.andAll_elim ?_
                    (ihE (A₁.ifThen B :: B₁.ifThen B :: Γ₁)
                      (A₁.ifThen B :: B₁.ifThen B :: Γ₂) (hset2 _ _))
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.or B₁).ifThen B, hF₁, .head _⟩))
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.andAll_elim ?_
                    (imp_mono
                      (imp_mono
                        (ihE (B₁.ifThen B :: Γ₁) (B₁.ifThen B :: Γ₂)
                          (hset1 _))
                        (ihA (B₁.ifThen B :: Γ₂) (B₁.ifThen B :: Γ₁)
                          (A₁.ifThen B₁) (hset1 _).symm))
                      (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.ifThen B₁).ifThen B, hF₁, .head _⟩))
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · refine G4c.andAll_elim ?_
                      (imp_mono (ihA Γ₂ Γ₁ A₁ hset.symm)
                        (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
                    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A₁.somehow.ifThen B, hF₁, .head _⟩))
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · refine G4c.andAll_elim ?_
                        (imp_mono
                          (box_mono (imp_mono (ihE Γ₁ Γ₂ hset)
                            (ihA Γ₂ Γ₁ A₁.somehow hset.symm)))
                          (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
                      exact List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨A₁.somehow.ifThen B, hF₁,
                          List.mem_cons.mpr (Or.inr (.head _))⟩))
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          refine G4c.andAll_elim ?_
                            (imp_mono
                              (box_mono
                                (imp_mono
                                  (ihE (x :: Γ₁) (x :: Γ₂) (hset1 x))
                                  (ihA (x :: Γ₂) (x :: Γ₁) A₁.somehow
                                    (hset1 x).symm)))
                              (ihE (B :: Γ₁) (B :: Γ₂) (hset1 B)))
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hF₁, ?_⟩))
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inr
                              (List.mem_filterMap.mpr
                                ⟨x.somehow, (hg _).mpr hXΓ, rfl⟩))))
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
      · -- A-side
        intro Γ₁ Γ₂ C hset
        have hg : ∀ (G : PLLFormula), G ∈ Γ₁ ↔ G ∈ Γ₂ := by
          intro G
          simp only [← List.mem_toFinset]
          rw [hset]
        have hset1 : ∀ (X : PLLFormula),
            (X :: Γ₁).toFinset = (X :: Γ₂).toFinset := by
          intro X
          rw [List.toFinset_cons, List.toFinset_cons, hset]
        have hset2 : ∀ (X Y : PLLFormula),
            (X :: Y :: Γ₁).toFinset = (X :: Y :: Γ₂).toFinset := by
          intro X Y
          simp only [List.toFinset_cons, hset]
        simp only [interA]
        refine G4c.orAll_elim ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · -- goal clauses (over Γ₁'s list)
          cases C with
          | prop q =>
              simp only at hφ
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine G4c.orAll_intro ?_ (G4c.iden (.head _))
                refine List.mem_append.mpr (Or.inl ?_)
                simp only
                rw [if_neg hq]
                exact .head _
          | falsePLL => cases hφ
          | and C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.orAll_intro
                (List.mem_append.mpr (Or.inl (.head _))) ?_
              exact and_mono (ihA Γ₁ Γ₂ C₁ hset) (ihA Γ₁ Γ₂ C₂ hset)
          | or C₁ C₂ =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine G4c.orAll_intro
                  (List.mem_append.mpr (Or.inl (.head _))) ?_
                exact ihA Γ₁ Γ₂ C₁ hset
              · rcases List.mem_singleton.mp hφ' with rfl
                refine G4c.orAll_intro
                  (List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
                exact ihA Γ₁ Γ₂ C₂ hset
          | ifThen C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.orAll_intro
                (List.mem_append.mpr (Or.inl (.head _))) ?_
              exact imp_mono
                (ihE (C₁ :: Γ₂) (C₁ :: Γ₁) (hset1 C₁).symm)
                (ihA (C₁ :: Γ₁) (C₁ :: Γ₂) C₂ (hset1 C₁))
          | somehow D =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine G4c.orAll_intro
                  (List.mem_append.mpr (Or.inl (.head _))) ?_
                exact box_mono (imp_mono (ihE Γ₂ Γ₁ hset.symm)
                  (ihA Γ₁ Γ₂ D hset))
              · rcases List.mem_singleton.mp hφ' with rfl
                refine G4c.orAll_intro
                  (List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
                exact box_mono (imp_mono (ihE Γ₂ Γ₁ hset.symm)
                  (ihA Γ₁ Γ₂ D.somehow hset))
        · -- context clauses (over Γ₁'s list)
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          have hF₂ : F ∈ Γ₂ := (hg _).mp hFΓ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hgd =>
                rcases List.mem_singleton.mp hin with rfl
                refine G4c.orAll_intro ?_ (G4c.iden (.head _))
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨prop q, hF₂, ?_⟩))
                simp only
                rw [if_pos hgd]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.and B, hF₂, .head _⟩))) ?_
              exact ihA (A :: B :: Γ₁) (A :: B :: Γ₂) C (hset2 A B)
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.or B, hF₂, .head _⟩))) ?_
              exact and_mono
                (imp_mono (ihE (A :: Γ₂) (A :: Γ₁) (hset1 A).symm)
                  (ihA (A :: Γ₁) (A :: Γ₂) C (hset1 A)))
                (imp_mono (ihE (B :: Γ₂) (B :: Γ₁) (hset1 B).symm)
                  (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B)))
          | somehow χ =>
              simp only at hin
              split at hin
              · rcases List.mem_singleton.mp hin with rfl
                refine G4c.orAll_intro ?_
                  (box_mono
                    (imp_mono (ihE (χ :: Γ₂) (χ :: Γ₁) (hset1 χ).symm)
                      (ihA (χ :: Γ₁) (χ :: Γ₂) _ (hset1 χ))))
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hF₂, ?_⟩))
                simp only
                exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hq₁ =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4c.orAll_intro ?_
                      (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B))
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop q).ifThen B, hF₂, ?_⟩))
                    simp only
                    rw [if_pos ((hg _).mp hq₁)]
                    exact .head _
                  next hq₁ =>
                    split at hin
                    next => cases hin
                    next hqp =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4c.orAll_intro ?_
                        (and_mono (G4c.iden (.head _))
                          (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B)))
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hF₂, ?_⟩))
                      simp only
                      rw [if_neg (fun hc => hq₁ ((hg _).mpr hc)), if_neg hqp]
                      exact .head _
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro
                    (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(A₁.and B₁).ifThen B, hF₂, .head _⟩))) ?_
                  exact ihA (A₁.ifThen (B₁.ifThen B) :: Γ₁)
                    (A₁.ifThen (B₁.ifThen B) :: Γ₂) C (hset1 _)
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro
                    (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(A₁.or B₁).ifThen B, hF₂, .head _⟩))) ?_
                  exact ihA (A₁.ifThen B :: B₁.ifThen B :: Γ₁)
                    (A₁.ifThen B :: B₁.ifThen B :: Γ₂) C (hset2 _ _)
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro
                    (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(A₁.ifThen B₁).ifThen B, hF₂, .head _⟩))) ?_
                  exact and_mono
                    (imp_mono
                      (ihE (B₁.ifThen B :: Γ₂) (B₁.ifThen B :: Γ₁)
                        (hset1 _).symm)
                      (ihA (B₁.ifThen B :: Γ₁) (B₁.ifThen B :: Γ₂)
                        (A₁.ifThen B₁) (hset1 _)))
                    (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B))
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · refine G4c.orAll_intro
                      (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨A₁.somehow.ifThen B, hF₂, .head _⟩))) ?_
                    exact and_mono (ihA Γ₁ Γ₂ A₁ hset)
                      (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B))
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · refine G4c.orAll_intro
                        (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                          ⟨A₁.somehow.ifThen B, hF₂,
                            List.mem_cons.mpr (Or.inr (.head _))⟩))) ?_
                      exact and_mono
                        (box_mono (imp_mono (ihE Γ₂ Γ₁ hset.symm)
                          (ihA Γ₁ Γ₂ A₁.somehow hset)))
                        (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B))
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          refine G4c.orAll_intro ?_
                            (and_mono
                              (box_mono
                                (imp_mono
                                  (ihE (x :: Γ₂) (x :: Γ₁) (hset1 x).symm)
                                  (ihA (x :: Γ₁) (x :: Γ₂) A₁.somehow
                                    (hset1 x))))
                              (ihA (B :: Γ₁) (B :: Γ₂) C (hset1 B)))
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hF₂, ?_⟩))
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inr
                              (List.mem_filterMap.mpr
                                ⟨x.somehow, (hg _).mp hXΓ, rfl⟩))))
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq

/-! ### The lax fixpoint lemma

The PLL analogue of Bílková's Lemma 2.18 for GL: a ◯-guarded
self-referential disjunct is provably redundant after one unfolding —
`◯((α ∨ ◯δ) ∧ β) ⊣⊢ ◯(α ∧ β)` for `δ := α ∧ β`.  Where GL needs the
4-axiom (and Löb elsewhere), PLL needs only the monad: the collapsing
step is `◯(◯δ ∧ β) ⊢ ◯δ` — strength to pair `β` into the box and
multiplication to flatten.  This is the engine for truncating the
self-referential ◯-goal disjunct in the uniformity layer. -/

theorem lax_fixpoint (α β : PLLFormula) :
    (G4c [((α.or (α.and β).somehow).and β).somehow]
      ((α.and β).somehow)) ∧
    (G4c [(α.and β).somehow]
      (((α.or (α.and β).somehow).and β).somehow)) := by
  constructor
  · -- collapse: distribute, then multiply
    refine G4c.laxL (.head _) ?_
    refine G4c.andL (List.Perm.refl _) ?_
    refine G4c.orL (List.Perm.refl _) ?_ ?_
    · -- the α-branch: unit
      exact G4c.laxR (G4c.andR (G4c.iden (.head _))
        (G4c.iden (.tail _ (.head _))))
    · -- the ◯δ-branch: open the inner box (multiplication)
      refine G4c.laxL (.head _) ?_
      refine G4c.andL (List.Perm.refl _) ?_
      exact G4c.laxR (G4c.andR (G4c.iden (.head _))
        (G4c.iden (.tail _ (.head _))))
  · -- expansion: unit into the left disjunct
    refine G4c.laxL (.head _) ?_
    refine G4c.andL (List.Perm.refl _) ?_
    exact G4c.laxR (G4c.andR (G4c.orR1 (G4c.iden (.head _)))
      (G4c.iden (.tail _ (.head _))))

end PLLND
