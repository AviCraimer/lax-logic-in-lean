import LaxLogic.PLLG4UI

/-!
# UI phase 4a: adequacy of the Pitts quantifiers (E2/A2), height-fueled

The Pitts/iSL adequacy pair over the v2 quantifiers: for a derivation
of `Γ ∪ Δ ⊢ C` of height `n` with `Δ` p-free and any `fuel > n`,

* (E) if `C` is p-free then `interE p fuel Γ, Δ ⊢ C`;
* (A) `interE p fuel Γ, Δ ⊢ interA p fuel Γ (C)`

— both components simultaneously, by strong induction on `n`.  The
entire fuel bookkeeping collapses to `n < fuel`: every clause-descent
is paid by the height descent, same-set premises and Δ-side commutes
never burn, and `E_step` (cut through fuel monotonicity) bridges the
one-level descent of the `interE`-hypothesis.  No space hypotheses are
needed at this layer; the Γ-only-fuel (uniformity) refinement is a
separate stabilization lemma on top.
-/

open PLLFormula

set_option maxHeartbeats 12000000

namespace PLLND

private theorem pfree_insert {p : String} {ψ : PLLFormula}
    {Δ : Finset PLLFormula} (hψ : p ∉ ψ.atoms)
    (hΔ : ∀ χ ∈ Δ, p ∉ χ.atoms) :
    ∀ χ ∈ insert ψ Δ, p ∉ χ.atoms := by
  intro χ hχ
  rcases Finset.mem_insert.mp hχ with rfl | hχ
  · exact hψ
  · exact hΔ χ hχ

private theorem ctx_cons {X : PLLFormula} {Γ : List PLLFormula}
    {Δ : Finset PLLFormula} :
    insert X (Γ.toFinset ∪ Δ) = (X :: Γ).toFinset ∪ Δ := by
  rw [List.toFinset_cons, Finset.insert_union]

private theorem ctx_cons₂ {X Y : PLLFormula} {Γ : List PLLFormula}
    {Δ : Finset PLLFormula} :
    insert X (insert Y (Γ.toFinset ∪ Δ)) = (X :: Y :: Γ).toFinset ∪ Δ := by
  rw [List.toFinset_cons, List.toFinset_cons, Finset.insert_union,
    Finset.insert_union]

private theorem ctx_delta {X : PLLFormula} {Γ : List PLLFormula}
    {Δ : Finset PLLFormula} :
    insert X (Γ.toFinset ∪ Δ) = Γ.toFinset ∪ insert X Δ :=
  (Finset.union_insert _ _ _).symm

/-- Project a conjunct out of a bundled `andAll` in the context. -/
private theorem andAll_project {l : List PLLFormula} {φ : PLLFormula}
    (hmem : φ ∈ l) {Δ : Finset PLLFormula} :
    G4s (insert (andAll l) Δ) φ := by
  refine G4s.andAll_elim hmem ?_
  have h := G4c.iff_set.mp (G4c.iden (Γ := [φ]) (.head _))
  refine h.weaken_subset ?_
  intro y hy
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
    Finset.mem_insert, Finset.mem_singleton] at hy
  simp only [Finset.mem_insert]
  tauto

/-- Step the `interE`-hypothesis up one fuel level (cut through fuel
monotonicity). -/
theorem E_step {p : String} {fuel : Nat} {Γ : List PLLFormula}
    {Δ : Finset PLLFormula} {C : PLLFormula}
    (h : G4s (insert (interE p fuel Γ) Δ) C) :
    G4s (insert (interE p (fuel + 1) Γ) Δ) C := by
  have hm : G4s (insert (interE p (fuel + 1) Γ) Δ) (interE p fuel Γ) := by
    have h₁ := G4c.iff_set.mp ((inter_fuel_mono p fuel).1 Γ)
    refine h₁.weaken_subset ?_
    intro y hy
    simp only [List.toFinset_cons, List.toFinset_nil,
      Finset.insert_empty, Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_insert]
    tauto
  refine G4s.cut_adm hm (h.weaken_subset ?_)
  intro y hy
  simp only [Finset.mem_insert] at hy ⊢
  tauto

/-- **The adequacy pair** (Pitts E2/A2, iSL `pq_correct` shape), at
height-dominated fuel: `n < fuel` is the whole invariant. -/
theorem inter_adequate (p : String) :
    ∀ (n : Nat), ∀ (fuel : Nat) (Γ : List PLLFormula)
      (Δ : Finset PLLFormula) (C : PLLFormula),
    n < fuel →
    G4sh n (Γ.toFinset ∪ Δ) C →
    (∀ ψ ∈ Δ, p ∉ ψ.atoms) →
    ((p ∉ C.atoms → G4s (insert (interE p fuel Γ) Δ) C)
      ∧ G4s (insert (interE p fuel Γ) Δ) (interA p fuel Γ C)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro fuel Γ Δ C hfuel d hΔ
  cases d with
  | @init _ _ a h =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          rcases Finset.mem_union.mp h with hγ | hδ
          · constructor
            · intro hCp
              rw [atoms_prop, Finset.mem_singleton] at hCp
              have ha : ¬ a = p := fun hc => hCp hc.symm
              simp only [interE]
              refine G4s.andAll_elim ?_ (G4s.init (Finset.mem_insert_self _ _))
              refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inr (List.mem_filterMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))))
              simp only
              rw [if_neg ha]
            · by_cases ha : a = p
              · subst ha
                simp only [interA]
                refine G4s.orAll_intro ?_ (G4s.truePLL_intro _)
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))
                simp
              · simp only [interA]
                refine G4s.orAll_intro
                  (List.mem_append.mpr (Or.inl (by
                    rw [if_neg (fun hc => ha hc)]
                    exact .head _))) ?_
                simp only [interE]
                refine G4s.andAll_elim ?_
                  (G4s.init (Finset.mem_insert_self _ _))
                refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_filterMap.mpr
                    ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))))
                simp only
                rw [if_neg (fun hc => ha hc)]
          · have hap : ¬ a = p := by
              have := hΔ _ hδ
              rw [atoms_prop, Finset.mem_singleton] at this
              exact fun hc => this hc.symm
            constructor
            · intro _
              exact G4s.init (Finset.mem_insert_of_mem hδ)
            · simp only [interA]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inl (by
                  rw [if_neg hap]
                  exact .head _))) ?_
              exact G4s.init (Finset.mem_insert_of_mem hδ)
  | @botL _ _ _ h =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hexp : ∀ (D : PLLFormula),
                G4s (insert (interE p (f + 1) Γ) Δ) D := by
              intro D
              simp only [interE]
              refine G4s.andAll_elim ?_
                (G4s.botL (Finset.mem_insert_self _ _))
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos (List.mem_toFinset.mp hγ)]
                            exact .head _))))
            exact ⟨fun _ => hexp C, hexp _⟩
          · exact ⟨fun _ => G4s.botL (Finset.mem_insert_of_mem hδ),
              G4s.botL (Finset.mem_insert_of_mem hδ)⟩
  | @andR m _ A B d₁ d₂ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      have ih₁ := IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ
      have ih₂ := IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₂ hΔ
      constructor
      · intro hCp
        rw [atoms_and, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.andR (ih₁.1 hCp.1) (ih₂.1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have jh₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
            have jh₂ := IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₂ hΔ
            simp only [interA]
            refine G4s.orAll_intro
              (List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_step (G4s.andR jh₁.2 jh₂.2)
  | @orR1 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR1
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ).1 hCp.1)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            simp only [interA]
            refine G4s.orAll_intro
              (List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_step (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ).2
  | @orR2 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR2
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₁ hΔ).1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            simp only [interA]
            refine G4s.orAll_intro
              (List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
            exact E_step (IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₁ hΔ).2
  | @impR m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      constructor
      · intro hCp
        rw [atoms_ifThen, Finset.mem_union] at hCp
        push_neg at hCp
        have dδ := d₁
        rw [ctx_delta] at dδ
        have hres := (IH m (Nat.lt_succ_self m) fuel Γ (insert A Δ) B hm dδ
          (pfree_insert hCp.1 hΔ)).1 hCp.2
        refine G4s.impR ?_
        exact hres.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have dγ := d₁
            rw [ctx_cons] at dγ
            have hres := (IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B hmf dγ hΔ).2
            simp only [interA]
            refine G4s.orAll_intro
              (List.mem_append.mpr (Or.inl (.head _))) ?_
            refine G4s.impR ?_
            exact hres.weaken_subset (by
              intro y hy
              simp only [Finset.mem_insert] at hy ⊢
              tauto)
  | @laxR m _ A d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      constructor
      · intro hCp
        rw [atoms_somehow] at hCp
        exact G4s.laxR
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ).1 hCp)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have hres := (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ).2
            simp only [interA]
            refine G4s.orAll_intro
              (List.mem_append.mpr (Or.inl (.head _))) ?_
            refine G4s.laxR (G4s.impR ?_)
            exact hres.weaken_subset (by
              intro y hy
              simp only [Finset.mem_insert] at hy ⊢
              tauto)
  | @laxL m _ A B h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- witness box on the quantified side
            have hγl := List.mem_toFinset.mp hγ
            have dγ := d₁
            rw [ctx_cons] at dγ
            have ihp := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B.somehow
              hmf dγ hΔ
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim
                (φ := (interE p f (A :: Γ)).somehow) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow, hγl, .head _⟩))
              · refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                exact (ihp.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            · simp only [interA]
              refine G4s.orAll_intro
                (φ := ((interE p f (A :: Γ)).ifThen
                  (interA p f (A :: Γ) B.somehow)).somehow)
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow, hγl, by simp⟩))) ?_
              refine G4s.laxR (G4s.impR ?_)
              exact ihp.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
          · -- witness box on the p-free side
            have hAp : p ∉ A.atoms := by
              have := hΔ _ hδ
              rwa [atoms_somehow] at this
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hΔ' := pfree_insert hAp hΔ
            constructor
            · intro hCp
              have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
              have hres := (IH m (Nat.lt_succ_self m) (f + 1) Γ
                (insert A Δ) B.somehow hm dδ hΔ').1 hCp
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              exact hres.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · -- the self-referential ◯-disjunct
              have hres := (IH m (Nat.lt_succ_self m) f Γ
                (insert A Δ) B.somehow hmf dδ hΔ').2
              simp only [interA]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              refine G4s.laxR (G4s.impR ?_)
              exact hres.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @andL m _ A B _ h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            have dγ := d₁
            rw [ctx_cons₂] at dγ
            have ihp := IH m (Nat.lt_succ_self m) f (A :: B :: Γ) Δ C
              hmf dγ hΔ
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim ?_ (ihp.1 hCp)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.and B, hγl, .head _⟩))
            · simp only [interA, interE]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.and B, hγl, .head _⟩))) ?_
              refine G4s.andAll_elim ?_ ihp.2
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.and B, hγl, .head _⟩))
          · have hABp := hΔ _ hδ
            rw [atoms_and, Finset.mem_union] at hABp
            push_neg at hABp
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert A (insert B Δ)) C hm dδ
              (pfree_insert hABp.1 (pfree_insert hABp.2 hΔ))
            constructor
            · intro hCp
              refine G4s.andL (Finset.mem_insert_of_mem hδ) ?_
              exact (ihp.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · refine G4s.andL (Finset.mem_insert_of_mem hδ) ?_
              exact ihp.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @orL m _ A B _ h d₁ d₂ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            have dγ₁ := d₁
            rw [ctx_cons] at dγ₁
            have dγ₂ := d₂
            rw [ctx_cons] at dγ₂
            have ih₁ := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ C hmf dγ₁ hΔ
            have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ₂ hΔ
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim
                (φ := (interE p f (A :: Γ)).or (interE p f (B :: Γ))) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.or B, hγl, .head _⟩))
              · refine G4s.orL (Finset.mem_insert_self _ _) ?_ ?_
                · exact (ih₁.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
            · simp only [interA]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.or B, hγl, .head _⟩))) ?_
              refine G4s.andR ?_ ?_
              · refine G4s.impR ?_
                exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · refine G4s.impR ?_
                exact ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          · have hABp := hΔ _ hδ
            rw [atoms_or, Finset.mem_union] at hABp
            push_neg at hABp
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert A Δ) C
              hm dδ₁ (pfree_insert hABp.1 hΔ)
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hABp.2 hΔ)
            constructor
            · intro hCp
              refine G4s.orL (Finset.mem_insert_of_mem hδ) ?_ ?_
              · exact (ih₁.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            · refine G4s.orL (Finset.mem_insert_of_mem hδ) ?_ ?_
              · exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · exact ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
  | @impLProp m _ a B _ h ha d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- implication on the quantified side
            have hγl := List.mem_toFinset.mp hγ
            have dγ := d₁
            rw [ctx_cons] at dγ
            have ihp := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ hΔ
            by_cases haΓ : PLLFormula.prop a ∈ Γ
            · -- guarded clause: bare recursion
              constructor
              · intro hCp
                simp only [interE]
                refine G4s.andAll_elim ?_ (ihp.1 hCp)
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(prop a).ifThen B, hγl, ?_⟩))
                simp only
                rw [if_pos haΓ]
                exact .head _
              · simp only [interA, interE]
                refine G4s.orAll_intro
                  (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(prop a).ifThen B, hγl, by
                      simp only
                      rw [if_pos haΓ]
                      exact .head _⟩))) ?_
                refine G4s.andAll_elim ?_ ihp.2
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(prop a).ifThen B, hγl, ?_⟩))
                simp only
                rw [if_pos haΓ]
                exact .head _
            · by_cases hap : a = p
              · -- vacuous: the atom would have to be p, contradicting
                -- either the guard or Δ-p-freeness
                exfalso
                subst hap
                rcases Finset.mem_union.mp ha with haγ | haδ
                · exact haΓ (List.mem_toFinset.mp haγ)
                · exact (hΔ _ haδ) (by
                    rw [atoms_prop]
                    exact Finset.mem_singleton_self _)
              · -- unguarded clause: the atom must sit on the p-free side
                have haδ : PLLFormula.prop a ∈ Δ := by
                  rcases Finset.mem_union.mp ha with haγ | haδ
                  · exact absurd (List.mem_toFinset.mp haγ) haΓ
                  · exact haδ
                constructor
                · intro hCp
                  simp only [interE]
                  refine G4s.andAll_elim_keep
                    (φ := (prop a).ifThen (interE p f (B :: Γ))) ?_ ?_
                  · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg haΓ, if_neg hap]
                    exact .head _
                  · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (G4s.init (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem haδ))) ?_
                    exact (ihp.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                · simp only [interA, interE]
                  refine G4s.orAll_intro
                    (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, by
                        simp only
                        rw [if_neg haΓ, if_neg hap]
                        exact .head _⟩))) ?_
                  refine G4s.andR (G4s.init (Finset.mem_insert_of_mem haδ)) ?_
                  refine G4s.andAll_elim_keep
                    (φ := (prop a).ifThen (interE p f (B :: Γ))) ?_ ?_
                  · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg haΓ, if_neg hap]
                    exact .head _
                  · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (G4s.init (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem haδ))) ?_
                    exact ihp.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
          · -- implication on the p-free side
            have hFp := hΔ _ hδ
            rw [atoms_ifThen, atoms_prop, Finset.mem_union] at hFp
            push_neg at hFp
            have hap : ¬ a = p := fun hc => hFp.1 (by
              rw [Finset.mem_singleton]
              exact hc.symm)
            have hBp := hFp.2
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ (pfree_insert hBp hΔ)
            rcases Finset.mem_union.mp ha with haγ | haδ
            · -- the atom lives on the quantified side: expose E1
              have haγl := List.mem_toFinset.mp haγ
              constructor
              · intro hCp
                simp only [interE]
                have hres := ihp.1 hCp
                simp only [interE] at hres
                refine G4s.andAll_elim_keep (φ := prop a) ?_ ?_
                · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop a, haγl, by
                      simp only
                      rw [if_neg hap]⟩))))
                · refine G4s.impLProp
                    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                    (Finset.mem_insert_self _ _) ?_
                  exact hres.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · simp only [interE]
                have hres := ihp.2
                simp only [interE] at hres
                refine G4s.andAll_elim_keep (φ := prop a) ?_ ?_
                · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop a, haγl, by
                      simp only
                      rw [if_neg hap]⟩))))
                · refine G4s.impLProp
                    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                    (Finset.mem_insert_self _ _) ?_
                  exact hres.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
            · -- pure commute
              constructor
              · intro hCp
                refine G4s.impLProp (Finset.mem_insert_of_mem hδ)
                  (Finset.mem_insert_of_mem haδ) ?_
                exact (ihp.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · refine G4s.impLProp (Finset.mem_insert_of_mem hδ)
                  (Finset.mem_insert_of_mem haδ) ?_
                exact ihp.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
  | @impLAnd m _ A B D₀ _ h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            have dγ := d₁
            rw [ctx_cons] at dγ
            have ihp := IH m (Nat.lt_succ_self m) f
              (A.ifThen (B.ifThen D₀) :: Γ) Δ C hmf dγ hΔ
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim ?_ (ihp.1 hCp)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨(A.and B).ifThen D₀, hγl, .head _⟩))
            · simp only [interA, interE]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.and B).ifThen D₀, hγl, .head _⟩))) ?_
              refine G4s.andAll_elim ?_ ihp.2
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨(A.and B).ifThen D₀, hγl, .head _⟩))
          · have hFp := hΔ _ hδ
            have hPp : p ∉ (A.ifThen (B.ifThen D₀)).atoms := by
              simp only [atoms_ifThen, atoms_and, Finset.mem_union] at hFp ⊢
              tauto
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen (B.ifThen D₀)) Δ) C hm dδ
              (pfree_insert hPp hΔ)
            constructor
            · intro hCp
              refine G4s.impLAnd (Finset.mem_insert_of_mem hδ) ?_
              exact (ihp.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · refine G4s.impLAnd (Finset.mem_insert_of_mem hδ) ?_
              exact ihp.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @impLOr m _ A B D₀ _ h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            have dγ := d₁
            rw [ctx_cons₂] at dγ
            have ihp := IH m (Nat.lt_succ_self m) f
              (A.ifThen D₀ :: B.ifThen D₀ :: Γ) Δ C hmf dγ hΔ
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim ?_ (ihp.1 hCp)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨(A.or B).ifThen D₀, hγl, .head _⟩))
            · simp only [interA, interE]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.or B).ifThen D₀, hγl, .head _⟩))) ?_
              refine G4s.andAll_elim ?_ ihp.2
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨(A.or B).ifThen D₀, hγl, .head _⟩))
          · have hFp := hΔ _ hδ
            have hP₁ : p ∉ (A.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            have hP₂ : p ∉ (B.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen D₀) (insert (B.ifThen D₀) Δ)) C hm dδ
              (pfree_insert hP₁ (pfree_insert hP₂ hΔ))
            constructor
            · intro hCp
              refine G4s.impLOr (Finset.mem_insert_of_mem hδ) ?_
              exact (ihp.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · refine G4s.impLOr (Finset.mem_insert_of_mem hδ) ?_
              exact ihp.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @impLImp m _ A B D₀ _ h d₁ d₂ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- the reset case, paid by the height budget
            have hγl := List.mem_toFinset.mp hγ
            have dγ₁ := d₁
            rw [ctx_cons] at dγ₁
            have dγ₂ := d₂
            rw [ctx_cons] at dγ₂
            have ih₁ := IH m (Nat.lt_succ_self m) f (B.ifThen D₀ :: Γ) Δ
              (A.ifThen B) hmf dγ₁ hΔ
            have ih₂ := IH m (Nat.lt_succ_self m) f (D₀ :: Γ) Δ C hmf dγ₂ hΔ
            -- the guard of the E8/A8 clause, derivable from the IH pair
            have hguard : ∀ (Θ : Finset PLLFormula),
                Δ ⊆ Θ →
                G4s Θ ((interE p f (B.ifThen D₀ :: Γ)).ifThen
                  (interA p f (B.ifThen D₀ :: Γ) (A.ifThen B))) := by
              intro Θ hΘ
              refine G4s.impR ?_
              exact ih₁.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                rcases hy with rfl | hy
                · exact Or.inl rfl
                · exact Or.inr (hΘ hy))
            constructor
            · intro hCp
              simp only [interE]
              refine G4s.andAll_elim_keep
                (φ := ((interE p f (B.ifThen D₀ :: Γ)).ifThen
                    (interA p f (B.ifThen D₀ :: Γ) (A.ifThen B))).ifThen
                  (interE p f (D₀ :: Γ))) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.ifThen B).ifThen D₀, hγl, .head _⟩))
              · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hguard _ (by
                    intro y hy
                    simp only [Finset.mem_insert]
                    tauto)) ?_
                exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            · simp only [interA, interE]
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.ifThen B).ifThen D₀, hγl, .head _⟩))) ?_
              refine G4s.andR (hguard _ (Finset.subset_insert _ _)) ?_
              refine G4s.andAll_elim_keep
                (φ := ((interE p f (B.ifThen D₀ :: Γ)).ifThen
                    (interA p f (B.ifThen D₀ :: Γ) (A.ifThen B))).ifThen
                  (interE p f (D₀ :: Γ))) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.ifThen B).ifThen D₀, hγl, .head _⟩))
              · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hguard _ (by
                    intro y hy
                    simp only [Finset.mem_insert]
                    tauto)) ?_
                exact ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          · -- p-free side: commute (the reset goal is p-free)
            have hFp := hΔ _ hδ
            have hABp : p ∉ (A.ifThen B).atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp ⊢
              tauto
            have hBDp : p ∉ (B.ifThen D₀).atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp ⊢
              tauto
            have hDp : p ∉ D₀.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp
              tauto
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (B.ifThen D₀) Δ) (A.ifThen B) hm dδ₁
              (pfree_insert hBDp hΔ)).1 hABp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert D₀ Δ) C hm dδ₂ (pfree_insert hDp hΔ)
            constructor
            · intro hCp
              refine G4s.impLImp (Finset.mem_insert_of_mem hδ) ?_ ?_
              · exact ih₁.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            · refine G4s.impLImp (Finset.mem_insert_of_mem hδ) ?_ ?_
              · exact ih₁.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · exact ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
  | @impLLax m _ A B _ h d₁ d₂ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            have dγ₂ := d₂
            rw [ctx_cons] at dγ₂
            have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
            have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ₂ hΔ
            -- premise 1's ∀-interpolant, lifted one fuel level
            have hant : G4s (insert (interE p (f + 1) Γ) Δ)
                (interA p f Γ A) := E_step ih₁.2
            constructor
            · intro hCp
              simp only [interE]
              have hant' := hant
              simp only [interE] at hant'
              refine G4s.andAll_elim_keep
                (φ := (interA p f Γ A).ifThen (interE p f (B :: Γ))) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow.ifThen B, hγl, .head _⟩))
              · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)) ?_
                exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
            · simp only [interA, interE]
              have hant' := hant
              simp only [interE] at hant'
              refine G4s.orAll_intro
                (List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow.ifThen B, hγl, .head _⟩))) ?_
              refine G4s.andR hant' ?_
              refine G4s.andAll_elim_keep
                (φ := (interA p f Γ A).ifThen (interE p f (B :: Γ))) ?_ ?_
              · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow.ifThen B, hγl, .head _⟩))
              · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)) ?_
                exact ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          · -- p-free side: commute (premise 1 keeps the context)
            have hFp := hΔ _ hδ
            have hAp : p ∉ A.atoms := by
              simp only [atoms_ifThen, atoms_somehow, Finset.mem_union] at hFp
              tauto
            have hBp : p ∉ B.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp
              tauto
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ Δ A hm d₁ hΔ).1 hAp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ)
            constructor
            · intro hCp
              refine G4s.impLLax (Finset.mem_insert_of_mem hδ) ih₁ ?_
              exact (ih₂.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · refine G4s.impLLax (Finset.mem_insert_of_mem hδ) ih₁ ?_
              exact ih₂.2.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @impLLaxLax m _ A B X _ h hX d₁ d₂ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- principal on the quantified side
            have hγl := List.mem_toFinset.mp hγ
            have dγ₂ := d₂
            rw [ctx_cons] at dγ₂
            have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ₂ hΔ
            rcases Finset.mem_union.mp hX with hXγ | hXδ
            · -- witness also on the quantified side: the witness clause
              have hXγl := List.mem_toFinset.mp hXγ
              have dγ₁ := d₁
              rw [ctx_cons] at dγ₁
              have ih₁ := IH m (Nat.lt_succ_self m) f (X :: Γ) Δ A.somehow
                hmf dγ₁ hΔ
              have hant : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                  G4s Θ (((interE p f (X :: Γ)).ifThen
                    (interA p f (X :: Γ) A.somehow)).somehow) := by
                intro Θ hΘ
                refine G4s.laxR (G4s.impR ?_)
                exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  rcases hy with rfl | hy
                  · exact Or.inl rfl
                  · exact Or.inr (hΘ hy))
              constructor
              · intro hCp
                simp only [interE]
                refine G4s.andAll_elim_keep
                  (φ := (((interE p f (X :: Γ)).ifThen
                      (interA p f (X :: Γ) A.somehow)).somehow).ifThen
                    (interE p f (B :: Γ))) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨X.somehow, hXγl, rfl⟩))))
                · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (by
                      intro y hy
                      simp only [Finset.mem_insert]
                      tauto)) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · simp only [interA, interE]
                refine G4s.orAll_intro
                  (φ := (((interE p f (X :: Γ)).ifThen
                      (interA p f (X :: Γ) A.somehow)).somehow).and
                    (interA p f (B :: Γ) C)) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨X.somehow, hXγl, rfl⟩))))
                refine G4s.andR (hant _ (Finset.subset_insert _ _)) ?_
                refine G4s.andAll_elim_keep
                  (φ := (((interE p f (X :: Γ)).ifThen
                      (interA p f (X :: Γ) A.somehow)).somehow).ifThen
                    (interE p f (B :: Γ))) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨X.somehow, hXγl, rfl⟩))))
                · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (by
                      intro y hy
                      simp only [Finset.mem_insert]
                      tauto)) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
            · -- witness on the p-free side: the γ-clause
              have hXp : p ∉ X.atoms := by
                have := hΔ _ hXδ
                rwa [atoms_somehow] at this
              have dδ₁ := d₁
              rw [ctx_delta] at dδ₁
              have ih₁ := IH m (Nat.lt_succ_self m) f Γ (insert X Δ)
                A.somehow hmf dδ₁ (pfree_insert hXp hΔ)
              have hant : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                  G4s Θ (((interE p f Γ).ifThen
                    (interA p f Γ A.somehow)).somehow) := by
                intro Θ hΘ
                refine G4s.laxL (hΘ hXδ) ?_
                refine G4s.laxR (G4s.impR ?_)
                exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  rcases hy with rfl | hy
                  · exact Or.inl rfl
                  rcases hy with rfl | hy
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr (hΘ hy)))
              constructor
              · intro hCp
                simp only [interE]
                refine G4s.andAll_elim_keep
                  (φ := (((interE p f Γ).ifThen
                      (interA p f Γ A.somehow)).somehow).ifThen
                    (interE p f (B :: Γ))) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (.head _))
                · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (by
                      intro y hy
                      simp only [Finset.mem_insert]
                      tauto)) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · simp only [interA, interE]
                refine G4s.orAll_intro
                  (φ := (((interE p f Γ).ifThen
                      (interA p f Γ A.somehow)).somehow).and
                    (interA p f (B :: Γ) C)) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (.head _))
                refine G4s.andR (hant _ (Finset.subset_insert _ _)) ?_
                refine G4s.andAll_elim_keep
                  (φ := (((interE p f Γ).ifThen
                      (interA p f Γ A.somehow)).somehow).ifThen
                    (interE p f (B :: Γ))) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  exact List.mem_cons.mpr (Or.inr (.head _))
                · refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (by
                      intro y hy
                      simp only [Finset.mem_insert]
                      tauto)) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
          · -- principal on the p-free side
            have hFp := hΔ _ hδ
            have hAp : p ∉ A.somehow.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp
              simp only [atoms_somehow]
              have : p ∉ (A.somehow).atoms := fun hc => hFp (Or.inl hc)
              rwa [atoms_somehow] at this
            have hBp : p ∉ B.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hFp
              tauto
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ)
            rcases Finset.mem_union.mp hX with hXγ | hXδ
            · -- witness on the quantified side: the opening conjunct,
              -- projected at the folded level and cut in
              have hXγl := List.mem_toFinset.mp hXγ
              have dγ₁ := d₁
              rw [ctx_cons] at dγ₁
              have ih₁ := (IH m (Nat.lt_succ_self m) f (X :: Γ) Δ A.somehow
                hmf dγ₁ hΔ).1 hAp
              have hop : G4s (insert (interE p (f + 1) Γ) Δ)
                  ((interE p f (X :: Γ)).somehow) := by
                simp only [interE]
                exact andAll_project (List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨X.somehow, hXγl, .head _⟩)))
              have hfire : ∀ {T : PLLFormula},
                  G4s (insert B (insert ((interE p f (X :: Γ)).somehow)
                    (insert (interE p (f + 1) Γ) Δ))) T →
                  G4s (insert (interE p (f + 1) Γ) Δ) T := by
                intro T hT
                refine G4s.cut_adm hop ?_
                refine G4s.impLLaxLax
                  (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                  (Finset.mem_insert_self _ _) ?_ hT
                exact ih₁.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              constructor
              · intro hCp
                exact hfire ((ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto))
              · exact hfire (ih₂.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto))
            · -- both on the p-free side: pure commute
              have hXp : p ∉ X.atoms := by
                have := hΔ _ hXδ
                rwa [atoms_somehow] at this
              have dδ₁ := d₁
              rw [ctx_delta] at dδ₁
              have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ (insert X Δ)
                A.somehow hm dδ₁ (pfree_insert hXp hΔ)).1 hAp
              constructor
              · intro hCp
                refine G4s.impLLaxLax (Finset.mem_insert_of_mem hδ)
                  (Finset.mem_insert_of_mem hXδ) ?_ ?_
                · exact ih₁.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · refine G4s.impLLaxLax (Finset.mem_insert_of_mem hδ)
                  (Finset.mem_insert_of_mem hXδ) ?_ ?_
                · exact ih₁.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)

/--
info: 'PLLND.inter_adequate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms inter_adequate

end PLLND
