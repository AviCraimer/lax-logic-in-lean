import LaxLogic.PLLG4UITrunc
import absorb_base

/-!
# WIP: adequacy of the truncated quantifiers (v3.1) — the P4a re-run

The adequacy pair for `itpE`/`itpA` over a piece-closed space `S` and
a budget past the jump-state threshold: for a `G4sh`-derivation of
height `n` of `Γ ∪ Δ ⊢ C` with `Δ` p-free, everything inside the
space (`Γ ⊆ S`, `Δ ⊆ S`, `C ∈ S`), and `n < fuel`,

* (E) if `C` is p-free then `itpE p S fuel B Γ, Δ ⊢ C`;
* (A) `itpE p S fuel B Γ, Δ ⊢ itpA p S fuel B Γ C`.

Deltas against the v2 template (`PLLG4UIAdq.inter_adequate`):
guard-splits resolved by the space invariant (omitted clauses are
exactly the same-set skips, closed by the IH at the premise),
budget-gated components lowered with `itp_stab` under the ambient
`E`, the ◯-goal disjunct now guarded at `B-1`, and the Δ-side `laxL`
commute landing on the truncation disjunct by identity.

Build (absorb_base is consumed as a precompiled olean):

    lake env lean wip/absorb_base.lean -o <depdir>/absorb_base.olean
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/adequacy.lean'
-/

open PLLFormula

set_option maxHeartbeats 12000000

namespace PLLND

/-! ### The space invariant -/

/-- Piece-closure of the space: `S` contains every piece that the
clause tables of `itpE`/`itpA` test for, and every goal piece that a
`G4sh` rule can move into the context.  This is exactly what makes
every space gate of a Γ-driven clause satisfiable and the invariant
`Γ ⊆ S ∧ Δ ⊆ S ∧ C ∈ S` re-establishable at every premise. -/
structure PieceClosed (S : Finset PLLFormula) : Prop where
  and_mem : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S
  or_mem : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S
  imp_mem : ∀ {X D : PLLFormula}, X.ifThen D ∈ S → X ∈ S ∧ D ∈ S
  impAnd_mem : ∀ {A B D : PLLFormula},
    (A.and B).ifThen D ∈ S → A.ifThen (B.ifThen D) ∈ S
  impOr_mem : ∀ {A B D : PLLFormula},
    (A.or B).ifThen D ∈ S → A.ifThen D ∈ S ∧ B.ifThen D ∈ S
  impImp_mem : ∀ {A B D : PLLFormula},
    (A.ifThen B).ifThen D ∈ S → B.ifThen D ∈ S
  box_mem : ∀ {χ : PLLFormula}, χ.somehow ∈ S → χ ∈ S

/-! ### Context bookkeeping helpers (v2 transfers) -/

private theorem pfree_insert {p : String} {ψ : PLLFormula}
    {Δ : Finset PLLFormula} (hψ : p ∉ ψ.atoms)
    (hΔ : ∀ χ ∈ Δ, p ∉ χ.atoms) :
    ∀ χ ∈ insert ψ Δ, p ∉ χ.atoms := by
  intro χ hχ
  rcases Finset.mem_insert.mp hχ with rfl | hχ
  · exact hψ
  · exact hΔ χ hχ

private theorem memS_insert {S : Finset PLLFormula} {ψ : PLLFormula}
    {Δ : Finset PLLFormula} (hψ : ψ ∈ S) (hΔ : ∀ χ ∈ Δ, χ ∈ S) :
    ∀ χ ∈ insert ψ Δ, χ ∈ S := by
  intro χ hχ
  rcases Finset.mem_insert.mp hχ with rfl | hχ
  · exact hψ
  · exact hΔ χ hχ

private theorem memS_cons {S : Finset PLLFormula} {X : PLLFormula}
    {Γ : List PLLFormula} (hX : X ∈ S) (hΓ : ∀ F ∈ Γ, F ∈ S) :
    ∀ F ∈ X :: Γ, F ∈ S := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hX
  · exact hΓ F hF

private theorem memS_cons₂ {S : Finset PLLFormula} {X Y : PLLFormula}
    {Γ : List PLLFormula} (hX : X ∈ S) (hY : Y ∈ S)
    (hΓ : ∀ F ∈ Γ, F ∈ S) : ∀ F ∈ X :: Y :: Γ, F ∈ S :=
  memS_cons hX (memS_cons hY hΓ)

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

/-- Same-set absorption: a context piece already in the Γ-list. -/
private theorem ctx_absorb {X : PLLFormula} {Γ : List PLLFormula}
    {Δ : Finset PLLFormula} (hX : X ∈ Γ) :
    insert X (Γ.toFinset ∪ Δ) = Γ.toFinset ∪ Δ :=
  Finset.insert_eq_self.mpr
    (Finset.mem_union_left _ (List.mem_toFinset.mpr hX))

/-! ### G4c-to-G4s consumption helpers -/

/-- Feed a one-hypothesis `G4c` fact from a context member. -/
private theorem of_G4c1 {X Y : PLLFormula} (h : G4c [X] Y)
    {Δ : Finset PLLFormula} (hX : X ∈ Δ) : G4s Δ Y := by
  refine (G4c.iff_set.mp h).weaken_subset ?_
  intro y hy
  simp only [List.toFinset_cons, List.toFinset_nil,
    LawfulSingleton.insert_empty_eq, Finset.mem_singleton] at hy
  exact hy ▸ hX

/-- Feed a two-hypothesis `G4c` fact from two context members. -/
private theorem of_G4c2 {X₁ X₂ Y : PLLFormula} (h : G4c [X₁, X₂] Y)
    {Δ : Finset PLLFormula} (h₁ : X₁ ∈ Δ) (h₂ : X₂ ∈ Δ) : G4s Δ Y := by
  refine (G4c.iff_set.mp h).weaken_subset ?_
  intro y hy
  simp only [List.toFinset_cons, List.toFinset_nil,
    LawfulSingleton.insert_empty_eq, Finset.mem_insert,
    Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact h₁
  · exact h₂

/-- Identity for an arbitrary context member, set side. -/
private theorem G4s_id {φ : PLLFormula} {Δ : Finset PLLFormula}
    (h : φ ∈ Δ) : G4s Δ φ :=
  of_G4c1 (G4c.identity_mem (.head _)) h

/-- Project a conjunct out of a bundled `andAll` in the context. -/
private theorem andAll_project {l : List PLLFormula} {φ : PLLFormula}
    (hmem : φ ∈ l) {Δ : Finset PLLFormula} :
    G4s (insert (andAll l) Δ) φ :=
  G4s.andAll_elim hmem (G4s_id (Finset.mem_insert_self _ _))

/-! ### Fuel/budget/congruence plumbing for the truncated quantifiers -/

/-- Step the `itpE`-hypothesis up one fuel level (cut through fuel
monotonicity) — the v2 `E_step` re-proved for v3. -/
private theorem E_lift {p : String} {S : Finset PLLFormula}
    {fuel b : Nat} {Γ : List PLLFormula} {Δ : Finset PLLFormula}
    {C : PLLFormula} (h : G4s (insert (itpE p S fuel b Γ) Δ) C) :
    G4s (insert (itpE p S (fuel + 1) b Γ) Δ) C := by
  have hm : G4s (insert (itpE p S (fuel + 1) b Γ) Δ) (itpE p S fuel b Γ) :=
    of_G4c1 ((itp_fuel_mono p S fuel).1 b Γ) (Finset.mem_insert_self _ _)
  refine G4s.cut_adm hm (h.weaken_subset ?_)
  intro y hy
  simp only [Finset.mem_insert] at hy ⊢
  tauto

/-- Chain two single-hypothesis `G4c` facts. -/
private theorem g4c_chain {X Y Z : PLLFormula} (h₁ : G4c [X] Y)
    (h₂ : G4c [Y] Z) : G4c [X] Z :=
  G4c.cut h₁ ((h₂.weaken _).perm (List.Perm.swap _ _ _))

/-- The ambient `E` at successor fuel feeds the component-level `E`
at any set-equal list. -/
private theorem E_feed {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ Γ' : List PLLFormula}
    (hset : Γ.toFinset = Γ'.toFinset) {Θ : Finset PLLFormula}
    (hmem : itpE p S (f + 1) b Γ ∈ Θ) : G4s Θ (itpE p S f b Γ') :=
  of_G4c1 (g4c_chain ((itp_fuel_mono p S f).1 b Γ)
    ((itp_congr p S f).1 b Γ Γ' hset)) hmem

/-- Budget lowering under the ambient `E` (absorption, consumption
form): with `itpE f (b₀+1) Γ` in context, an `itpA f (b₀+1) Γ C`
value feeds the `b₀` slot. -/
private theorem stab_lower {p : String} {S : Finset PLLFormula}
    (hPC : PieceClosed S)
    {b₀ : Nat} (hB : kcap S < b₀ + 1) {f : Nat} {Γ : List PLLFormula}
    {C : PLLFormula} {Θ : Finset PLLFormula}
    (hΓS : ∀ F ∈ Γ, F ∈ S) (hCS : C ∈ S)
    (hE : itpE p S f (b₀ + 1) Γ ∈ Θ)
    (hA : G4s Θ (itpA p S f (b₀ + 1) Γ C)) :
    G4s Θ (itpA p S f b₀ Γ C) := by
  refine G4s.cut_adm hA (of_G4c2
    ((itp_stab p S hPC.and_mem hPC.or_mem hPC.imp_mem hPC.box_mem
        f (b₀ + 1) hB).2 Γ C hΓS hCS)
    (Finset.mem_insert_of_mem hE) (Finset.mem_insert_self _ _))

/-- An `others`-disjunct is a disjunct of the full table, any goal. -/
private theorem mem_full_of_oth {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C φ : PLLFormula}
    (h : φ ∈ itpAoth p S f b Γ C) : φ ∈ itpAfull p S f b Γ C := by
  cases C <;> simp only [itpAfull] <;>
    first
      | exact h
      | exact List.mem_append.mpr (Or.inl h)

/-- An environment disjunct is a disjunct of the full table. -/
private theorem mem_full_of_env {p : String} {S : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C φ : PLLFormula}
    (h : φ ∈ itpAenv p S f b Γ C) : φ ∈ itpAfull p S f b Γ C :=
  mem_full_of_oth (by
    simp only [itpAoth]
    exact List.mem_append.mpr (Or.inr h))

/-- Cut a component-level `E` (at a set-equal list) from the ambient
successor-fuel `E`, then consume an IH-style result. -/
private theorem E_cut {p : String} {S : Finset PLLFormula} {f b : Nat}
    {Γ Γ' : List PLLFormula} (hset : Γ.toFinset = Γ'.toFinset)
    {Θ Δ : Finset PLLFormula} {D : PLLFormula}
    (hmem : itpE p S (f + 1) b Γ ∈ Θ) (hsub : Δ ⊆ Θ)
    (h : G4s (insert (itpE p S f b Γ') Δ) D) : G4s Θ D :=
  G4s.cut_adm (E_feed hset hmem)
    (h.weaken_subset (Finset.insert_subset_insert _ hsub))

/-! ### The adequacy pair -/

set_option maxHeartbeats 12000000 in
/-- **The adequacy pair for the truncated quantifiers** (the P4a
re-run): height-dominated fuel, one ambient budget past the
jump-state threshold, all data inside a piece-closed space. -/
theorem itp_adequate (p : String) (S : Finset PLLFormula)
    (hPC : PieceClosed S) {B : Nat} (hB : kcap S < B) :
    ∀ (n : Nat), ∀ (fuel : Nat) (Γ : List PLLFormula)
      (Δ : Finset PLLFormula) (C : PLLFormula),
    n < fuel → G4sh n (Γ.toFinset ∪ Δ) C →
    (∀ ψ ∈ Δ, p ∉ ψ.atoms) →
    (∀ F ∈ Γ, F ∈ S) → (∀ ψ ∈ Δ, ψ ∈ S) → C ∈ S →
    ((p ∉ C.atoms → G4s (insert (itpE p S fuel B Γ) Δ) C)
      ∧ G4s (insert (itpE p S fuel B Γ) Δ) (itpA p S fuel B Γ C)) := by
  obtain ⟨b₀, rfl⟩ : ∃ b₀, B = b₀ + 1 :=
    ⟨B - 1, by have := kcap_ge (S := S); omega⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro fuel Γ Δ C hfuel d hΔ hΓS hΔS hCS
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
              rw [itpE_succ]
              refine G4s.andAll_elim ?_
                (G4s.init (Finset.mem_insert_self _ _))
              refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inr (List.mem_filterMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))))
              simp only
              rw [if_neg ha]
            · by_cases ha : a = p
              · subst ha
                rw [itpA_succ]
                refine G4s.orAll_intro ?_ (G4s.truePLL_intro _)
                simp only [itpAfull, itpAoth]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))
                simp
              · rw [itpA_succ]
                refine G4s.orAll_intro (φ := prop a)
                  (by simp only [itpAfull, itpAoth, itpAgoal]
                      refine List.mem_append.mpr (Or.inl ?_)
                      rw [if_neg (fun hc => ha hc)]
                      exact .head _) ?_
                rw [itpE_succ]
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
            · rw [itpA_succ]
              refine G4s.orAll_intro (φ := prop a)
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_neg hap]
                    exact .head _) ?_
              exact G4s.init (Finset.mem_insert_of_mem hδ)
  | @botL _ _ _ h =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hexp : ∀ (D : PLLFormula),
                G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) D := by
              intro D
              rw [itpE_succ]
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
      obtain ⟨hAS, hBS⟩ := hPC.and_mem hCS
      have ih₁ := IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS
      have ih₂ := IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₂ hΔ hΓS hΔS hBS
      constructor
      · intro hCp
        rw [atoms_and, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.andR (ih₁.1 hCp.1) (ih₂.1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have jh₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ hΓS hΔS hAS
            have jh₂ := IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₂ hΔ hΓS hΔS hBS
            rw [itpA_succ]
            refine G4s.orAll_intro
              (φ := (itpA p S f (b₀ + 1) Γ A).and (itpA p S f (b₀ + 1) Γ B))
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_lift (G4s.andR jh₁.2 jh₂.2)
  | @orR1 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.or_mem hCS
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR1
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS).1 hCp.1)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            rw [itpA_succ]
            refine G4s.orAll_intro (φ := itpA p S f (b₀ + 1) Γ A)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_lift
              (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ hΓS hΔS hAS).2
  | @orR2 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.or_mem hCS
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR2
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₁ hΔ hΓS hΔS hBS).1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            rw [itpA_succ]
            refine G4s.orAll_intro (φ := itpA p S f (b₀ + 1) Γ B)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
            exact E_lift
              (IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₁ hΔ hΓS hΔS hBS).2
  | @impR m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.imp_mem hCS
      constructor
      · intro hCp
        rw [atoms_ifThen, Finset.mem_union] at hCp
        push_neg at hCp
        have dδ := d₁
        rw [ctx_delta] at dδ
        have hres := (IH m (Nat.lt_succ_self m) fuel Γ (insert A Δ) B hm dδ
          (pfree_insert hCp.1 hΔ) hΓS (memS_insert hAS hΔS) hBS).1 hCp.2
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
            have hres := (IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B hmf dγ hΔ
              (memS_cons hAS hΓS) hΔS hBS).2
            rw [itpA_succ]
            by_cases hAΓ : A ∈ Γ
            · -- same-set antecedent: budget-gated guard, body at full
              -- budget; land through the ambient via set-congruence
              refine G4s.orAll_intro
                (φ := (itpE p S f b₀ (A :: Γ)).ifThen
                  (itpA p S f (b₀ + 1) (A :: Γ) B))
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_pos hAΓ]
                    exact .head _) ?_
              refine G4s.impR ?_
              have hset : Γ.toFinset = (A :: Γ).toFinset := by
                rw [List.toFinset_cons,
                  Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hAΓ)]
              refine E_cut hset
                (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                (fun y hy => Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hy)) hres
            · refine G4s.orAll_intro
                (φ := (itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                  (itpA p S f (b₀ + 1) (A :: Γ) B))
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_neg hAΓ]
                    exact .head _) ?_
              refine G4s.impR ?_
              exact hres.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @laxR m _ A d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      have hAS := hPC.box_mem hCS
      constructor
      · intro hCp
        rw [atoms_somehow] at hCp
        exact G4s.laxR
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS).1 hCp)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have hres := (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
              hΓS hΔS hAS).2
            rw [itpA_succ]
            refine G4s.orAll_intro
              (φ := ((itpE p S f b₀ Γ).ifThen
                (itpA p S f (b₀ + 1) Γ A)).somehow)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl
                    (List.mem_append.mpr (Or.inl (.head _))))) ?_
            refine G4s.laxR (G4s.impR ?_)
            exact E_cut rfl
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              (fun y hy => Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hy)) hres
  | @laxL m _ A B h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- witness box on the quantified side
            have hγl := List.mem_toFinset.mp hγ
            have hAS := hPC.box_mem (hΓS _ hγl)
            by_cases hAΓ : A ∈ Γ
            · -- body already present: same-set skip
              have dabs := d₁
              rw [ctx_absorb hAΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ B.somehow
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hgate : ¬ (A ∈ Γ ∨ A ∉ S) := by
                push_neg
                exact ⟨hAΓ, hAS⟩
              have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B.somehow
                hmf dγ hΔ (memS_cons hAS hΓS) hΔS hCS
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim
                  (φ := (itpE p S f (b₀ + 1) (A :: Γ)).somehow) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow, hγl, ?_⟩))
                  simp only
                  rw [if_neg hgate]
                  exact .head _
                · refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                  exact (ihp.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · rw [itpA_succ]
                refine G4s.orAll_intro
                  (φ := ((itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                    (itpA p S f (b₀ + 1) (A :: Γ) B.somehow)).somehow)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.somehow, hγl, by
                      simp only
                      rw [if_neg hgate]
                      exact .head _⟩)) ?_
                refine G4s.laxR (G4s.impR ?_)
                exact ihp.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          · -- witness box on the p-free side: land the truncation
            -- disjunct through the IH's own disjunction
            have hAp : p ∉ A.atoms := by
              have := hΔ _ hδ
              rwa [atoms_somehow] at this
            have hAS := hPC.box_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hΔ' := pfree_insert hAp hΔ
            have hΔS' := memS_insert hAS hΔS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert A Δ)
              B.somehow hm dδ hΔ' hΓS hΔS' hCS
            constructor
            · intro hCp
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              exact (ihp.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · have hne : itpAoth p S f (b₀ + 1) Γ (B.somehow) ≠ [] := by
                simp [itpAoth, itpAgoal]
              have heq : itpAfull p S f (b₀ + 1) Γ (B.somehow)
                  = itpAoth p S f (b₀ + 1) Γ (B.somehow) ++
                    [((itpE p S f b₀ Γ).ifThen
                      (orAll (itpAoth p S f (b₀ + 1) Γ (B.somehow)))).somehow] := by
                simp only [itpAfull]
                rw [if_neg (by simpa [List.isEmpty_iff] using hne)]
              rw [itpA_succ, heq]
              refine G4s.orAll_intro
                (φ := ((itpE p S f b₀ Γ).ifThen
                  (orAll (itpAoth p S f (b₀ + 1) Γ (B.somehow)))).somehow)
                (List.mem_append.mpr (Or.inr (.head _))) ?_
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              have hcut : G4s (insert A (insert
                  (itpE p S (f + 1) (b₀ + 1) Γ) Δ))
                  (itpA p S (f + 1) (b₀ + 1) Γ B.somehow) :=
                ihp.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              refine G4s.cut_adm hcut ?_
              rw [itpA_succ, heq]
              refine G4s.orAll_elim ?_
              intro φ hφ
              rcases List.mem_append.mp hφ with hoth | htr
              · -- an `others`-disjunct re-enters under the guard
                refine G4s.laxR (G4s.impR ?_)
                exact G4s.orAll_intro hoth
                  (G4s_id (Finset.mem_insert_of_mem
                    (Finset.mem_insert_self _ _)))
              · -- the truncation disjunct is the goal: identity
                have := List.mem_singleton.mp htr
                subst this
                exact G4s_id (Finset.mem_insert_self _ _)
  | @andL m _ A B _ h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            obtain ⟨hAS, hBS⟩ := hPC.and_mem (hΓS _ hγl)
            by_cases hpres : A ∈ Γ ∧ B ∈ Γ
            · -- both pieces present: same-set skip via the premise IH
              have dabs := d₁
              rw [ctx_absorb hpres.2, ctx_absorb hpres.1] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) :=
                ⟨Or.inr hAS, Or.inr hBS⟩
              have dγ := d₁
              rw [ctx_cons₂] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (A :: B :: Γ) Δ C
                hmf dγ hΔ (memS_cons₂ hAS hBS hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1) (A :: B :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.and B, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1) (A :: B :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.and B, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hABp := hΔ _ hδ
            rw [atoms_and, Finset.mem_union] at hABp
            push_neg at hABp
            obtain ⟨hAS, hBS⟩ := hPC.and_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert A (insert B Δ)) C hm dδ
              (pfree_insert hABp.1 (pfree_insert hABp.2 hΔ)) hΓS
              (memS_insert hAS (memS_insert hBS hΔS)) hCS
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
            obtain ⟨hAS, hBS⟩ := hPC.or_mem (hΓS _ hγl)
            by_cases hpres : A ∈ Γ ∨ B ∈ Γ
            · -- a branch piece is present: that premise IH concludes
              rcases hpres with hA | hB
              · have dabs := d₁
                rw [ctx_absorb hA] at dabs
                exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                  (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
              · have dabs := d₂
                rw [ctx_absorb hB] at dabs
                exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                  (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : A ∈ S ∧ B ∈ S := ⟨hAS, hBS⟩
              have dγ₁ := d₁
              rw [ctx_cons] at dγ₁
              have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₁ := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ C hmf dγ₁
                hΔ (memS_cons hAS hΓS) hΔS hCS
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ₂
                hΔ (memS_cons hBS hΓS) hΔS hCS
              have hEmem : (itpE p S f (b₀ + 1) (A :: Γ)).or
                  (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.or B, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim hEmem ?_
                refine G4s.orL (Finset.mem_insert_self _ _) ?_ ?_
                · exact (ih₁.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · rw [itpA_succ]
                refine G4s.orAll_intro
                  (φ := ((itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (A :: Γ) C)).and
                    ((itpE p S f (b₀ + 1) (B :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B :: Γ) C)))
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.or B, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
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
            obtain ⟨hAS, hBS⟩ := hPC.or_mem (hΔS _ hδ)
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert A Δ) C
              hm dδ₁ (pfree_insert hABp.1 hΔ) hΓS (memS_insert hAS hΔS) hCS
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hABp.2 hΔ) hΓS (memS_insert hBS hΔS) hCS
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
            have hBS := (hPC.imp_mem (hΓS _ hγl)).2
            by_cases hBΓ : B ∈ Γ
            · -- consequent already present: same-set skip
              have dabs := d₁
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ
                hΔ (memS_cons hBS hΓS) hΔS hCS
              by_cases haΓ : PLLFormula.prop a ∈ Γ
              · -- guarded clause: bare recursion
                have hEmem : itpE p S f (b₀ + 1) (B :: Γ) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(prop a).ifThen B, hγl, ?_⟩))
                  simp only
                  rw [if_neg hBΓ, if_pos hBS, if_pos haΓ]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  exact G4s.andAll_elim hEmem (ihp.1 hCp)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := itpA p S f (b₀ + 1) (B :: Γ) C)
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, by
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos haΓ]
                        exact .head _⟩)) ?_
                  exact G4s.andAll_elim hEmem ihp.2
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
                · -- unguarded clause: the atom sits on the p-free side
                  have haδ : PLLFormula.prop a ∈ Δ := by
                    rcases Finset.mem_union.mp ha with haγ | haδ
                    · exact absurd (List.mem_toFinset.mp haγ) haΓ
                    · exact haδ
                  have hEmem : (prop a).ifThen (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS, if_neg haΓ, if_neg hap]
                    exact .head _
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hEmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (G4s.init (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem haδ))) ?_
                    exact (ihp.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (prop a).and (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨(prop a).ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg haΓ, if_neg hap]
                          exact .head _⟩)) ?_
                    refine G4s.andR (G4s.init (Finset.mem_insert_of_mem haδ)) ?_
                    refine G4s.andAll_elim_keep hEmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
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
            have hBS := (hPC.imp_mem (hΔS _ hδ)).2
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
            rcases Finset.mem_union.mp ha with haγ | haδ
            · -- the atom lives on the quantified side: expose E1
              have haγl := List.mem_toFinset.mp haγ
              have hamem : prop a ∈ itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_filterMap.mpr ⟨prop a, haγl, ?_⟩))))
                simp only
                rw [if_neg hap]
              constructor
              · intro hCp
                rw [itpE_succ]
                have hres := ihp.1 hCp
                rw [itpE_succ] at hres
                refine G4s.andAll_elim_keep hamem ?_
                refine G4s.impLProp
                  (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                  (Finset.mem_insert_self _ _) ?_
                exact hres.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · rw [itpE_succ]
                have hres := ihp.2
                rw [itpE_succ] at hres
                refine G4s.andAll_elim_keep hamem ?_
                refine G4s.impLProp
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
            have hPS := hPC.impAnd_mem (hΓS _ hγl)
            by_cases hPΓ : A.ifThen (B.ifThen D₀) ∈ Γ
            · have dabs := d₁
              rw [ctx_absorb hPΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f
                (A.ifThen (B.ifThen D₀) :: Γ) Δ C hmf dγ hΔ
                (memS_cons hPS hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1)
                  (A.ifThen (B.ifThen D₀) :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.and B).ifThen D₀, hγl, ?_⟩))
                simp only
                rw [if_neg hPΓ, if_pos hPS]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1)
                    (A.ifThen (B.ifThen D₀) :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨(A.and B).ifThen D₀, hγl, by
                      simp only
                      rw [if_neg hPΓ, if_pos hPS]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hFp := hΔ _ hδ
            have hPp : p ∉ (A.ifThen (B.ifThen D₀)).atoms := by
              simp only [atoms_ifThen, atoms_and, Finset.mem_union] at hFp ⊢
              tauto
            have hPS := hPC.impAnd_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen (B.ifThen D₀)) Δ) C hm dδ
              (pfree_insert hPp hΔ) hΓS (memS_insert hPS hΔS) hCS
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
            obtain ⟨hP₁S, hP₂S⟩ := hPC.impOr_mem (hΓS _ hγl)
            by_cases hpres : A.ifThen D₀ ∈ Γ ∧ B.ifThen D₀ ∈ Γ
            · have dabs := d₁
              rw [ctx_absorb hpres.2, ctx_absorb hpres.1] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : (A.ifThen D₀ ∈ Γ ∨ A.ifThen D₀ ∈ S) ∧
                  (B.ifThen D₀ ∈ Γ ∨ B.ifThen D₀ ∈ S) :=
                ⟨Or.inr hP₁S, Or.inr hP₂S⟩
              have dγ := d₁
              rw [ctx_cons₂] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f
                (A.ifThen D₀ :: B.ifThen D₀ :: Γ) Δ C hmf dγ hΔ
                (memS_cons₂ hP₁S hP₂S hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1)
                  (A.ifThen D₀ :: B.ifThen D₀ :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.or B).ifThen D₀, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1)
                    (A.ifThen D₀ :: B.ifThen D₀ :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨(A.or B).ifThen D₀, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hFp := hΔ _ hδ
            have hP₁ : p ∉ (A.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            have hP₂ : p ∉ (B.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            obtain ⟨hP₁S, hP₂S⟩ := hPC.impOr_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen D₀) (insert (B.ifThen D₀) Δ)) C hm dδ
              (pfree_insert hP₁ (pfree_insert hP₂ hΔ)) hΓS
              (memS_insert hP₁S (memS_insert hP₂S hΔS)) hCS
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
          · have hγl := List.mem_toFinset.mp hγ
            have hprinS := hΓS _ hγl
            obtain ⟨hABS, hDS⟩ := hPC.imp_mem hprinS
            have hPS := hPC.impImp_mem hprinS
            by_cases hDΓ : D₀ ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hDΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₂ := IH m (Nat.lt_succ_self m) f (D₀ :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hDS hΓS) hΔS hCS
              by_cases hBDΓ : B.ifThen D₀ ∈ Γ
              · -- present piece: the jump clause, components at b₀,
                -- fed by absorption under the ambient E
                have dabs₁ := d₁
                rw [ctx_absorb hBDΓ] at dabs₁
                have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ (A.ifThen B)
                  hmf dabs₁ hΔ hΓS hΔS hABS
                have hguard : ∀ (Θ : Finset PLLFormula),
                    itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                    G4s Θ ((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ (A.ifThen B))) := by
                  intro Θ hamb hΘ
                  refine G4s.impR ?_
                  refine G4s.cut_adm
                    (E_feed rfl (Finset.mem_insert_of_mem hamb)) ?_
                  refine stab_lower hPC hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    · exact Or.inr (Or.inr (hΘ hy)))
                have hEmem : ((itpE p S f b₀ Γ).ifThen
                    (itpA p S f b₀ Γ (A.ifThen B))).ifThen
                      (itpE p S f (b₀ + 1) (D₀ :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A.ifThen B).ifThen D₀, hγl, ?_⟩))
                  simp only
                  rw [if_neg hDΓ, if_pos hDS, if_pos hBDΓ, if_pos hprinS]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := ((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ (A.ifThen B))).and
                        (itpA p S f (b₀ + 1) (D₀ :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(A.ifThen B).ifThen D₀, hγl, by
                        simp only
                        rw [if_neg hDΓ, if_pos hDS, if_pos hBDΓ,
                          if_pos hprinS]
                        exact .head _⟩)) ?_
                  refine G4s.andR
                    (hguard _ (Finset.mem_insert_self _ _)
                      (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · -- fresh piece: the reset clause at full budget
                have dγ₁ := d₁
                rw [ctx_cons] at dγ₁
                have ih₁ := IH m (Nat.lt_succ_self m) f
                  (B.ifThen D₀ :: Γ) Δ (A.ifThen B) hmf dγ₁ hΔ
                  (memS_cons hPS hΓS) hΔS hABS
                have hguard : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                    G4s Θ ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                        (A.ifThen B))) := by
                  intro Θ hΘ
                  refine G4s.impR ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    · exact Or.inr (hΘ hy))
                have hEmem : ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                    (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                      (A.ifThen B))).ifThen
                      (itpE p S f (b₀ + 1) (D₀ :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A.ifThen B).ifThen D₀, hγl, ?_⟩))
                  simp only
                  rw [if_neg hDΓ, if_pos hDS, if_neg hBDΓ, if_pos hPS]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                        (A.ifThen B))).and
                          (itpA p S f (b₀ + 1) (D₀ :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(A.ifThen B).ifThen D₀, hγl, by
                        simp only
                        rw [if_neg hDΓ, if_pos hDS, if_neg hBDΓ, if_pos hPS]
                        exact .head _⟩)) ?_
                  refine G4s.andR (hguard _ (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
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
            have hprinS := hΔS _ hδ
            obtain ⟨hABS, hDS⟩ := hPC.imp_mem hprinS
            have hPS := hPC.impImp_mem hprinS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (B.ifThen D₀) Δ) (A.ifThen B) hm dδ₁
              (pfree_insert hBDp hΔ) hΓS (memS_insert hPS hΔS) hABS).1 hABp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert D₀ Δ) C hm dδ₂ (pfree_insert hDp hΔ) hΓS
              (memS_insert hDS hΔS) hCS
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
            have hprinS := hΓS _ hγl
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            have hAS := hPC.box_mem hboxAS
            by_cases hBΓ : B ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
                hΓS hΔS hAS
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hBS hΓS) hΔS hCS
              -- premise 1's ∀-interpolant, absorbed into the b₀ slot
              have hant : ∀ (Θ : Finset PLLFormula),
                  itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                  G4s Θ (itpA p S f b₀ Γ A) := by
                intro Θ hamb hΘ
                refine G4s.cut_adm (E_feed rfl hamb) ?_
                refine stab_lower hPC hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  rcases hy with rfl | hy
                  · exact Or.inl rfl
                  · exact Or.inr (hΘ hy))
              have hEmem : (itpA p S f b₀ Γ A).ifThen
                  (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow.ifThen B, hγl, ?_⟩))
                simp only
                rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim_keep hEmem ?_
                refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant _ (Finset.mem_insert_of_mem
                      (Finset.mem_insert_self _ _))
                    (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
                exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := (itpA p S f b₀ Γ A).and
                    (itpA p S f (b₀ + 1) (B :: Γ) C))
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, by
                      simp only
                      rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                      exact .head _⟩)) ?_
                refine G4s.andR
                  (hant _ (Finset.mem_insert_self _ _)
                    (Finset.subset_insert _ _)) ?_
                refine G4s.andAll_elim_keep hEmem ?_
                refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant _ (Finset.mem_insert_of_mem
                      (Finset.mem_insert_self _ _))
                    (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
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
            have hprinS := hΔS _ hδ
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            have hAS := hPC.box_mem hboxAS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ Δ A hm d₁ hΔ
              hΓS hΔS hAS).1 hAp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
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
            have hprinS := hΓS _ hγl
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            by_cases hBΓ : B ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hBS hΓS) hΔS hCS
              rcases Finset.mem_union.mp hX with hXγ | hXδ
              · -- witness also on the quantified side
                have hXγl := List.mem_toFinset.mp hXγ
                have hXS := hPC.box_mem (hΓS _ hXγl)
                by_cases hXΓ : X ∈ Γ
                · -- witness body present: γ-clause fed by absorption
                  have dabs₁ := d₁
                  rw [ctx_absorb hXΓ] at dabs₁
                  have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ A.somehow
                    hmf dabs₁ hΔ hΓS hΔS hboxAS
                  have hant : ∀ (Θ : Finset PLLFormula),
                      itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                      G4s Θ (((itpE p S f b₀ Γ).ifThen
                        (itpA p S f b₀ Γ A.somehow)).somehow) := by
                    intro Θ hamb hΘ
                    refine G4s.laxR (G4s.impR ?_)
                    refine G4s.cut_adm
                      (E_feed rfl (Finset.mem_insert_of_mem hamb)) ?_
                    refine stab_lower hPC hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                    exact ih₁.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      rcases hy with rfl | hy
                      · exact Or.inl rfl
                      · exact Or.inr (Or.inr (hΘ hy)))
                  have hgmem : (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow).ifThen
                        (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                    exact .tail _ (.head _)
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (Finset.mem_insert_of_mem
                          (Finset.mem_insert_self _ _))
                        (fun y hy => Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem hy))) ?_
                    exact (ih₂.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (((itpE p S f b₀ Γ).ifThen
                        (itpA p S f b₀ Γ A.somehow)).somehow).and
                          (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨A.somehow.ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                          exact .tail _ (.head _)⟩)) ?_
                    refine G4s.andR
                      (hant _ (Finset.mem_insert_self _ _)
                        (Finset.subset_insert _ _)) ?_
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (Finset.mem_insert_of_mem
                          (Finset.mem_insert_self _ _))
                        (fun y hy => Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem hy))) ?_
                    exact ih₂.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                · -- fresh witness body: the per-witness clause
                  have hgate : ¬ (X ∈ Γ ∨ X ∉ S) := by
                    push_neg
                    exact ⟨hXΓ, hXS⟩
                  have dγ₁ := d₁
                  rw [ctx_cons] at dγ₁
                  have ih₁ := IH m (Nat.lt_succ_self m) f (X :: Γ) Δ
                    A.somehow hmf dγ₁ hΔ (memS_cons hXS hΓS) hΔS hboxAS
                  have hant : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                      G4s Θ (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                        (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow) := by
                    intro Θ hΘ
                    refine G4s.laxR (G4s.impR ?_)
                    exact ih₁.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      rcases hy with rfl | hy
                      · exact Or.inl rfl
                      · exact Or.inr (hΘ hy))
                  have hgmem : (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow).ifThen
                        (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_filterMap.mpr ⟨X.somehow, hXγl, ?_⟩))
                    simp only
                    rw [if_neg hgate]
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                    exact (ih₂.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                        (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow).and
                          (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨A.somehow.ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_filterMap.mpr ⟨X.somehow, hXγl, ?_⟩))
                          simp only
                          rw [if_neg hgate]⟩)) ?_
                    refine G4s.andR
                      (hant _ (Finset.subset_insert _ _)) ?_
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                    exact ih₂.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
              · -- witness on the p-free side: γ-clause after laxL
                have hXp : p ∉ X.atoms := by
                  have := hΔ _ hXδ
                  rwa [atoms_somehow] at this
                have hXS := hPC.box_mem (hΔS _ hXδ)
                have dδ₁ := d₁
                rw [ctx_delta] at dδ₁
                have ih₁ := IH m (Nat.lt_succ_self m) f Γ (insert X Δ)
                  A.somehow hmf dδ₁ (pfree_insert hXp hΔ) hΓS
                  (memS_insert hXS hΔS) hboxAS
                have hant : ∀ (Θ : Finset PLLFormula),
                    itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                    G4s Θ (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow) := by
                  intro Θ hamb hΘ
                  refine G4s.laxL (hΘ hXδ) ?_
                  refine G4s.laxR (G4s.impR ?_)
                  refine G4s.cut_adm
                    (E_feed rfl (Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hamb))) ?_
                  refine stab_lower hPC hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    rcases hy with rfl | hy
                    · exact Or.inr (Or.inr (Or.inl rfl))
                    · exact Or.inr (Or.inr (Or.inr (hΘ hy))))
                have hgmem : (((itpE p S f b₀ Γ).ifThen
                    (itpA p S f b₀ Γ A.somehow)).somehow).ifThen
                      (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  simp only
                  rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                  exact .tail _ (.head _)
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hgmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow).and
                        (itpA p S f (b₀ + 1) (B :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, by
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                        exact .tail _ (.head _)⟩)) ?_
                  refine G4s.andR
                    (hant _ (Finset.mem_insert_self _ _)
                      (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hgmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
          · -- principal on the p-free side
            have hABp := hΔ _ hδ
            have hAp : p ∉ A.somehow.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hABp
              tauto
            have hBp : p ∉ B.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hABp
              tauto
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem (hΔS _ hδ)
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
            rcases Finset.mem_union.mp hX with hXγ | hXδ
            · -- witness on the quantified side
              have hXγl := List.mem_toFinset.mp hXγ
              have hXS := hPC.box_mem (hΓS _ hXγl)
              by_cases hXΓ : X ∈ Γ
              · -- witness body present: premise 1 absorbs at full
                -- fuel; the cut-in ◯A self-witnesses
                have dabs₁ := d₁
                rw [ctx_absorb hXΓ] at dabs₁
                have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ Δ
                  A.somehow hm dabs₁ hΔ hΓS hΔS hboxAS).1 hAp
                have hfire : ∀ {T : PLLFormula},
                    G4s (insert B (insert A.somehow
                      (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ))) T →
                    G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) T := by
                  intro T hT
                  refine G4s.cut_adm ih₁ ?_
                  refine G4s.impLLaxLax
                    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                    (Finset.mem_insert_self _ _) ?_ hT
                  exact G4s.laxR (G4s_id (Finset.mem_insert_self _ _))
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
              · -- fresh witness body: the opening conjunct, projected
                -- at the folded level and cut in
                have hgate : ¬ (X ∈ Γ ∨ X ∉ S) := by
                  push_neg
                  exact ⟨hXΓ, hXS⟩
                have dγ₁ := d₁
                rw [ctx_cons] at dγ₁
                have ih₁ := (IH m (Nat.lt_succ_self m) f (X :: Γ) Δ
                  A.somehow hmf dγ₁ hΔ (memS_cons hXS hΓS) hΔS hboxAS).1 hAp
                have hop : G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ)
                    ((itpE p S f (b₀ + 1) (X :: Γ)).somehow) := by
                  rw [itpE_succ]
                  refine andAll_project ?_
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨X.somehow, hXγl, ?_⟩))
                  simp only
                  rw [if_neg hgate]
                  exact .head _
                have hfire : ∀ {T : PLLFormula},
                    G4s (insert B (insert ((itpE p S f (b₀ + 1)
                      (X :: Γ)).somehow)
                      (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ))) T →
                    G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) T := by
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
              have hXS := hPC.box_mem (hΔS _ hXδ)
              have dδ₁ := d₁
              rw [ctx_delta] at dδ₁
              have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ (insert X Δ)
                A.somehow hm dδ₁ (pfree_insert hXp hΔ) hΓS
                (memS_insert hXS hΔS) hboxAS).1 hAp
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

/-- The file itself is sorry-free; the `sorryAx` below is inherited
from `absorb_base`'s single quarantined holdout — since round 4
(PROGRESS §60) that is `cascade_boxgoal_pos`, the `◯`-goal descent,
feeding `itp_stab` — and disappears when that lands. -/
theorem itp_adequate_axiom_note : True := trivial

/--
info: 'PLLND.itp_adequate' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms itp_adequate

/-- Smoke instantiation: the space/threshold hypotheses are jointly
satisfiable on a nonempty space (statement-level sanity, not part of
the tower). -/
example : G4s {itpE "p" {prop "q"} 1 19 [prop "q"]}
    (itpA "p" {prop "q"} 1 19 [prop "q"] (prop "q")) := by
  have hPC : PieceClosed ({prop "q"} : Finset PLLFormula) := by
    constructor <;>
      (intros; rename_i h; exact absurd (Finset.mem_singleton.mp h) (by simp))
  have hB : kcap {prop "q"} < 19 := by
    simp [kcap]
  have d : G4sh 0 (([(prop "q" : PLLFormula)]).toFinset ∪ ∅) (prop "q") :=
    .init (by simp)
  have hres := (itp_adequate "p" {prop "q"} hPC hB 0 1 [prop "q"] ∅
    (prop "q") Nat.one_pos d (by simp) (by simp) (by simp) (by simp)).2
  simpa using hres


/-! ### Box-free adequacy tier (mechanical clone of `itp_adequate`)

`stab_lower_bf`/`itp_adequate_bf` mirror `stab_lower`/`itp_adequate`
but route the budget-lowering step through `itp_stab_bf` (sorry-free)
under the added `∀ F ∈ S, boxFree F` side condition.  The four
`stab_lower` sites in `itp_adequate` all lower at the ambient context
`Γ` with a goal whose `∈ S` witness is already in scope; the box-free
clone forwards those plus `hSbf`. -/

/-- Box-free budget lowering: `stab_lower` via `itp_stab_bf`. -/
private theorem stab_lower_bf {p : String} {S : Finset PLLFormula}
    (hPC : PieceClosed S) (hSbf : ∀ F ∈ S, boxFree F)
    {b₀ : Nat} (hB : kcap S < b₀ + 1) {f : Nat} {Γ : List PLLFormula}
    {C : PLLFormula} {Θ : Finset PLLFormula}
    (hΓS : ∀ F ∈ Γ, F ∈ S) (hCS : C ∈ S)
    (hE : itpE p S f (b₀ + 1) Γ ∈ Θ)
    (hA : G4s Θ (itpA p S f (b₀ + 1) Γ C)) :
    G4s Θ (itpA p S f b₀ Γ C) := by
  refine G4s.cut_adm hA (of_G4c2
    ((itp_stab_bf p S hSbf hPC.and_mem hPC.or_mem hPC.imp_mem
        hPC.impAnd_mem hPC.impOr_mem hPC.impImp_mem f (b₀ + 1) hB).2
      Γ C hΓS hCS)
    (Finset.mem_insert_of_mem hE) (Finset.mem_insert_self _ _))

theorem itp_adequate_bf (p : String) (S : Finset PLLFormula)
    (hPC : PieceClosed S) (hSbf : ∀ F ∈ S, boxFree F)
    {B : Nat} (hB : kcap S < B) :
    ∀ (n : Nat), ∀ (fuel : Nat) (Γ : List PLLFormula)
      (Δ : Finset PLLFormula) (C : PLLFormula),
    n < fuel → G4sh n (Γ.toFinset ∪ Δ) C →
    (∀ ψ ∈ Δ, p ∉ ψ.atoms) →
    (∀ F ∈ Γ, F ∈ S) → (∀ ψ ∈ Δ, ψ ∈ S) → C ∈ S →
    ((p ∉ C.atoms → G4s (insert (itpE p S fuel B Γ) Δ) C)
      ∧ G4s (insert (itpE p S fuel B Γ) Δ) (itpA p S fuel B Γ C)) := by
  obtain ⟨b₀, rfl⟩ : ∃ b₀, B = b₀ + 1 :=
    ⟨B - 1, by have := kcap_ge (S := S); omega⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro fuel Γ Δ C hfuel d hΔ hΓS hΔS hCS
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
              rw [itpE_succ]
              refine G4s.andAll_elim ?_
                (G4s.init (Finset.mem_insert_self _ _))
              refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inr (List.mem_filterMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))))
              simp only
              rw [if_neg ha]
            · by_cases ha : a = p
              · subst ha
                rw [itpA_succ]
                refine G4s.orAll_intro ?_ (G4s.truePLL_intro _)
                simp only [itpAfull, itpAoth]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨prop a, List.mem_toFinset.mp hγ, ?_⟩))
                simp
              · rw [itpA_succ]
                refine G4s.orAll_intro (φ := prop a)
                  (by simp only [itpAfull, itpAoth, itpAgoal]
                      refine List.mem_append.mpr (Or.inl ?_)
                      rw [if_neg (fun hc => ha hc)]
                      exact .head _) ?_
                rw [itpE_succ]
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
            · rw [itpA_succ]
              refine G4s.orAll_intro (φ := prop a)
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_neg hap]
                    exact .head _) ?_
              exact G4s.init (Finset.mem_insert_of_mem hδ)
  | @botL _ _ _ h =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hexp : ∀ (D : PLLFormula),
                G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) D := by
              intro D
              rw [itpE_succ]
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
      obtain ⟨hAS, hBS⟩ := hPC.and_mem hCS
      have ih₁ := IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS
      have ih₂ := IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₂ hΔ hΓS hΔS hBS
      constructor
      · intro hCp
        rw [atoms_and, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.andR (ih₁.1 hCp.1) (ih₂.1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have jh₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ hΓS hΔS hAS
            have jh₂ := IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₂ hΔ hΓS hΔS hBS
            rw [itpA_succ]
            refine G4s.orAll_intro
              (φ := (itpA p S f (b₀ + 1) Γ A).and (itpA p S f (b₀ + 1) Γ B))
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_lift (G4s.andR jh₁.2 jh₂.2)
  | @orR1 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.or_mem hCS
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR1
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS).1 hCp.1)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            rw [itpA_succ]
            refine G4s.orAll_intro (φ := itpA p S f (b₀ + 1) Γ A)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.head _))) ?_
            exact E_lift
              (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ hΓS hΔS hAS).2
  | @orR2 m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.or_mem hCS
      constructor
      · intro hCp
        rw [atoms_or, Finset.mem_union] at hCp
        push_neg at hCp
        exact G4s.orR2
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ B hm d₁ hΔ hΓS hΔS hBS).1 hCp.2)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            rw [itpA_succ]
            refine G4s.orAll_intro (φ := itpA p S f (b₀ + 1) Γ B)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))) ?_
            exact E_lift
              (IH m (Nat.lt_succ_self m) f Γ Δ B hmf d₁ hΔ hΓS hΔS hBS).2
  | @impR m _ A B d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      obtain ⟨hAS, hBS⟩ := hPC.imp_mem hCS
      constructor
      · intro hCp
        rw [atoms_ifThen, Finset.mem_union] at hCp
        push_neg at hCp
        have dδ := d₁
        rw [ctx_delta] at dδ
        have hres := (IH m (Nat.lt_succ_self m) fuel Γ (insert A Δ) B hm dδ
          (pfree_insert hCp.1 hΔ) hΓS (memS_insert hAS hΔS) hBS).1 hCp.2
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
            have hres := (IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B hmf dγ hΔ
              (memS_cons hAS hΓS) hΔS hBS).2
            rw [itpA_succ]
            by_cases hAΓ : A ∈ Γ
            · -- same-set antecedent: budget-gated guard, body at full
              -- budget; land through the ambient via set-congruence
              refine G4s.orAll_intro
                (φ := (itpE p S f b₀ (A :: Γ)).ifThen
                  (itpA p S f (b₀ + 1) (A :: Γ) B))
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_pos hAΓ]
                    exact .head _) ?_
              refine G4s.impR ?_
              have hset : Γ.toFinset = (A :: Γ).toFinset := by
                rw [List.toFinset_cons,
                  Finset.insert_eq_self.mpr (List.mem_toFinset.mpr hAΓ)]
              refine E_cut hset
                (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                (fun y hy => Finset.mem_insert_of_mem
                  (Finset.mem_insert_of_mem hy)) hres
            · refine G4s.orAll_intro
                (φ := (itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                  (itpA p S f (b₀ + 1) (A :: Γ) B))
                (by simp only [itpAfull, itpAoth, itpAgoal]
                    refine List.mem_append.mpr (Or.inl ?_)
                    rw [if_neg hAΓ]
                    exact .head _) ?_
              refine G4s.impR ?_
              exact hres.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
  | @laxR m _ A d₁ =>
      have hm : m < fuel := Nat.lt_of_succ_lt hfuel
      have hAS := hPC.box_mem hCS
      constructor
      · intro hCp
        rw [atoms_somehow] at hCp
        exact G4s.laxR
          ((IH m (Nat.lt_succ_self m) fuel Γ Δ A hm d₁ hΔ hΓS hΔS hAS).1 hCp)
      · cases fuel with
        | zero => exact absurd hfuel (Nat.not_lt_zero _)
        | succ f =>
            have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
            have hres := (IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
              hΓS hΔS hAS).2
            rw [itpA_succ]
            refine G4s.orAll_intro
              (φ := ((itpE p S f b₀ Γ).ifThen
                (itpA p S f (b₀ + 1) Γ A)).somehow)
              (by simp only [itpAfull, itpAoth, itpAgoal]
                  exact List.mem_append.mpr (Or.inl
                    (List.mem_append.mpr (Or.inl (.head _))))) ?_
            refine G4s.laxR (G4s.impR ?_)
            exact E_cut rfl
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              (fun y hy => Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem hy)) hres
  | @laxL m _ A B h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · -- witness box on the quantified side
            have hγl := List.mem_toFinset.mp hγ
            have hAS := hPC.box_mem (hΓS _ hγl)
            by_cases hAΓ : A ∈ Γ
            · -- body already present: same-set skip
              have dabs := d₁
              rw [ctx_absorb hAΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ B.somehow
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hgate : ¬ (A ∈ Γ ∨ A ∉ S) := by
                push_neg
                exact ⟨hAΓ, hAS⟩
              have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ B.somehow
                hmf dγ hΔ (memS_cons hAS hΓS) hΔS hCS
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim
                  (φ := (itpE p S f (b₀ + 1) (A :: Γ)).somehow) ?_ ?_
                · refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow, hγl, ?_⟩))
                  simp only
                  rw [if_neg hgate]
                  exact .head _
                · refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                  exact (ihp.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · rw [itpA_succ]
                refine G4s.orAll_intro
                  (φ := ((itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                    (itpA p S f (b₀ + 1) (A :: Γ) B.somehow)).somehow)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.somehow, hγl, by
                      simp only
                      rw [if_neg hgate]
                      exact .head _⟩)) ?_
                refine G4s.laxR (G4s.impR ?_)
                exact ihp.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
          · -- witness box on the p-free side: land the truncation
            -- disjunct through the IH's own disjunction
            have hAp : p ∉ A.atoms := by
              have := hΔ _ hδ
              rwa [atoms_somehow] at this
            have hAS := hPC.box_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hΔ' := pfree_insert hAp hΔ
            have hΔS' := memS_insert hAS hΔS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert A Δ)
              B.somehow hm dδ hΔ' hΓS hΔS' hCS
            constructor
            · intro hCp
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              exact (ihp.1 hCp).weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
            · have hne : itpAoth p S f (b₀ + 1) Γ (B.somehow) ≠ [] := by
                simp [itpAoth, itpAgoal]
              have heq : itpAfull p S f (b₀ + 1) Γ (B.somehow)
                  = itpAoth p S f (b₀ + 1) Γ (B.somehow) ++
                    [((itpE p S f b₀ Γ).ifThen
                      (orAll (itpAoth p S f (b₀ + 1) Γ (B.somehow)))).somehow] := by
                simp only [itpAfull]
                rw [if_neg (by simpa [List.isEmpty_iff] using hne)]
              rw [itpA_succ, heq]
              refine G4s.orAll_intro
                (φ := ((itpE p S f b₀ Γ).ifThen
                  (orAll (itpAoth p S f (b₀ + 1) Γ (B.somehow)))).somehow)
                (List.mem_append.mpr (Or.inr (.head _))) ?_
              refine G4s.laxL (Finset.mem_insert_of_mem hδ) ?_
              have hcut : G4s (insert A (insert
                  (itpE p S (f + 1) (b₀ + 1) Γ) Δ))
                  (itpA p S (f + 1) (b₀ + 1) Γ B.somehow) :=
                ihp.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              refine G4s.cut_adm hcut ?_
              rw [itpA_succ, heq]
              refine G4s.orAll_elim ?_
              intro φ hφ
              rcases List.mem_append.mp hφ with hoth | htr
              · -- an `others`-disjunct re-enters under the guard
                refine G4s.laxR (G4s.impR ?_)
                exact G4s.orAll_intro hoth
                  (G4s_id (Finset.mem_insert_of_mem
                    (Finset.mem_insert_self _ _)))
              · -- the truncation disjunct is the goal: identity
                have := List.mem_singleton.mp htr
                subst this
                exact G4s_id (Finset.mem_insert_self _ _)
  | @andL m _ A B _ h d₁ =>
      cases fuel with
      | zero => exact absurd hfuel (Nat.not_lt_zero _)
      | succ f =>
          have hmf : m < f := Nat.lt_of_succ_lt_succ hfuel
          rcases Finset.mem_union.mp h with hγ | hδ
          · have hγl := List.mem_toFinset.mp hγ
            obtain ⟨hAS, hBS⟩ := hPC.and_mem (hΓS _ hγl)
            by_cases hpres : A ∈ Γ ∧ B ∈ Γ
            · -- both pieces present: same-set skip via the premise IH
              have dabs := d₁
              rw [ctx_absorb hpres.2, ctx_absorb hpres.1] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) :=
                ⟨Or.inr hAS, Or.inr hBS⟩
              have dγ := d₁
              rw [ctx_cons₂] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (A :: B :: Γ) Δ C
                hmf dγ hΔ (memS_cons₂ hAS hBS hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1) (A :: B :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.and B, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1) (A :: B :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.and B, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hABp := hΔ _ hδ
            rw [atoms_and, Finset.mem_union] at hABp
            push_neg at hABp
            obtain ⟨hAS, hBS⟩ := hPC.and_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert A (insert B Δ)) C hm dδ
              (pfree_insert hABp.1 (pfree_insert hABp.2 hΔ)) hΓS
              (memS_insert hAS (memS_insert hBS hΔS)) hCS
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
            obtain ⟨hAS, hBS⟩ := hPC.or_mem (hΓS _ hγl)
            by_cases hpres : A ∈ Γ ∨ B ∈ Γ
            · -- a branch piece is present: that premise IH concludes
              rcases hpres with hA | hB
              · have dabs := d₁
                rw [ctx_absorb hA] at dabs
                exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                  (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
              · have dabs := d₂
                rw [ctx_absorb hB] at dabs
                exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                  (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : A ∈ S ∧ B ∈ S := ⟨hAS, hBS⟩
              have dγ₁ := d₁
              rw [ctx_cons] at dγ₁
              have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₁ := IH m (Nat.lt_succ_self m) f (A :: Γ) Δ C hmf dγ₁
                hΔ (memS_cons hAS hΓS) hΔS hCS
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ₂
                hΔ (memS_cons hBS hΓS) hΔS hCS
              have hEmem : (itpE p S f (b₀ + 1) (A :: Γ)).or
                  (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.or B, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim hEmem ?_
                refine G4s.orL (Finset.mem_insert_self _ _) ?_ ?_
                · exact (ih₁.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · rw [itpA_succ]
                refine G4s.orAll_intro
                  (φ := ((itpE p S f (b₀ + 1) (A :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (A :: Γ) C)).and
                    ((itpE p S f (b₀ + 1) (B :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B :: Γ) C)))
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.or B, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
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
            obtain ⟨hAS, hBS⟩ := hPC.or_mem (hΔS _ hδ)
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert A Δ) C
              hm dδ₁ (pfree_insert hABp.1 hΔ) hΓS (memS_insert hAS hΔS) hCS
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hABp.2 hΔ) hΓS (memS_insert hBS hΔS) hCS
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
            have hBS := (hPC.imp_mem (hΓS _ hγl)).2
            by_cases hBΓ : B ∈ Γ
            · -- consequent already present: same-set skip
              have dabs := d₁
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf dγ
                hΔ (memS_cons hBS hΓS) hΔS hCS
              by_cases haΓ : PLLFormula.prop a ∈ Γ
              · -- guarded clause: bare recursion
                have hEmem : itpE p S f (b₀ + 1) (B :: Γ) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(prop a).ifThen B, hγl, ?_⟩))
                  simp only
                  rw [if_neg hBΓ, if_pos hBS, if_pos haΓ]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  exact G4s.andAll_elim hEmem (ihp.1 hCp)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := itpA p S f (b₀ + 1) (B :: Γ) C)
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, by
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos haΓ]
                        exact .head _⟩)) ?_
                  exact G4s.andAll_elim hEmem ihp.2
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
                · -- unguarded clause: the atom sits on the p-free side
                  have haδ : PLLFormula.prop a ∈ Δ := by
                    rcases Finset.mem_union.mp ha with haγ | haδ
                    · exact absurd (List.mem_toFinset.mp haγ) haΓ
                    · exact haδ
                  have hEmem : (prop a).ifThen (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨(prop a).ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS, if_neg haΓ, if_neg hap]
                    exact .head _
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hEmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (G4s.init (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem haδ))) ?_
                    exact (ihp.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (prop a).and (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨(prop a).ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg haΓ, if_neg hap]
                          exact .head _⟩)) ?_
                    refine G4s.andR (G4s.init (Finset.mem_insert_of_mem haδ)) ?_
                    refine G4s.andAll_elim_keep hEmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
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
            have hBS := (hPC.imp_mem (hΔS _ hδ)).2
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
            rcases Finset.mem_union.mp ha with haγ | haδ
            · -- the atom lives on the quantified side: expose E1
              have haγl := List.mem_toFinset.mp haγ
              have hamem : prop a ∈ itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_filterMap.mpr ⟨prop a, haγl, ?_⟩))))
                simp only
                rw [if_neg hap]
              constructor
              · intro hCp
                rw [itpE_succ]
                have hres := ihp.1 hCp
                rw [itpE_succ] at hres
                refine G4s.andAll_elim_keep hamem ?_
                refine G4s.impLProp
                  (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                  (Finset.mem_insert_self _ _) ?_
                exact hres.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · rw [itpE_succ]
                have hres := ihp.2
                rw [itpE_succ] at hres
                refine G4s.andAll_elim_keep hamem ?_
                refine G4s.impLProp
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
            have hPS := hPC.impAnd_mem (hΓS _ hγl)
            by_cases hPΓ : A.ifThen (B.ifThen D₀) ∈ Γ
            · have dabs := d₁
              rw [ctx_absorb hPΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ := d₁
              rw [ctx_cons] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f
                (A.ifThen (B.ifThen D₀) :: Γ) Δ C hmf dγ hΔ
                (memS_cons hPS hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1)
                  (A.ifThen (B.ifThen D₀) :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.and B).ifThen D₀, hγl, ?_⟩))
                simp only
                rw [if_neg hPΓ, if_pos hPS]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1)
                    (A.ifThen (B.ifThen D₀) :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨(A.and B).ifThen D₀, hγl, by
                      simp only
                      rw [if_neg hPΓ, if_pos hPS]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hFp := hΔ _ hδ
            have hPp : p ∉ (A.ifThen (B.ifThen D₀)).atoms := by
              simp only [atoms_ifThen, atoms_and, Finset.mem_union] at hFp ⊢
              tauto
            have hPS := hPC.impAnd_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen (B.ifThen D₀)) Δ) C hm dδ
              (pfree_insert hPp hΔ) hΓS (memS_insert hPS hΔS) hCS
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
            obtain ⟨hP₁S, hP₂S⟩ := hPC.impOr_mem (hΓS _ hγl)
            by_cases hpres : A.ifThen D₀ ∈ Γ ∧ B.ifThen D₀ ∈ Γ
            · have dabs := d₁
              rw [ctx_absorb hpres.2, ctx_absorb hpres.1] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have hguard : (A.ifThen D₀ ∈ Γ ∨ A.ifThen D₀ ∈ S) ∧
                  (B.ifThen D₀ ∈ Γ ∨ B.ifThen D₀ ∈ S) :=
                ⟨Or.inr hP₁S, Or.inr hP₂S⟩
              have dγ := d₁
              rw [ctx_cons₂] at dγ
              have ihp := IH m (Nat.lt_succ_self m) f
                (A.ifThen D₀ :: B.ifThen D₀ :: Γ) Δ C hmf dγ hΔ
                (memS_cons₂ hP₁S hP₂S hΓS) hΔS hCS
              have hEmem : itpE p S f (b₀ + 1)
                  (A.ifThen D₀ :: B.ifThen D₀ :: Γ) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨(A.or B).ifThen D₀, hγl, ?_⟩))
                simp only
                rw [if_neg hpres, if_pos hguard]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                exact G4s.andAll_elim hEmem (ihp.1 hCp)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := itpA p S f (b₀ + 1)
                    (A.ifThen D₀ :: B.ifThen D₀ :: Γ) C)
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨(A.or B).ifThen D₀, hγl, by
                      simp only
                      rw [if_neg hpres, if_pos hguard]
                      exact .head _⟩)) ?_
                exact G4s.andAll_elim hEmem ihp.2
          · have hFp := hΔ _ hδ
            have hP₁ : p ∉ (A.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            have hP₂ : p ∉ (B.ifThen D₀).atoms := by
              simp only [atoms_ifThen, atoms_or, Finset.mem_union] at hFp ⊢
              tauto
            obtain ⟨hP₁S, hP₂S⟩ := hPC.impOr_mem (hΔS _ hδ)
            have dδ := d₁
            rw [ctx_delta, ctx_delta] at dδ
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have ihp := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (A.ifThen D₀) (insert (B.ifThen D₀) Δ)) C hm dδ
              (pfree_insert hP₁ (pfree_insert hP₂ hΔ)) hΓS
              (memS_insert hP₁S (memS_insert hP₂S hΔS)) hCS
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
          · have hγl := List.mem_toFinset.mp hγ
            have hprinS := hΓS _ hγl
            obtain ⟨hABS, hDS⟩ := hPC.imp_mem hprinS
            have hPS := hPC.impImp_mem hprinS
            by_cases hDΓ : D₀ ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hDΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₂ := IH m (Nat.lt_succ_self m) f (D₀ :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hDS hΓS) hΔS hCS
              by_cases hBDΓ : B.ifThen D₀ ∈ Γ
              · -- present piece: the jump clause, components at b₀,
                -- fed by absorption under the ambient E
                have dabs₁ := d₁
                rw [ctx_absorb hBDΓ] at dabs₁
                have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ (A.ifThen B)
                  hmf dabs₁ hΔ hΓS hΔS hABS
                have hguard : ∀ (Θ : Finset PLLFormula),
                    itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                    G4s Θ ((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ (A.ifThen B))) := by
                  intro Θ hamb hΘ
                  refine G4s.impR ?_
                  refine G4s.cut_adm
                    (E_feed rfl (Finset.mem_insert_of_mem hamb)) ?_
                  refine stab_lower_bf hPC hSbf hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    · exact Or.inr (Or.inr (hΘ hy)))
                have hEmem : ((itpE p S f b₀ Γ).ifThen
                    (itpA p S f b₀ Γ (A.ifThen B))).ifThen
                      (itpE p S f (b₀ + 1) (D₀ :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A.ifThen B).ifThen D₀, hγl, ?_⟩))
                  simp only
                  rw [if_neg hDΓ, if_pos hDS, if_pos hBDΓ, if_pos hprinS]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := ((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ (A.ifThen B))).and
                        (itpA p S f (b₀ + 1) (D₀ :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(A.ifThen B).ifThen D₀, hγl, by
                        simp only
                        rw [if_neg hDΓ, if_pos hDS, if_pos hBDΓ,
                          if_pos hprinS]
                        exact .head _⟩)) ?_
                  refine G4s.andR
                    (hguard _ (Finset.mem_insert_self _ _)
                      (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · -- fresh piece: the reset clause at full budget
                have dγ₁ := d₁
                rw [ctx_cons] at dγ₁
                have ih₁ := IH m (Nat.lt_succ_self m) f
                  (B.ifThen D₀ :: Γ) Δ (A.ifThen B) hmf dγ₁ hΔ
                  (memS_cons hPS hΓS) hΔS hABS
                have hguard : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                    G4s Θ ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                        (A.ifThen B))) := by
                  intro Θ hΘ
                  refine G4s.impR ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    · exact Or.inr (hΘ hy))
                have hEmem : ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                    (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                      (A.ifThen B))).ifThen
                      (itpE p S f (b₀ + 1) (D₀ :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A.ifThen B).ifThen D₀, hγl, ?_⟩))
                  simp only
                  rw [if_neg hDΓ, if_pos hDS, if_neg hBDΓ, if_pos hPS]
                  exact .head _
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := ((itpE p S f (b₀ + 1) (B.ifThen D₀ :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (B.ifThen D₀ :: Γ)
                        (A.ifThen B))).and
                          (itpA p S f (b₀ + 1) (D₀ :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨(A.ifThen B).ifThen D₀, hγl, by
                        simp only
                        rw [if_neg hDΓ, if_pos hDS, if_neg hBDΓ, if_pos hPS]
                        exact .head _⟩)) ?_
                  refine G4s.andR (hguard _ (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hEmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hguard _ (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
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
            have hprinS := hΔS _ hδ
            obtain ⟨hABS, hDS⟩ := hPC.imp_mem hprinS
            have hPS := hPC.impImp_mem hprinS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₁ := d₁
            rw [ctx_delta] at dδ₁
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert (B.ifThen D₀) Δ) (A.ifThen B) hm dδ₁
              (pfree_insert hBDp hΔ) hΓS (memS_insert hPS hΔS) hABS).1 hABp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ
              (insert D₀ Δ) C hm dδ₂ (pfree_insert hDp hΔ) hΓS
              (memS_insert hDS hΔS) hCS
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
            have hprinS := hΓS _ hγl
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            have hAS := hPC.box_mem hboxAS
            by_cases hBΓ : B ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ A hmf d₁ hΔ
                hΓS hΔS hAS
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hBS hΓS) hΔS hCS
              -- premise 1's ∀-interpolant, absorbed into the b₀ slot
              have hant : ∀ (Θ : Finset PLLFormula),
                  itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                  G4s Θ (itpA p S f b₀ Γ A) := by
                intro Θ hamb hΘ
                refine G4s.cut_adm (E_feed rfl hamb) ?_
                refine stab_lower_bf hPC hSbf hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                exact ih₁.2.weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  rcases hy with rfl | hy
                  · exact Or.inl rfl
                  · exact Or.inr (hΘ hy))
              have hEmem : (itpA p S f b₀ Γ A).ifThen
                  (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                  itpEcls p S f (b₀ + 1) Γ := by
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨A.somehow.ifThen B, hγl, ?_⟩))
                simp only
                rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                exact .head _
              constructor
              · intro hCp
                rw [itpE_succ]
                refine G4s.andAll_elim_keep hEmem ?_
                refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant _ (Finset.mem_insert_of_mem
                      (Finset.mem_insert_self _ _))
                    (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
                exact (ih₂.1 hCp).weaken_subset (by
                  intro y hy
                  simp only [Finset.mem_insert] at hy ⊢
                  tauto)
              · rw [itpA_succ, itpE_succ]
                refine G4s.orAll_intro
                  (φ := (itpA p S f b₀ Γ A).and
                    (itpA p S f (b₀ + 1) (B :: Γ) C))
                  (mem_full_of_env (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, by
                      simp only
                      rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                      exact .head _⟩)) ?_
                refine G4s.andR
                  (hant _ (Finset.mem_insert_self _ _)
                    (Finset.subset_insert _ _)) ?_
                refine G4s.andAll_elim_keep hEmem ?_
                refine G4s.mp_adm (Finset.mem_insert_self _ _)
                  (hant _ (Finset.mem_insert_of_mem
                      (Finset.mem_insert_self _ _))
                    (fun y hy => Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hy))) ?_
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
            have hprinS := hΔS _ hδ
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            have hAS := hPC.box_mem hboxAS
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ Δ A hm d₁ hΔ
              hΓS hΔS hAS).1 hAp
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
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
            have hprinS := hΓS _ hγl
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem hprinS
            by_cases hBΓ : B ∈ Γ
            · -- consequent present: same-set skip via premise 2
              have dabs := d₂
              rw [ctx_absorb hBΓ] at dabs
              exact IH m (Nat.lt_succ_self m) (f + 1) Γ Δ C
                (Nat.lt_of_succ_lt hfuel) dabs hΔ hΓS hΔS hCS
            · have dγ₂ := d₂
              rw [ctx_cons] at dγ₂
              have ih₂ := IH m (Nat.lt_succ_self m) f (B :: Γ) Δ C hmf
                dγ₂ hΔ (memS_cons hBS hΓS) hΔS hCS
              rcases Finset.mem_union.mp hX with hXγ | hXδ
              · -- witness also on the quantified side
                have hXγl := List.mem_toFinset.mp hXγ
                have hXS := hPC.box_mem (hΓS _ hXγl)
                by_cases hXΓ : X ∈ Γ
                · -- witness body present: γ-clause fed by absorption
                  have dabs₁ := d₁
                  rw [ctx_absorb hXΓ] at dabs₁
                  have ih₁ := IH m (Nat.lt_succ_self m) f Γ Δ A.somehow
                    hmf dabs₁ hΔ hΓS hΔS hboxAS
                  have hant : ∀ (Θ : Finset PLLFormula),
                      itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                      G4s Θ (((itpE p S f b₀ Γ).ifThen
                        (itpA p S f b₀ Γ A.somehow)).somehow) := by
                    intro Θ hamb hΘ
                    refine G4s.laxR (G4s.impR ?_)
                    refine G4s.cut_adm
                      (E_feed rfl (Finset.mem_insert_of_mem hamb)) ?_
                    refine stab_lower_bf hPC hSbf hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                    exact ih₁.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      rcases hy with rfl | hy
                      · exact Or.inl rfl
                      · exact Or.inr (Or.inr (hΘ hy)))
                  have hgmem : (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow).ifThen
                        (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                    exact .tail _ (.head _)
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (Finset.mem_insert_of_mem
                          (Finset.mem_insert_self _ _))
                        (fun y hy => Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem hy))) ?_
                    exact (ih₂.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (((itpE p S f b₀ Γ).ifThen
                        (itpA p S f b₀ Γ A.somehow)).somehow).and
                          (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨A.somehow.ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                          exact .tail _ (.head _)⟩)) ?_
                    refine G4s.andR
                      (hant _ (Finset.mem_insert_self _ _)
                        (Finset.subset_insert _ _)) ?_
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (Finset.mem_insert_of_mem
                          (Finset.mem_insert_self _ _))
                        (fun y hy => Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem hy))) ?_
                    exact ih₂.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                · -- fresh witness body: the per-witness clause
                  have hgate : ¬ (X ∈ Γ ∨ X ∉ S) := by
                    push_neg
                    exact ⟨hXΓ, hXS⟩
                  have dγ₁ := d₁
                  rw [ctx_cons] at dγ₁
                  have ih₁ := IH m (Nat.lt_succ_self m) f (X :: Γ) Δ
                    A.somehow hmf dγ₁ hΔ (memS_cons hXS hΓS) hΔS hboxAS
                  have hant : ∀ (Θ : Finset PLLFormula), Δ ⊆ Θ →
                      G4s Θ (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                        (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow) := by
                    intro Θ hΘ
                    refine G4s.laxR (G4s.impR ?_)
                    exact ih₁.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      rcases hy with rfl | hy
                      · exact Or.inl rfl
                      · exact Or.inr (hΘ hy))
                  have hgmem : (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                      (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow).ifThen
                        (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                      itpEcls p S f (b₀ + 1) Γ := by
                    refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, ?_⟩))
                    simp only
                    rw [if_neg hBΓ, if_pos hBS]
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_filterMap.mpr ⟨X.somehow, hXγl, ?_⟩))
                    simp only
                    rw [if_neg hgate]
                  constructor
                  · intro hCp
                    rw [itpE_succ]
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                    exact (ih₂.1 hCp).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · rw [itpA_succ, itpE_succ]
                    refine G4s.orAll_intro
                      (φ := (((itpE p S f (b₀ + 1) (X :: Γ)).ifThen
                        (itpA p S f (b₀ + 1) (X :: Γ) A.somehow)).somehow).and
                          (itpA p S f (b₀ + 1) (B :: Γ) C))
                      (mem_full_of_env (List.mem_flatMap.mpr
                        ⟨A.somehow.ifThen B, hγl, by
                          simp only
                          rw [if_neg hBΓ, if_pos hBS]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_filterMap.mpr ⟨X.somehow, hXγl, ?_⟩))
                          simp only
                          rw [if_neg hgate]⟩)) ?_
                    refine G4s.andR
                      (hant _ (Finset.subset_insert _ _)) ?_
                    refine G4s.andAll_elim_keep hgmem ?_
                    refine G4s.mp_adm (Finset.mem_insert_self _ _)
                      (hant _ (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                    exact ih₂.2.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
              · -- witness on the p-free side: γ-clause after laxL
                have hXp : p ∉ X.atoms := by
                  have := hΔ _ hXδ
                  rwa [atoms_somehow] at this
                have hXS := hPC.box_mem (hΔS _ hXδ)
                have dδ₁ := d₁
                rw [ctx_delta] at dδ₁
                have ih₁ := IH m (Nat.lt_succ_self m) f Γ (insert X Δ)
                  A.somehow hmf dδ₁ (pfree_insert hXp hΔ) hΓS
                  (memS_insert hXS hΔS) hboxAS
                have hant : ∀ (Θ : Finset PLLFormula),
                    itpE p S (f + 1) (b₀ + 1) Γ ∈ Θ → Δ ⊆ Θ →
                    G4s Θ (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow) := by
                  intro Θ hamb hΘ
                  refine G4s.laxL (hΘ hXδ) ?_
                  refine G4s.laxR (G4s.impR ?_)
                  refine G4s.cut_adm
                    (E_feed rfl (Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem hamb))) ?_
                  refine stab_lower_bf hPC hSbf hB hΓS (by assumption) (Finset.mem_insert_self _ _) ?_
                  exact ih₁.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    rcases hy with rfl | hy
                    · exact Or.inl rfl
                    rcases hy with rfl | hy
                    · exact Or.inr (Or.inr (Or.inl rfl))
                    · exact Or.inr (Or.inr (Or.inr (hΘ hy))))
                have hgmem : (((itpE p S f b₀ Γ).ifThen
                    (itpA p S f b₀ Γ A.somehow)).somehow).ifThen
                      (itpE p S f (b₀ + 1) (B :: Γ)) ∈
                    itpEcls p S f (b₀ + 1) Γ := by
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.somehow.ifThen B, hγl, ?_⟩))
                  simp only
                  rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                  exact .tail _ (.head _)
                constructor
                · intro hCp
                  rw [itpE_succ]
                  refine G4s.andAll_elim_keep hgmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact (ih₂.1 hCp).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · rw [itpA_succ, itpE_succ]
                  refine G4s.orAll_intro
                    (φ := (((itpE p S f b₀ Γ).ifThen
                      (itpA p S f b₀ Γ A.somehow)).somehow).and
                        (itpA p S f (b₀ + 1) (B :: Γ) C))
                    (mem_full_of_env (List.mem_flatMap.mpr
                      ⟨A.somehow.ifThen B, hγl, by
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hprinS]
                        exact .tail _ (.head _)⟩)) ?_
                  refine G4s.andR
                    (hant _ (Finset.mem_insert_self _ _)
                      (Finset.subset_insert _ _)) ?_
                  refine G4s.andAll_elim_keep hgmem ?_
                  refine G4s.mp_adm (Finset.mem_insert_self _ _)
                    (hant _ (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))
                      (fun y hy => Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem hy))) ?_
                  exact ih₂.2.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
          · -- principal on the p-free side
            have hABp := hΔ _ hδ
            have hAp : p ∉ A.somehow.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hABp
              tauto
            have hBp : p ∉ B.atoms := by
              simp only [atoms_ifThen, Finset.mem_union] at hABp
              tauto
            obtain ⟨hboxAS, hBS⟩ := hPC.imp_mem (hΔS _ hδ)
            have hm : m < f + 1 := Nat.lt_of_succ_lt hfuel
            have dδ₂ := d₂
            rw [ctx_delta] at dδ₂
            have ih₂ := IH m (Nat.lt_succ_self m) (f + 1) Γ (insert B Δ) C
              hm dδ₂ (pfree_insert hBp hΔ) hΓS (memS_insert hBS hΔS) hCS
            rcases Finset.mem_union.mp hX with hXγ | hXδ
            · -- witness on the quantified side
              have hXγl := List.mem_toFinset.mp hXγ
              have hXS := hPC.box_mem (hΓS _ hXγl)
              by_cases hXΓ : X ∈ Γ
              · -- witness body present: premise 1 absorbs at full
                -- fuel; the cut-in ◯A self-witnesses
                have dabs₁ := d₁
                rw [ctx_absorb hXΓ] at dabs₁
                have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ Δ
                  A.somehow hm dabs₁ hΔ hΓS hΔS hboxAS).1 hAp
                have hfire : ∀ {T : PLLFormula},
                    G4s (insert B (insert A.somehow
                      (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ))) T →
                    G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) T := by
                  intro T hT
                  refine G4s.cut_adm ih₁ ?_
                  refine G4s.impLLaxLax
                    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hδ))
                    (Finset.mem_insert_self _ _) ?_ hT
                  exact G4s.laxR (G4s_id (Finset.mem_insert_self _ _))
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
              · -- fresh witness body: the opening conjunct, projected
                -- at the folded level and cut in
                have hgate : ¬ (X ∈ Γ ∨ X ∉ S) := by
                  push_neg
                  exact ⟨hXΓ, hXS⟩
                have dγ₁ := d₁
                rw [ctx_cons] at dγ₁
                have ih₁ := (IH m (Nat.lt_succ_self m) f (X :: Γ) Δ
                  A.somehow hmf dγ₁ hΔ (memS_cons hXS hΓS) hΔS hboxAS).1 hAp
                have hop : G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ)
                    ((itpE p S f (b₀ + 1) (X :: Γ)).somehow) := by
                  rw [itpE_succ]
                  refine andAll_project ?_
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨X.somehow, hXγl, ?_⟩))
                  simp only
                  rw [if_neg hgate]
                  exact .head _
                have hfire : ∀ {T : PLLFormula},
                    G4s (insert B (insert ((itpE p S f (b₀ + 1)
                      (X :: Γ)).somehow)
                      (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ))) T →
                    G4s (insert (itpE p S (f + 1) (b₀ + 1) Γ) Δ) T := by
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
              have hXS := hPC.box_mem (hΔS _ hXδ)
              have dδ₁ := d₁
              rw [ctx_delta] at dδ₁
              have ih₁ := (IH m (Nat.lt_succ_self m) (f + 1) Γ (insert X Δ)
                A.somehow hm dδ₁ (pfree_insert hXp hΔ) hΓS
                (memS_insert hXS hΔS) hboxAS).1 hAp
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

end PLLND
