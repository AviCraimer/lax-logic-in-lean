import LaxLogic.PLLCompleteness
import LaxLogic.PLLFinsetKit

/-!
# The finite model property (F&M Theorem 4.6)

Given any counter-model for `φ`, F&M filter it through the finite set
`Sf(φ)` of subformulas (with `⊥` always counted as a subformula): two worlds
are identified when they validate the same subformulas — `T(w)` — *and*
refute the same subformulas at all their `Rₘ`-successors — `Fₘ(w)`, the
extra ingredient needed for the ∀∃ modality.  Rather than a quotient, we
take the worlds of the filtered model to be the *realised pairs*
`(T(w), Fₘ(w))` themselves; well-definedness obligations disappear, and
finiteness is immediate since both components are subsets of `Sf(φ)`.

The main lemma `filt_force` shows forcing of subformulas is preserved and
reflected; `finite_model_property` then combines it with soundness and
completeness: `⊢ φ` iff `φ` holds in every *finite* constraint model.
-/

open PLLFormula

namespace PLLND

/-- Subformulas (reflexive). -/
def subF : PLLFormula → Finset PLLFormula
  | .prop a => {.prop a}
  | .falsePLL => {.falsePLL}
  | .and φ ψ => insert (.and φ ψ) (finUnion (subF φ) (subF ψ))
  | .or φ ψ => insert (.or φ ψ) (finUnion (subF φ) (subF ψ))
  | .ifThen φ ψ => insert (.ifThen φ ψ) (finUnion (subF φ) (subF ψ))
  | .somehow φ => insert (.somehow φ) (subF φ)

@[simp] theorem self_mem_subF (φ : PLLFormula) : φ ∈ subF φ := by
  cases φ <;> simp [subF]

/-- A set of formulas closed under immediate subformulas, containing `⊥`. -/
structure SubClosed (S : Finset PLLFormula) : Prop where
  bot : PLLFormula.falsePLL ∈ S
  and_left : ∀ {φ ψ}, PLLFormula.and φ ψ ∈ S → φ ∈ S
  and_right : ∀ {φ ψ}, PLLFormula.and φ ψ ∈ S → ψ ∈ S
  or_left : ∀ {φ ψ}, PLLFormula.or φ ψ ∈ S → φ ∈ S
  or_right : ∀ {φ ψ}, PLLFormula.or φ ψ ∈ S → ψ ∈ S
  imp_left : ∀ {φ ψ}, PLLFormula.ifThen φ ψ ∈ S → φ ∈ S
  imp_right : ∀ {φ ψ}, PLLFormula.ifThen φ ψ ∈ S → ψ ∈ S
  lax : ∀ {φ}, PLLFormula.somehow φ ∈ S → φ ∈ S

/-- Subformula membership is transitive. -/
theorem subF_trans : ∀ (χ : PLLFormula) {φ : PLLFormula},
    φ ∈ subF χ → subF φ ⊆ subF χ := by
  intro χ
  induction χ with
  | prop a =>
      intro φ h
      simp only [subF, Finset.mem_singleton] at h
      subst h
      exact subset_rfl
  | falsePLL =>
      intro φ h
      simp only [subF, Finset.mem_singleton] at h
      subst h
      exact subset_rfl
  | and α β ihα ihβ =>
      intro φ h
      simp only [subF, Finset.mem_insert, mem_finUnion] at h
      rcases h with rfl | h | h
      · exact subset_rfl
      · refine (ihα h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inl hx)
      · refine (ihβ h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inr hx)
  | or α β ihα ihβ =>
      intro φ h
      simp only [subF, Finset.mem_insert, mem_finUnion] at h
      rcases h with rfl | h | h
      · exact subset_rfl
      · refine (ihα h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inl hx)
      · refine (ihβ h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inr hx)
  | ifThen α β ihα ihβ =>
      intro φ h
      simp only [subF, Finset.mem_insert, mem_finUnion] at h
      rcases h with rfl | h | h
      · exact subset_rfl
      · refine (ihα h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inl hx)
      · refine (ihβ h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert, mem_finUnion]
        exact .inr (.inr hx)
  | somehow α ihα =>
      intro φ h
      simp only [subF, Finset.mem_insert] at h
      rcases h with rfl | h
      · exact subset_rfl
      · refine (ihα h).trans ?_
        intro x hx
        simp only [subF, Finset.mem_insert]
        exact .inr hx

/-- The closure `{⊥} ∪ subF φ` is subformula-closed. -/
theorem subClosed_insert_bot_subF (φ₀ : PLLFormula) :
    SubClosed (insert PLLFormula.falsePLL (subF φ₀)) := by
  have step : ∀ {φ ψ : PLLFormula}, ψ ∈ subF φ →
      φ ∈ insert PLLFormula.falsePLL (subF φ₀) →
      ψ ∈ insert PLLFormula.falsePLL (subF φ₀) := by
    intro φ ψ hψ hφ
    rcases Finset.mem_insert.mp hφ with rfl | hφ
    · simp only [subF, Finset.mem_singleton] at hψ
      subst hψ
      exact Finset.mem_insert_self ..
    · exact Finset.mem_insert_of_mem (subF_trans φ₀ hφ hψ)
  refine ⟨Finset.mem_insert_self .., ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ ψ h
    exact step (by simp [subF]) h
  · intro φ h
    exact step (by simp [subF]) h

variable (C : ConstraintModel) (S : Finset PLLFormula)

/-- Validated subformulas at `w`. -/
def Tset (w : C.W) : Set PLLFormula := {N | N ∈ S ∧ C.force w N}

/-- Subformulas refuted at every `Rₘ`-successor of `w` — the modal
information of the filtration. -/
def Fmset (w : C.W) : Set PLLFormula :=
  {N | N ∈ S ∧ ∀ v, C.Rm w v → ¬ C.force v N}

/-- The realised `(T, Fₘ)` pairs. -/
def FiltW : Set (Set PLLFormula × Set PLLFormula) :=
  Set.range fun w : C.W => (Tset C S w, Fmset C S w)

theorem filtW_finite : (FiltW C S).Finite := by
  have hsub : FiltW C S ⊆
      {t | t ⊆ ↑S} ×ˢ {t | t ⊆ ↑S} := by
    rintro p ⟨w, rfl⟩
    constructor
    · intro x hx; exact hx.1
    · intro x hx; exact hx.1
  exact Set.Finite.subset
    (Set.Finite.prod (Set.Finite.powerset S.finite_toSet)
      (Set.Finite.powerset S.finite_toSet)) hsub

/-- The canonical representative of `w` in the filtration. -/
def mkF (w : C.W) : ↥(FiltW C S) := ⟨(Tset C S w, Fmset C S w), ⟨w, rfl⟩⟩

/-- The filtration model (F&M Theorem 4.6). -/
def filtration : ConstraintModel where
  W := ↥(FiltW C S)
  Ri q q' := q.1.1 ⊆ q'.1.1
  Rm q q' := q.1.1 ⊆ q'.1.1 ∧ q.1.2 ⊆ q'.1.2
  F := {q | PLLFormula.falsePLL ∈ q.1.1}
  V a := {q | PLLFormula.prop a ∉ S ∨ PLLFormula.prop a ∈ q.1.1}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m _ := ⟨subset_rfl, subset_rfl⟩
  trans_m h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := by
    rcases hw with h' | h'
    · exact .inl h'
    · exact .inr (h h')
  full_F {a} {q} hq := by
    by_cases hmem : PLLFormula.prop a ∈ S
    · obtain ⟨⟨p₁, p₂⟩, w, hw⟩ := q
      injection hw with h₁ h₂
      subst h₁
      subst h₂
      right
      have hbot : PLLFormula.falsePLL ∈ Tset C S w := hq
      exact ⟨hmem, C.force_of_fallible hbot.2⟩
    · exact .inl hmem

/-- **Filtration lemma**: forcing of subformulas is preserved and
reflected. -/
theorem filt_force (hS : SubClosed S) :
    ∀ {N : PLLFormula}, N ∈ S → ∀ (w : C.W),
      C.force w N ↔ (filtration C S).force (mkF C S w) N := by
  intro N
  induction N with
  | prop a =>
      intro hmem w
      constructor
      · intro h
        exact .inr ⟨hmem, h⟩
      · rintro (h | h)
        · exact absurd hmem h
        · exact h.2
  | falsePLL =>
      intro hmem w
      constructor
      · intro h
        exact ⟨hmem, h⟩
      · intro h
        exact h.2
  | and φ ψ ihφ ihψ =>
      intro hmem w
      constructor
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ihφ (hS.and_left hmem) w).mp h₁,
          (ihψ (hS.and_right hmem) w).mp h₂⟩
      · rintro ⟨h₁, h₂⟩
        exact ⟨(ihφ (hS.and_left hmem) w).mpr h₁,
          (ihψ (hS.and_right hmem) w).mpr h₂⟩
  | or φ ψ ihφ ihψ =>
      intro hmem w
      constructor
      · rintro (h | h)
        · exact .inl ((ihφ (hS.or_left hmem) w).mp h)
        · exact .inr ((ihψ (hS.or_right hmem) w).mp h)
      · rintro (h | h)
        · exact .inl ((ihφ (hS.or_left hmem) w).mpr h)
        · exact .inr ((ihψ (hS.or_right hmem) w).mpr h)
  | ifThen φ ψ ihφ ihψ =>
      intro hmem w
      constructor
      · intro h q' hle hφ'
        obtain ⟨v, hv⟩ := q'.2
        have hq' : q' = mkF C S v := Subtype.ext hv.symm
        subst hq'
        -- membership transfer: φ ⊃ ψ ∈ T(w) ⊆ T(v)
        have himp : C.force v (φ.ifThen ψ) :=
          (hle (show φ.ifThen ψ ∈ Tset C S w from ⟨hmem, h⟩)).2
        have hφv : C.force v φ := (ihφ (hS.imp_left hmem) v).mpr hφ'
        exact (ihψ (hS.imp_right hmem) v).mp (himp v (C.refl_i v) hφv)
      · intro h v hwv hφv
        have hle : (filtration C S).Ri (mkF C S w) (mkF C S v) := by
          intro x hx
          exact ⟨hx.1, C.force_hered hwv hx.2⟩
        have hφ' := (ihφ (hS.imp_left hmem) v).mp hφv
        exact (ihψ (hS.imp_right hmem) v).mpr (h (mkF C S v) hle hφ')
  | somehow φ ih =>
      intro hmem w
      constructor
      · intro h q' hle
        obtain ⟨v, hv⟩ := q'.2
        have hq' : q' = mkF C S v := Subtype.ext hv.symm
        subst hq'
        -- membership transfer: ◯φ ∈ T(w) ⊆ T(v), so v ⊨ ◯φ
        have hv' : C.force v (φ.somehow) :=
          (hle (show φ.somehow ∈ Tset C S w from ⟨hmem, h⟩)).2
        obtain ⟨u, hvu, hu⟩ := hv' v (C.refl_i v)
        refine ⟨mkF C S u, ⟨?_, ?_⟩, (ih (hS.lax hmem) u).mp hu⟩
        · intro x hx
          exact ⟨hx.1, C.force_hered (C.sub_mi hvu) hx.2⟩
        · intro x hx
          exact ⟨hx.1, fun t hut => hx.2 t (C.trans_m hvu hut)⟩
      · intro h v hwv
        have hle : (filtration C S).Ri (mkF C S w) (mkF C S v) := by
          intro x hx
          exact ⟨hx.1, C.force_hered hwv hx.2⟩
        obtain ⟨q'', hrm, hq''⟩ := h (mkF C S v) hle
        obtain ⟨u₀, hu₀⟩ := q''.2
        have hq'' : q'' = mkF C S u₀ := Subtype.ext hu₀.symm
        subst hq''
        have hu₀φ : C.force u₀ φ := (ih (hS.lax hmem) u₀).mpr hq''
        by_contra hno
        push_neg at hno
        have hFm : φ ∈ Fmset C S v :=
          ⟨hS.lax hmem, fun t hvt hft => hno t hvt hft⟩
        have : φ ∈ Fmset C S u₀ := hrm.2 hFm
        exact this.2 u₀ (C.refl_m u₀) hu₀φ

/-- **Finite model property** (F&M Theorem 4.6): provability coincides with
validity over *finite* constraint models. -/
theorem finite_model_property {φ : PLLFormula} :
    Nonempty (LaxND [] φ) ↔
      ∀ (C : ConstraintModel), Finite C.W → ∀ w : C.W, C.force w φ := by
  constructor
  · rintro ⟨p⟩ C _ w
    exact soundness_valid p C w
  · intro h
    by_contra hn
    have hcon : ¬ ([] ⊨- φ) := fun hc => hn (completeness hc)
    unfold Consequence at hcon
    push_neg at hcon
    obtain ⟨C, w, _, hforce⟩ := hcon
    have hS := subClosed_insert_bot_subF φ
    have hmem : φ ∈ insert PLLFormula.falsePLL (subF φ) :=
      Finset.mem_insert_of_mem (self_mem_subF φ)
    have hfin : Finite (filtration C (insert PLLFormula.falsePLL (subF φ))).W :=
      (filtW_finite C _).to_subtype
    have hval := h (filtration C _) hfin (mkF C _ w)
    exact hforce ((filt_force C _ hS hmem w).mpr hval)

end PLLND
