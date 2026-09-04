import LaxLogic.PLLKripke
import LaxLogic.PLLConsequence
import Mathlib.Order.Zorn

/-!
# Completeness of PLL for Kripke constraint models

Fairtlough & Mendler, *Propositional Lax Logic*, §4 (Lemmas 4.2, 4.3,
Theorem 4.4), over the slime-free system `PLLND.LaxND`.

Worlds of the counter-model are *theories* `(Γ, Δ, Θ)`: formulas validated,
falsified, and falsified at every `Rₘ`-successor.  A theory is **consistent**
when for all finite `Ds ⊆ Δ`, `Ts ⊆ Θ` with `Ds ++ Ts ≠ []`,

  `Γ ⊬ ⋁Ds ∨ ◯(⋁Ts)`   (`disjOf Ds Ts` below).

The nonemptiness guard is essential: it makes `(all formulas, ∅, ∅)` a
consistent — and after extension, maximally consistent — theory, which is the
single fallible world of the canonical model.

Everything is `Prop`-level (sets, derivability, Zorn): no casts anywhere.
-/

open PLLFormula

namespace PLLND

/-! ### Theories and consistency -/

/-- A theory in the sense of F&M §4: `val`idated / `fal`sified /
`mfal` = falsified at every `Rₘ`-successor. -/
@[ext]
structure Theory where
  val : Set PLLFormula
  fal : Set PLLFormula
  mfal : Set PLLFormula

instance : Preorder Theory where
  le T T' := T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ T.mfal ⊆ T'.mfal
  le_refl T := ⟨subset_rfl, subset_rfl, subset_rfl⟩
  le_trans a b c h h' := ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

theorem Theory.le_def {T T' : Theory} :
    T ≤ T' ↔ T.val ⊆ T'.val ∧ T.fal ⊆ T'.fal ∧ T.mfal ⊆ T'.mfal :=
  Iff.rfl

/-- The consistency formula `⋁Ds ∨ ◯(⋁Ts)`, with the convention that an
*absent* (empty) disjunct is dropped rather than read as `⊥`. -/
def disjOf : List PLLFormula → List PLLFormula → PLLFormula
  | Ds, [] => bigOr Ds
  | [], K :: Ts => .somehow (bigOr (K :: Ts))
  | D :: Ds, K :: Ts => (bigOr (D :: Ds)).or (.somehow (bigOr (K :: Ts)))

@[simp] theorem disjOf_nil_right (Ds : List PLLFormula) :
    disjOf Ds [] = bigOr Ds := by cases Ds <;> rfl

@[simp] theorem disjOf_nil_left (K : PLLFormula) (Ts : List PLLFormula) :
    disjOf [] (K :: Ts) = .somehow (bigOr (K :: Ts)) := rfl

@[simp] theorem disjOf_cons_cons (D K : PLLFormula) (Ds Ts : List PLLFormula) :
    disjOf (D :: Ds) (K :: Ts) =
      (bigOr (D :: Ds)).or (.somehow (bigOr (K :: Ts))) := rfl

/-- Consistency (F&M §4): no nonempty finite choice from `fal` and `mfal`
has its `disjOf` derivable from `val`. -/
def Consistent (T : Theory) : Prop :=
  ∀ Ds Ts : List PLLFormula, (∀ φ ∈ Ds, φ ∈ T.fal) → (∀ φ ∈ Ts, φ ∈ T.mfal) →
    Ds ++ Ts ≠ [] → ¬ T.val ⊩ disjOf Ds Ts

theorem not_consistent_iff {T : Theory} :
    ¬ Consistent T ↔ ∃ Ds Ts : List PLLFormula,
      (∀ φ ∈ Ds, φ ∈ T.fal) ∧ (∀ φ ∈ Ts, φ ∈ T.mfal) ∧ Ds ++ Ts ≠ [] ∧
        T.val ⊩ disjOf Ds Ts := by
  unfold Consistent
  push_neg
  rfl

/-! ### Reasoning with `disjOf` -/

open SetDeriv

/-- Introduce `disjOf` from one of its `fal`-disjuncts. -/
theorem disjOf_intro_fal {Γ : Set PLLFormula} {φ : PLLFormula}
    {Ds Ts : List PLLFormula} (hmem : φ ∈ Ds) (h : Γ ⊩ φ) :
    Γ ⊩ disjOf Ds Ts := by
  cases Ts with
  | nil => simpa using bigOr_intro hmem h
  | cons K Ts =>
      cases Ds with
      | nil => cases hmem
      | cons D Ds => simpa using orL _ (bigOr_intro hmem h)

/-- Introduce `disjOf` from its modal disjunct. -/
theorem disjOf_intro_lax {Γ : Set PLLFormula} {Ds Ts : List PLLFormula}
    (hne : Ts ≠ []) (h : Γ ⊩ .somehow (bigOr Ts)) : Γ ⊩ disjOf Ds Ts := by
  cases Ts with
  | nil => exact absurd rfl hne
  | cons K Ts =>
      cases Ds with
      | nil => simpa using h
      | cons D Ds => simpa using orR _ h

/-- Eliminate `disjOf`. -/
theorem disjOf_elim {Γ : Set PLLFormula} {χ : PLLFormula}
    {Ds Ts : List PLLFormula} (h : Γ ⊩ disjOf Ds Ts)
    (hD : ∀ φ ∈ Ds, insert φ Γ ⊩ χ)
    (hT : Ts ≠ [] → insert (.somehow (bigOr Ts)) Γ ⊩ χ) : Γ ⊩ χ := by
  cases Ts with
  | nil =>
      rw [disjOf_nil_right] at h
      exact bigOr_elim h hD
  | cons K Ts =>
      cases Ds with
      | nil =>
          rw [disjOf_nil_left] at h
          exact cut h (hT (by simp))
      | cons D Ds =>
          rw [disjOf_cons_cons] at h
          refine orE h ?_ (hT (by simp))
          exact bigOr_elim (of_mem (Set.mem_insert ..))
            (fun φ hφ => mono (fun χ' h' => by
                rcases h' with rfl | h'
                · exact Set.mem_insert ..
                · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h'))
              (hD φ hφ))

/-- The workhorse: transform a `disjOf`-derivation by handling each
`fal`-disjunct and injecting the modal part into a superlist. -/
theorem disjOf_transform {Γ : Set PLLFormula} {Ds Ts Ds' Ts' : List PLLFormula}
    (h : Γ ⊩ disjOf Ds Ts)
    (hD : ∀ φ ∈ Ds, insert φ Γ ⊩ disjOf Ds' Ts')
    (hT : ∀ φ ∈ Ts, φ ∈ Ts') : Γ ⊩ disjOf Ds' Ts' := by
  refine disjOf_elim h hD (fun hne => ?_)
  have hne' : Ts' ≠ [] := by
    cases Ts with
    | nil => exact absurd rfl hne
    | cons K Ts => exact List.ne_nil_of_mem (hT K (List.mem_cons_self ..))
  refine disjOf_intro_lax hne' ?_
  exact somehow_mono (of_mem (Set.mem_insert ..))
    (bigOr_sub hT (of_mem (Set.mem_insert ..)))

/-- Monotonicity of `disjOf` in both lists. -/
theorem disjOf_mono {Γ : Set PLLFormula} {Ds Ts Ds' Ts' : List PLLFormula}
    (hDs : ∀ φ ∈ Ds, φ ∈ Ds') (hTs : ∀ φ ∈ Ts, φ ∈ Ts')
    (h : Γ ⊩ disjOf Ds Ts) : Γ ⊩ disjOf Ds' Ts' :=
  disjOf_transform h
    (fun φ hφ => disjOf_intro_fal (hDs φ hφ) (of_mem (Set.mem_insert ..)))
    hTs

/-- Remove all occurrences of `φ` from a list. -/
def rmv (φ : PLLFormula) (Ds : List PLLFormula) : List PLLFormula :=
  Ds.filter (fun χ => decide (χ ≠ φ))

theorem mem_rmv_iff {φ ψ : PLLFormula} {Ds : List PLLFormula} :
    ψ ∈ rmv φ Ds ↔ ψ ∈ Ds ∧ ψ ≠ φ := by
  simp [rmv, List.mem_filter]

theorem guard_append {A B A' B' : List PLLFormula}
    (h : A ++ B ≠ []) : (A ++ A') ++ (B ++ B') ≠ [] := by
  simp only [ne_eq, List.append_eq_nil_iff] at h ⊢
  tauto

/-! ### Lindenbaum: maximally consistent extensions via Zorn -/

/-- Maximal consistency: consistent, and any consistent extension is no
larger. -/
def MaxConsistent (T : Theory) : Prop :=
  Consistent T ∧ ∀ T', Consistent T' → T ≤ T' → T' ≤ T

private theorem chain_cover {c : Set Theory} (hc : IsChain (· ≤ ·) c)
    {y : Theory} (hy : y ∈ c) (sel : Theory → Set PLLFormula)
    (hsel : ∀ {T T' : Theory}, T ≤ T' → sel T ⊆ sel T')
    (L : List PLLFormula) (hL : ∀ φ ∈ L, ∃ T ∈ c, φ ∈ sel T) :
    ∃ T ∈ c, ∀ φ ∈ L, φ ∈ sel T := by
  induction L with
  | nil => exact ⟨y, hy, by simp⟩
  | cons ψ L ih =>
      obtain ⟨T₁, hT₁, hmem⟩ := hL ψ (List.mem_cons_self ..)
      obtain ⟨T₂, hT₂, hall⟩ := ih (fun φ hφ => hL φ (List.mem_cons_of_mem _ hφ))
      rcases eq_or_ne T₁ T₂ with rfl | hne
      · refine ⟨T₁, hT₁, fun φ hφ => ?_⟩
        rcases List.mem_cons.mp hφ with rfl | hφ
        exacts [hmem, hall φ hφ]
      rcases hc hT₁ hT₂ hne with hle | hle
      · refine ⟨T₂, hT₂, fun φ hφ => ?_⟩
        rcases List.mem_cons.mp hφ with rfl | hφ
        exacts [hsel hle hmem, hall φ hφ]
      · refine ⟨T₁, hT₁, fun φ hφ => ?_⟩
        rcases List.mem_cons.mp hφ with rfl | hφ
        exacts [hmem, hsel hle (hall φ hφ)]

private theorem chain_ub₂ {c : Set Theory} (hc : IsChain (· ≤ ·) c)
    {T₁ T₂ : Theory} (h₁ : T₁ ∈ c) (h₂ : T₂ ∈ c) :
    ∃ T ∈ c, T₁ ≤ T ∧ T₂ ≤ T := by
  rcases eq_or_ne T₁ T₂ with rfl | hne
  · exact ⟨T₁, h₁, le_refl _, le_refl _⟩
  rcases hc h₁ h₂ hne with h | h
  · exact ⟨T₂, h₂, h, le_refl _⟩
  · exact ⟨T₁, h₁, le_refl _, h⟩

/-- **Lindenbaum lemma**: every consistent theory extends to a maximally
consistent one.  (Zorn; consistency has finite character.) -/
theorem exists_maxConsistent_extension {T₀ : Theory} (h₀ : Consistent T₀) :
    ∃ T, T₀ ≤ T ∧ MaxConsistent T := by
  have hchain : ∀ c ⊆ {T : Theory | Consistent T}, IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {T : Theory | Consistent T}, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨⟨⋃ T ∈ c, T.val, ⋃ T ∈ c, T.fal, ⋃ T ∈ c, T.mfal⟩, ?_, ?_⟩
    · -- the union of a chain of consistent theories is consistent
      intro Ds Ts hDs hTs hne hder
      obtain ⟨L, hL, hp⟩ := hder
      obtain ⟨Ta, hTa, hLa⟩ := chain_cover hc hy Theory.val (fun h => h.1) L
        (fun φ hφ => by simpa using hL φ hφ)
      obtain ⟨Tb, hTb, hLb⟩ := chain_cover hc hy Theory.fal (fun h => h.2.1) Ds
        (fun φ hφ => by simpa using hDs φ hφ)
      obtain ⟨Tc, hTc, hLc⟩ := chain_cover hc hy Theory.mfal (fun h => h.2.2) Ts
        (fun φ hφ => by simpa using hTs φ hφ)
      obtain ⟨Tab, hTab, hab₁, hab₂⟩ := chain_ub₂ hc hTa hTb
      obtain ⟨T, hT, h₁, h₂⟩ := chain_ub₂ hc hTab hTc
      have hcons := hcS hT
      exact hcons Ds Ts
        (fun φ hφ => (h₁.2.1 (hab₂.2.1 (hLb φ hφ))))
        (fun φ hφ => h₂.2.2 (hLc φ hφ))
        hne
        ⟨L, fun φ hφ => h₁.1 (hab₁.1 (hLa φ hφ)), hp⟩
    · intro T hT
      exact ⟨Set.subset_biUnion_of_mem hT, Set.subset_biUnion_of_mem hT,
        Set.subset_biUnion_of_mem hT⟩
  obtain ⟨m, hm₀, hmem, hmax⟩ :=
    zorn_le_nonempty₀ {T : Theory | Consistent T} hchain T₀ h₀
  exact ⟨m, hm₀, hmem, fun T' hT' hle => hmax hT' hle⟩

/-! ### Properties of maximally consistent theories (F&M Lemma 4.2) -/

namespace MaxConsistent

theorem not_fal_deriv {T : Theory} (hM : MaxConsistent T)
    {φ : PLLFormula} (hφ : φ ∈ T.fal)
    (hd : T.val ⊩ φ) : False := by
  refine hM.1 [φ] [] (by simpa using hφ) (by simp) (by simp) ?_
  rw [disjOf_nil_right]
  exact bigOr_intro (List.mem_cons_self ..) hd

/-- (i) deductive closure of the validated part. -/
theorem ded_closed {T : Theory} (hM : MaxConsistent T)
    {φ : PLLFormula} (hd : T.val ⊩ φ) : φ ∈ T.val := by
  have hcons : Consistent ⟨insert φ T.val, T.fal, T.mfal⟩ := by
    intro Ds Ts h1 h2 hg hder
    exact hM.1 Ds Ts h1 h2 hg (SetDeriv.cut hd hder)
  exact (hM.2 _ hcons ⟨Set.subset_insert .., subset_rfl, subset_rfl⟩).1
    (Set.mem_insert ..)

/-- Adding an underivable formula to `val` stays consistent — packaged form
of the maximality argument. -/
private theorem val_ext {T : Theory} (hM : MaxConsistent T) {φ : PLLFormula}
    (h : φ ∉ T.val) :
    ∃ Ds Ts : List PLLFormula,
      (∀ ψ ∈ Ds, ψ ∈ T.fal) ∧ (∀ ψ ∈ Ts, ψ ∈ T.mfal) ∧ Ds ++ Ts ≠ [] ∧
        insert φ T.val ⊩ disjOf Ds Ts := by
  rw [← not_consistent_iff (T := ⟨insert φ T.val, T.fal, T.mfal⟩)]
  intro hcons
  exact h ((hM.2 _ hcons ⟨Set.subset_insert .., subset_rfl, subset_rfl⟩).1
    (Set.mem_insert ..))

/-- Adding a formula to `fal` when it is not there: witness of failure. -/
private theorem fal_ext {T : Theory} (hM : MaxConsistent T) {φ : PLLFormula}
    (h : φ ∉ T.fal) :
    ∃ Ds Ts : List PLLFormula,
      (∀ ψ ∈ Ds, ψ ∈ insert φ T.fal) ∧ (∀ ψ ∈ Ts, ψ ∈ T.mfal) ∧
        Ds ++ Ts ≠ [] ∧ T.val ⊩ disjOf Ds Ts := by
  rw [← not_consistent_iff (T := ⟨T.val, insert φ T.fal, T.mfal⟩)]
  intro hcons
  exact h ((hM.2 _ hcons ⟨subset_rfl, Set.subset_insert .., subset_rfl⟩).2.1
    (Set.mem_insert ..))

/-- (vii) totality: every formula is validated or falsified. -/
theorem mem_val_or_mem_fal {T : Theory} (hM : MaxConsistent T)
    (φ : PLLFormula) :
    φ ∈ T.val ∨ φ ∈ T.fal := by
  by_cases hv : φ ∈ T.val
  · exact .inl hv
  by_cases hf : φ ∈ T.fal
  · exact .inr hf
  exfalso
  obtain ⟨Ds₁, Ts₁, hDs₁, hTs₁, hg₁, hd₁⟩ := hM.val_ext hv
  obtain ⟨Ds₂, Ts₂, hDs₂, hTs₂, hg₂, hd₂⟩ := hM.fal_ext hf
  have hd : T.val ⊩ disjOf (Ds₁ ++ rmv φ Ds₂) (Ts₁ ++ Ts₂) := by
    refine disjOf_transform hd₂ (fun ψ hψ => ?_)
      (fun ψ hψ => List.mem_append.mpr (.inr hψ))
    by_cases he : ψ = φ
    · subst he
      exact disjOf_mono
        (fun χ hχ => List.mem_append.mpr (.inl hχ))
        (fun χ hχ => List.mem_append.mpr (.inl hχ)) hd₁
    · exact disjOf_intro_fal
        (List.mem_append.mpr (.inr (mem_rmv_iff.mpr ⟨hψ, he⟩)))
        (of_mem (Set.mem_insert ..))
  refine hM.1 _ _ ?_ ?_ (guard_append hg₁) hd
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    · exact hDs₁ ψ h
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h
      rcases hDs₂ ψ hin with rfl | h'
      · exact absurd rfl hne
      · exact h'
  · intro ψ hψ
    rcases List.mem_append.mp hψ with h | h
    exacts [hTs₁ ψ h, hTs₂ ψ h]

theorem not_mem_fal_of_mem_val {T : Theory} (hM : MaxConsistent T)
    {φ : PLLFormula} (hv : φ ∈ T.val) :
    φ ∉ T.fal :=
  fun hf => hM.not_fal_deriv hf (of_mem hv)

/-- (ii) primeness of `val`. -/
theorem or_mem {T : Theory} (hM : MaxConsistent T)
    {φ ψ : PLLFormula} (h : φ.or ψ ∈ T.val) :
    φ ∈ T.val ∨ ψ ∈ T.val := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨Ds₁, Ts₁, hDs₁, hTs₁, hg₁, hd₁⟩ := hM.val_ext hcon.1
  obtain ⟨Ds₂, Ts₂, hDs₂, hTs₂, hg₂, hd₂⟩ := hM.val_ext hcon.2
  have hd : T.val ⊩ disjOf (Ds₁ ++ Ds₂) (Ts₁ ++ Ts₂) := by
    refine orE (of_mem h) ?_ ?_
    · exact disjOf_mono (fun χ hχ => List.mem_append.mpr (.inl hχ))
        (fun χ hχ => List.mem_append.mpr (.inl hχ)) hd₁
    · exact disjOf_mono (fun χ hχ => List.mem_append.mpr (.inr hχ))
        (fun χ hχ => List.mem_append.mpr (.inr hχ)) hd₂
  refine hM.1 _ _ ?_ ?_ (guard_append hg₁) hd
  · intro χ hχ
    rcases List.mem_append.mp hχ with h' | h'
    exacts [hDs₁ χ h', hDs₂ χ h']
  · intro χ hχ
    rcases List.mem_append.mp hχ with h' | h'
    exacts [hTs₁ χ h', hTs₂ χ h']

/-- (iii) implication decomposition. -/
theorem imp_mem {T : Theory} (hM : MaxConsistent T)
    {φ ψ : PLLFormula} (h : φ.ifThen ψ ∈ T.val) :
    φ ∈ T.fal ∨ ψ ∈ T.val := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨Ds₁, Ts₁, hDs₁, hTs₁, hg₁, hd₁⟩ := hM.val_ext hcon.2
  obtain ⟨Ds₂, Ts₂, hDs₂, hTs₂, hg₂, hd₂⟩ := hM.fal_ext hcon.1
  have hd : T.val ⊩ disjOf (Ds₁ ++ rmv φ Ds₂) (Ts₁ ++ Ts₂) := by
    refine disjOf_transform hd₂ (fun χ hχ => ?_)
      (fun χ hχ => List.mem_append.mpr (.inr hχ))
    by_cases he : χ = φ
    · subst he
      have hψ : insert χ T.val ⊩ ψ :=
        mp (of_mem (Set.mem_insert_of_mem _ h)) (of_mem (Set.mem_insert ..))
      refine SetDeriv.cut hψ ?_
      refine disjOf_mono (fun χ' hχ' => List.mem_append.mpr (.inl hχ'))
        (fun χ' hχ' => List.mem_append.mpr (.inl hχ')) ?_
      exact mono (Set.insert_subset_insert (Set.subset_insert ..)) hd₁
    · exact disjOf_intro_fal
        (List.mem_append.mpr (.inr (mem_rmv_iff.mpr ⟨hχ, he⟩)))
        (of_mem (Set.mem_insert ..))
  refine hM.1 _ _ ?_ ?_ (guard_append hg₁) hd
  · intro χ hχ
    rcases List.mem_append.mp hχ with h' | h'
    · exact hDs₁ χ h'
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h'
      rcases hDs₂ χ hin with rfl | h''
      · exact absurd rfl hne
      · exact h''
  · intro χ hχ
    rcases List.mem_append.mp hχ with h' | h'
    exacts [hTs₁ χ h', hTs₂ χ h']

/-- (iv) falsified disjunctions decompose conjunctively. -/
theorem fal_or {T : Theory} (hM : MaxConsistent T)
    {φ ψ : PLLFormula} (h : φ.or ψ ∈ T.fal) :
    φ ∈ T.fal ∧ ψ ∈ T.fal := by
  have main : ∀ χ : PLLFormula,
      (∀ Γ : Set PLLFormula, Γ ⊩ χ → Γ ⊩ φ.or ψ) → χ ∈ T.fal := by
    intro χ hinj
    by_contra hχ
    obtain ⟨Ds, Ts, hDs, hTs, hg, hd⟩ := hM.fal_ext hχ
    have hd' : T.val ⊩ disjOf ((φ.or ψ) :: rmv χ Ds) Ts := by
      refine disjOf_transform hd (fun χ' hχ' => ?_) (fun χ' hχ' => hχ')
      by_cases he : χ' = χ
      · subst he
        exact disjOf_intro_fal (List.mem_cons_self ..)
          (hinj _ (of_mem (Set.mem_insert ..)))
      · exact disjOf_intro_fal
          (List.mem_cons_of_mem _ (mem_rmv_iff.mpr ⟨hχ', he⟩))
          (of_mem (Set.mem_insert ..))
    refine hM.1 _ _ ?_ hTs (by simp) hd'
    intro χ' hχ'
    rcases List.mem_cons.mp hχ' with rfl | h'
    · exact h
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h'
      rcases hDs χ' hin with rfl | h''
      · exact absurd rfl hne
      · exact h''
  exact ⟨main φ (fun Γ hd => orL _ hd), main ψ (fun Γ hd => orR _ hd)⟩

/-- (v) falsified conjunctions decompose disjunctively. -/
theorem fal_and {T : Theory} (hM : MaxConsistent T)
    {φ ψ : PLLFormula} (h : φ.and ψ ∈ T.fal) :
    φ ∈ T.fal ∨ ψ ∈ T.fal := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨Ds₁, Ts₁, hDs₁, hTs₁, hg₁, hd₁⟩ := hM.fal_ext hcon.1
  obtain ⟨Ds₂, Ts₂, hDs₂, hTs₂, hg₂, hd₂⟩ := hM.fal_ext hcon.2
  have hd : T.val ⊩
      disjOf ((φ.and ψ) :: (rmv φ Ds₁ ++ rmv ψ Ds₂)) (Ts₁ ++ Ts₂) := by
    refine disjOf_transform hd₁ (fun χ hχ => ?_)
      (fun χ hχ => List.mem_append.mpr (.inl hχ))
    by_cases he : χ = φ
    · subst he
      refine disjOf_transform
        (mono (Set.subset_insert ..) hd₂) (fun χ' hχ' => ?_)
        (fun χ' hχ' => List.mem_append.mpr (.inr hχ'))
      by_cases he' : χ' = ψ
      · subst he'
        refine disjOf_intro_fal (List.mem_cons_self ..) ?_
        exact map₂ (fun p₁ p₂ => .andIntro p₁ p₂)
          (of_mem (Set.mem_insert_of_mem _ (Set.mem_insert ..)))
          (of_mem (Set.mem_insert ..))
      · exact disjOf_intro_fal
          (List.mem_cons_of_mem _
            (List.mem_append.mpr (.inr (mem_rmv_iff.mpr ⟨hχ', he'⟩))))
          (of_mem (Set.mem_insert ..))
    · exact disjOf_intro_fal
        (List.mem_cons_of_mem _
          (List.mem_append.mpr (.inl (mem_rmv_iff.mpr ⟨hχ, he⟩))))
        (of_mem (Set.mem_insert ..))
  refine hM.1 _ _ ?_ ?_ (by simp) hd
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | h'
    · exact h
    rcases List.mem_append.mp h' with h'' | h''
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h''
      rcases hDs₁ χ hin with rfl | h₃
      · exact absurd rfl hne
      · exact h₃
    · obtain ⟨hin, hne⟩ := mem_rmv_iff.mp h''
      rcases hDs₂ χ hin with rfl | h₃
      · exact absurd rfl hne
      · exact h₃
  · intro χ hχ
    rcases List.mem_append.mp hχ with h' | h'
    exacts [hTs₁ χ h', hTs₂ χ h']

/-- (vi) `Θ ⊆ Δ`: modally falsified formulas are falsified. -/
theorem mfal_sub_fal {T : Theory} (hM : MaxConsistent T)
    {φ : PLLFormula} (h : φ ∈ T.mfal) : φ ∈ T.fal := by
  by_contra hφ
  obtain ⟨Ds, Ts, hDs, hTs, hg, hd⟩ := hM.fal_ext hφ
  have hd' : T.val ⊩ disjOf (rmv φ Ds) (φ :: Ts) := by
    refine disjOf_transform hd (fun χ hχ => ?_)
      (fun χ hχ => List.mem_cons_of_mem _ hχ)
    by_cases he : χ = φ
    · subst he
      refine disjOf_intro_lax (by simp) ?_
      refine map (fun p => .laxIntro p) ?_
      exact bigOr_intro (List.mem_cons_self ..) (of_mem (Set.mem_insert ..))
    · exact disjOf_intro_fal (mem_rmv_iff.mpr ⟨hχ, he⟩)
        (of_mem (Set.mem_insert ..))
  refine hM.1 _ _ ?_ ?_ (by simp) hd'
  · intro χ hχ
    obtain ⟨hin, hne⟩ := mem_rmv_iff.mp hχ
    rcases hDs χ hin with rfl | h'
    · exact absurd rfl hne
    · exact h'
  · intro χ hχ
    rcases List.mem_cons.mp hχ with rfl | h'
    exacts [h, hTs χ h']

end MaxConsistent

/-! ### The canonical model -/

/-- Worlds of the canonical model: maximally consistent theories. -/
def MaxTheory : Type := {T : Theory // MaxConsistent T}

private theorem list_sub_empty {Ds : List PLLFormula}
    (h : ∀ φ ∈ Ds, φ ∈ (∅ : Set PLLFormula)) : Ds = [] := by
  cases Ds with
  | nil => rfl
  | cons φ Ds => exact absurd (h φ (List.mem_cons_self ..)) (by simp)

/-- The canonical constraint model (F&M §4). -/
def canonical : ConstraintModel where
  W := MaxTheory
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm T T' := T.1.val ⊆ T'.1.val ∧ T.1.mfal ⊆ T'.1.mfal
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m _ := ⟨subset_rfl, subset_rfl⟩
  trans_m h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := h hw
  full_F {_} {T} hw := T.2.ded_closed (SetDeriv.falso _
    (SetDeriv.of_mem (show PLLFormula.falsePLL ∈ T.1.val from hw)))

/-- **Truth lemma** (F&M Lemma 4.3): membership in `val` forces, membership
in `fal` refutes. -/
theorem truth_lemma (φ : PLLFormula) :
    ∀ T : MaxTheory,
      (φ ∈ T.1.val → canonical.force T φ) ∧
        (φ ∈ T.1.fal → ¬ canonical.force T φ) := by
  induction φ with
  | prop a =>
      intro T
      refine ⟨fun h => h, fun h hf => ?_⟩
      exact T.2.not_fal_deriv h (SetDeriv.of_mem hf)
  | falsePLL =>
      intro T
      refine ⟨fun h => h, fun h hf => ?_⟩
      exact T.2.not_fal_deriv h (SetDeriv.of_mem hf)
  | and φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro h
        have hφ : φ ∈ T.1.val :=
          T.2.ded_closed (SetDeriv.map (fun p => .andElim1 p) (SetDeriv.of_mem h))
        have hψ : ψ ∈ T.1.val :=
          T.2.ded_closed (SetDeriv.map (fun p => .andElim2 p) (SetDeriv.of_mem h))
        exact ⟨(ihφ T).1 hφ, (ihψ T).1 hψ⟩
      · intro h hf
        rcases T.2.fal_and h with h' | h'
        · exact (ihφ T).2 h' hf.1
        · exact (ihψ T).2 h' hf.2
  | or φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro h
        rcases T.2.or_mem h with h' | h'
        · exact .inl ((ihφ T).1 h')
        · exact .inr ((ihψ T).1 h')
      · intro h hf
        obtain ⟨h₁, h₂⟩ := T.2.fal_or h
        rcases hf with hf | hf
        · exact (ihφ T).2 h₁ hf
        · exact (ihψ T).2 h₂ hf
  | ifThen φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro h T' hle hfφ
        have h' : φ.ifThen ψ ∈ T'.1.val := hle h
        rcases T'.2.imp_mem h' with h'' | h''
        · exact absurd hfφ ((ihφ T').2 h'')
        · exact (ihψ T').1 h''
      · intro h hf
        -- extend ⟨insert φ val, {ψ}, ∅⟩ to a maximally consistent theory
        have hcons : Consistent ⟨insert φ T.1.val, {ψ}, ∅⟩ := by
          intro Ds Ts hDs hTs hg hder
          have hTs' : Ts = [] := list_sub_empty hTs
          subst hTs'
          rw [disjOf_nil_right] at hder
          have hψ : insert φ T.1.val ⊩ ψ :=
            SetDeriv.bigOr_collapse (fun χ hχ => hDs χ hχ) hder
          exact T.2.not_fal_deriv h (SetDeriv.deduct hψ)
        obtain ⟨T', hle, hM'⟩ := exists_maxConsistent_extension hcons
        have hRi : T.1.val ⊆ T'.val :=
          (Set.subset_insert ..).trans hle.1
        have hfφ' : canonical.force ⟨T', hM'⟩ φ :=
          (ihφ ⟨T', hM'⟩).1 (hle.1 (Set.mem_insert ..))
        have hfψ' : ¬ canonical.force ⟨T', hM'⟩ ψ :=
          (ihψ ⟨T', hM'⟩).2 (hle.2.1 rfl)
        exact hfψ' (hf ⟨T', hM'⟩ hRi hfφ')
  | somehow φ ih =>
      intro T
      constructor
      · intro h T₁ hle
        -- ◯φ ∈ val ⊆ val₁; extend ⟨insert φ val₁, ∅, mfal₁⟩
        have hcons : Consistent ⟨insert φ T₁.1.val, ∅, T₁.1.mfal⟩ := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := list_sub_empty hDs
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left] at hder
              have himp : T₁.1.val ⊩ φ.ifThen (.somehow (bigOr (K :: Ts))) :=
                SetDeriv.deduct hder
              have hlax : T₁.1.val ⊩ .somehow (bigOr (K :: Ts)) :=
                SetDeriv.somehow_bind (SetDeriv.of_mem (hle h)) himp
              refine T₁.2.1 [] (K :: Ts) (by simp) hTs (by simp) ?_
              rwa [disjOf_nil_left]
        obtain ⟨T₂, hle₂, hM₂⟩ := exists_maxConsistent_extension hcons
        refine ⟨⟨T₂, hM₂⟩, ⟨(Set.subset_insert ..).trans hle₂.1, hle₂.2.2⟩, ?_⟩
        exact (ih ⟨T₂, hM₂⟩).1 (hle₂.1 (Set.mem_insert ..))
      · intro h hf
        -- extend ⟨val, ∅, {φ}⟩; its Rm-successors all refute φ
        have hcons : Consistent ⟨T.1.val, ∅, {φ}⟩ := by
          intro Ds Ts hDs hTs hg hder
          have hDs' : Ds = [] := list_sub_empty hDs
          subst hDs'
          cases Ts with
          | nil => exact hg rfl
          | cons K Ts =>
              rw [disjOf_nil_left] at hder
              have hφd : T.1.val ⊩ .somehow φ :=
                SetDeriv.somehow_mono hder
                  (SetDeriv.bigOr_collapse (fun χ hχ => hTs χ hχ)
                    (SetDeriv.of_mem (Set.mem_insert ..)))
              exact T.2.not_fal_deriv h hφd
        obtain ⟨T', hle, hM'⟩ := exists_maxConsistent_extension hcons
        obtain ⟨T₂, hRm, hfφ⟩ := hf ⟨T', hM'⟩ hle.1
        have hmem : φ ∈ T₂.1.mfal := hRm.2 (hle.2.2 rfl)
        exact (ih T₂).2 (T₂.2.mfal_sub_fal hmem) hfφ

/-! ### Completeness -/

/-- **Completeness** (F&M Theorem 4.4, strengthened to sequents): a semantic
consequence over a finite context is derivable. -/
theorem completeness {Γ : List PLLFormula} {φ : PLLFormula}
    (h : Γ ⊨- φ) : Nonempty (LaxND Γ φ) := by
  by_contra hn
  have hcons : Consistent ⟨{ψ | ψ ∈ Γ}, {φ}, ∅⟩ := by
    intro Ds Ts hDs hTs hg hder
    have hTs' : Ts = [] := list_sub_empty hTs
    subst hTs'
    rw [disjOf_nil_right] at hder
    have hd : {ψ | ψ ∈ Γ} ⊩ φ :=
      SetDeriv.bigOr_collapse (fun χ hχ => hDs χ hχ) hder
    obtain ⟨L, hL, ⟨p⟩⟩ := hd
    exact hn ⟨p.rename hL⟩
  obtain ⟨T, hle, hM⟩ := exists_maxConsistent_extension hcons
  have hforce : ∀ ψ ∈ Γ, canonical.force ⟨T, hM⟩ ψ :=
    fun ψ hψ => (truth_lemma ψ ⟨T, hM⟩).1 (hle.1 hψ)
  have := h canonical ⟨T, hM⟩ hforce
  exact (truth_lemma φ ⟨T, hM⟩).2 (hle.2.1 rfl) this

/-- **Soundness and completeness combined**: derivability coincides with
semantic consequence over constraint models. -/
theorem consequence_iff_derivable {Γ : List PLLFormula} {φ : PLLFormula} :
    Γ ⊨- φ ↔ Nonempty (LaxND Γ φ) :=
  ⟨completeness, fun ⟨p⟩ => soundness p⟩

/-- Validity coincides with theoremhood. -/
theorem valid_iff_provable {φ : PLLFormula} :
    (∀ (C : ConstraintModel) (w : C.W), C.force w φ) ↔
      Nonempty (LaxND [] φ) := by
  constructor
  · intro h
    exact completeness (fun C w _ => h C w)
  · rintro ⟨p⟩ C w
    exact soundness_valid p C w

end PLLND
