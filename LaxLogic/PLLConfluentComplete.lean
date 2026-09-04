import LaxLogic.PLLFrames
import Mathlib.Order.Zorn

/-!
# Completeness of PLL + `◯(A∨B) ⊃ (◯A∨◯B)` for confluent constraint models

The soundness side of the F&M Theorem 4.5 correspondence is in
`PLLFrames.lean`: on mutually confluent models the `∀∃` clause for `◯`
collapses to bare possibility (`force_somehow_iff_of_confluent`) and the
distribution scheme is valid (`force_somehow_or_dist_of_confluent`).
This file proves the **completeness** side: the extension of PLL by the
scheme

    distF A B  :=  ◯(A ∨ B) ⊃ (◯A ∨ ◯B)

is complete for mutually confluent constraint models, so the two
together give

    DerivU Γ φ  ↔  Γ ⊨ φ over all mutually confluent models
                                     (`derivU_iff_confluent_valid`).

The extended system `DerivU` is natural deduction with finitely many
instances of the scheme as extra hypotheses — equivalent to the Hilbert
extension by the schema, with the whole of `LaxND`'s admissible
structure available.

**The construction.**  Worlds of the canonical model are the
deductively closed prime sets of formulas (the improper set is allowed:
it is the fallible world); `Rᵢ` is inclusion and `T Rₘ U` is inclusion
together with `∀ ψ ∈ U, ◯ψ ∈ T`.  The engine is the operator

    obInv T := {ψ | ◯ψ ∈ T}

which, **precisely because of the distribution scheme**, carries closed
prime sets to prime sets; it contains `T` (unit), and everything it
contains is `◯`-ed in `T` (definition), so it witnesses both the modal
case of the truth lemma and — applied to the `Rᵢ`-successor — mutual
confluence of the canonical frame.  No third theory component
("promises") is needed anywhere: on confluent frames the refutation of
a `◯`-formula needs no separate bookkeeping, because the clause is
already bare possibility.

The Lindenbaum step (prime extension avoiding a formula) is by Zorn;
the file is deliberately classical (audit `clean`), like the parent's
`PLLCompleteness.lean` and unlike the finite construction of
`PLLFinComp.lean`.
-/

open PLLFormula

namespace PLLND
namespace ConfluentU

/-! ## The extended system -/

/-- One instance of the distribution scheme. -/
def distF (A B : PLLFormula) : PLLFormula :=
  (somehow (A.or B)).ifThen ((somehow A).or (somehow B))

/-- A list of instances of the scheme. -/
def DistList (L : List PLLFormula) : Prop :=
  ∀ θ ∈ L, ∃ A B, θ = distF A B

theorem DistList.nil : DistList ([] : List PLLFormula) := by
  intro θ h
  exact absurd h (by simp)

/-- PLL extended by the distribution scheme, hypothesis form: derivable
in `LaxND` from `Γ` together with finitely many scheme instances. -/
def DerivU (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  ∃ L, DistList L ∧ Nonempty (LaxND (L ++ Γ) φ)

theorem DerivU.of_nd {Γ : List PLLFormula} {φ : PLLFormula} (p : LaxND Γ φ) : DerivU Γ φ :=
  ⟨[], DistList.nil, ⟨p⟩⟩

theorem DerivU.hyp {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : DerivU Γ φ :=
  .of_nd (.iden h)

theorem DerivU.dist (A B : PLLFormula) {Γ} : DerivU Γ (distF A B) :=
  ⟨[distF A B], ⟨fun θ h => ⟨A, B, by simpa using h⟩,
    ⟨.iden (by simp)⟩⟩⟩

theorem DerivU.rename {Γ Γ' : List PLLFormula} {φ : PLLFormula} (H : ∀ ψ ∈ Γ, ψ ∈ Γ') :
    DerivU Γ φ → DerivU Γ' φ := by
  rintro ⟨L, hL, ⟨p⟩⟩
  refine ⟨L, hL, ⟨p.rename ?_⟩⟩
  intro ψ h
  simp only [List.mem_append] at h ⊢
  rcases h with h | h
  exacts [Or.inl h, Or.inr (H ψ h)]

theorem DerivU.mp {Γ : List PLLFormula} {φ ψ : PLLFormula} (h₁ : DerivU Γ (φ.ifThen ψ)) (h₂ : DerivU Γ φ) :
    DerivU Γ ψ := by
  obtain ⟨L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨L₂, hL₂, ⟨p₂⟩⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ⟨?_⟩⟩
  · intro θ h
    rcases List.mem_append.mp h with h | h
    exacts [hL₁ θ h, hL₂ θ h]
  · refine .impElim (p₁.rename ?_) (p₂.rename ?_) <;>
      · intro ψ' h
        simp only [List.mem_append] at h ⊢
        tauto

theorem DerivU.deduction {Γ : List PLLFormula} {φ ψ : PLLFormula} (h : DerivU (φ :: Γ) ψ) :
    DerivU Γ (φ.ifThen ψ) := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine ⟨L, hL, ⟨.impIntro (p.rename ?_)⟩⟩
  intro θ hθ
  simp only [List.mem_append, List.mem_cons] at hθ ⊢
  tauto

theorem DerivU.unit {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivU Γ φ) : DerivU Γ (somehow φ) := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  exact ⟨L, hL, ⟨.laxIntro p⟩⟩

/-! ## Set-level derivability -/

/-- `T` derives `φ` in the extended system: some finite context drawn
from `T` does. -/
def SDeriv (T : Set PLLFormula) (φ : PLLFormula) : Prop :=
  ∃ Γ : List PLLFormula, (∀ ψ ∈ Γ, ψ ∈ T) ∧ DerivU Γ φ

theorem SDeriv.of_mem {T : Set PLLFormula} {φ : PLLFormula} (h : φ ∈ T) : SDeriv T φ :=
  ⟨[φ], by simpa using h, .hyp (by simp)⟩

theorem SDeriv.mono {T U : Set PLLFormula} {φ : PLLFormula} (hTU : T ⊆ U) :
    SDeriv T φ → SDeriv U φ := by
  rintro ⟨Γ, hΓ, hd⟩
  exact ⟨Γ, fun ψ h => hTU (hΓ ψ h), hd⟩

theorem SDeriv.mp {T : Set PLLFormula} {φ ψ : PLLFormula}
    (h₁ : SDeriv T (φ.ifThen ψ)) (h₂ : SDeriv T φ) : SDeriv T ψ := by
  obtain ⟨Γ₁, hΓ₁, hd₁⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, hd₂⟩ := h₂
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ψ' h
    rcases List.mem_append.mp h with h | h
    exacts [hΓ₁ ψ' h, hΓ₂ ψ' h]
  · exact DerivU.mp
      (hd₁.rename (by intro θ h; simp only [List.mem_append]; tauto))
      (hd₂.rename (by intro θ h; simp only [List.mem_append]; tauto))

theorem SDeriv.unit {T : Set PLLFormula} {φ : PLLFormula} (h : SDeriv T φ) :
    SDeriv T (somehow φ) := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  exact ⟨Γ, hΓ, hd.unit⟩

theorem SDeriv.andI {T : Set PLLFormula} {φ ψ : PLLFormula}
    (h₁ : SDeriv T φ) (h₂ : SDeriv T ψ) : SDeriv T (φ.and ψ) := by
  obtain ⟨Γ₁, hΓ₁, L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, L₂, hL₂, ⟨p₂⟩⟩ := h₂
  refine ⟨Γ₁ ++ Γ₂, ?_, L₁ ++ L₂, ?_, ⟨.andIntro (p₁.rename ?_) (p₂.rename ?_)⟩⟩
  · intro ψ' h
    rcases List.mem_append.mp h with h | h
    exacts [hΓ₁ ψ' h, hΓ₂ ψ' h]
  · intro θ h
    rcases List.mem_append.mp h with h | h
    exacts [hL₁ θ h, hL₂ θ h]
  all_goals
    intro θ h
    simp only [List.mem_append] at h ⊢
    tauto

theorem SDeriv.andE₁ {T : Set PLLFormula} {φ ψ : PLLFormula}
    (h : SDeriv T (PLLFormula.and φ ψ)) : SDeriv T φ := by
  obtain ⟨Γ, hΓ, L, hL, ⟨p⟩⟩ := h
  exact ⟨Γ, hΓ, L, hL, ⟨.andElim1 p⟩⟩

theorem SDeriv.andE₂ {T : Set PLLFormula} {φ ψ : PLLFormula}
    (h : SDeriv T (PLLFormula.and φ ψ)) : SDeriv T ψ := by
  obtain ⟨Γ, hΓ, L, hL, ⟨p⟩⟩ := h
  exact ⟨Γ, hΓ, L, hL, ⟨.andElim2 p⟩⟩

theorem SDeriv.orI₁ {T : Set PLLFormula} {φ ψ : PLLFormula} (h : SDeriv T φ) :
    SDeriv T (PLLFormula.or φ ψ) := by
  obtain ⟨Γ, hΓ, L, hL, ⟨p⟩⟩ := h
  exact ⟨Γ, hΓ, L, hL, ⟨.orIntro1 p⟩⟩

theorem SDeriv.orI₂ {T : Set PLLFormula} {φ ψ : PLLFormula} (h : SDeriv T ψ) :
    SDeriv T (PLLFormula.or φ ψ) := by
  obtain ⟨Γ, hΓ, L, hL, ⟨p⟩⟩ := h
  exact ⟨Γ, hΓ, L, hL, ⟨.orIntro2 p⟩⟩

/-- Deduction theorem, set form.  Decidable equality of formulas
filters the used context. -/
theorem SDeriv.deduction {T : Set PLLFormula} {φ ψ : PLLFormula}
    (h : SDeriv (insert φ T) ψ) : SDeriv T (φ.ifThen ψ) := by
  obtain ⟨Γ, hΓ, hd⟩ := h
  refine ⟨Γ.filter (fun θ => decide (θ ≠ φ)), ?_, ?_⟩
  · intro θ hθ
    rw [List.mem_filter] at hθ
    have hne : θ ≠ φ := by simpa using hθ.2
    rcases hΓ θ hθ.1 with h | h
    · exact absurd h hne
    · exact h
  · refine DerivU.deduction (hd.rename ?_)
    intro θ hθ
    by_cases hθφ : θ = φ
    · simp [hθφ]
    · simp only [List.mem_cons, List.mem_filter]
      exact Or.inr ⟨hθ, by simpa using hθφ⟩

/-- `∨`-elimination at set level. -/
theorem SDeriv.or_elim {T : Set PLLFormula} {A B ψ : PLLFormula}
    (h₀ : SDeriv T (A.or B))
    (h₁ : SDeriv T (A.ifThen ψ)) (h₂ : SDeriv T (B.ifThen ψ)) :
    SDeriv T ψ := by
  obtain ⟨Γ₀, hΓ₀, L₀, hL₀, ⟨p₀⟩⟩ := h₀
  obtain ⟨Γ₁, hΓ₁, L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨Γ₂, hΓ₂, L₂, hL₂, ⟨p₂⟩⟩ := h₂
  refine ⟨Γ₀ ++ Γ₁ ++ Γ₂, ?_, (L₀ ++ L₁ ++ L₂), ?_, ⟨?_⟩⟩
  · intro ψ' h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    exacts [hΓ₀ ψ' h, hΓ₁ ψ' h, hΓ₂ ψ' h]
  · intro θ h
    simp only [List.mem_append] at h
    rcases h with (h | h) | h
    exacts [hL₀ θ h, hL₁ θ h, hL₂ θ h]
  · refine .orElim (p₀.rename ?_)
      (.impElim (p₁.rename ?_) (.iden (by simp)))
      (.impElim (p₂.rename ?_) (.iden (by simp))) <;>
      · intro θ h
        simp only [List.mem_append, List.mem_cons] at h ⊢
        tauto

/-- Deductively closed. -/
def SClosed (T : Set PLLFormula) : Prop := ∀ φ, SDeriv T φ → φ ∈ T

/-- Prime. -/
def SPrime (T : Set PLLFormula) : Prop :=
  ∀ A B, (A.or B) ∈ T → A ∈ T ∨ B ∈ T

/-! ## The `◯⁻¹` operator: where the scheme earns its keep -/

/-- `obInv T = {ψ | ◯ψ ∈ T}`. -/
def obInv (T : Set PLLFormula) : Set PLLFormula := {ψ | somehow ψ ∈ T}

theorem subset_obInv {T : Set PLLFormula} (hc : SClosed T) : T ⊆ obInv T :=
  fun _ h => hc _ (SDeriv.unit (SDeriv.of_mem h))

/-- The heart of the file: with the distribution scheme, `obInv`
carries closed prime sets to prime sets. -/
theorem obInv_prime {T : Set PLLFormula} (hc : SClosed T) (hp : SPrime T) :
    SPrime (obInv T) := by
  intro A B hAB
  have hdist : SDeriv T (distF A B) :=
    ⟨[], by simp, DerivU.dist A B⟩
  have h₁ : SDeriv T ((somehow A).or (somehow B)) :=
    hdist.mp (SDeriv.of_mem hAB)
  exact hp _ _ (hc _ h₁)

/-- `obInv` of a closed set is closed: box the conclusion by
`laxIntro`, then bind each hypothesis by `laxElim`. -/
theorem obInv_closed {T : Set PLLFormula} (hc : SClosed T) :
    SClosed (obInv T) := by
  intro φ h
  obtain ⟨Γ, hΓ, L, hL, ⟨p⟩⟩ := h
  have key : ∀ (Γ' Δ : List PLLFormula),
      LaxND (Γ' ++ Δ) (somehow φ) →
      LaxND (Γ'.map somehow ++ Δ) (somehow φ) := by
    intro Γ'
    induction Γ' with
    | nil => intro Δ p; simpa using p
    | cons ψ Γ' ih =>
        intro Δ p
        have p₁ : LaxND (Γ' ++ (ψ :: Δ)) (somehow φ) :=
          p.rename (by
            intro θ h
            simp only [List.mem_append, List.mem_cons] at h ⊢
            tauto)
        have p₂ := ih (ψ :: Δ) p₁
        have p₃ : LaxND (ψ :: (somehow ψ :: (Γ'.map somehow ++ Δ)))
            (somehow φ) :=
          p₂.rename (by
            intro θ h
            simp only [List.mem_append, List.mem_cons] at h ⊢
            tauto)
        have p₄ : LaxND (somehow ψ :: (Γ'.map somehow ++ Δ)) (somehow φ) :=
          .laxElim (.iden (by simp)) p₃
        exact p₄.rename (by
          intro θ h
          simp only [List.map_cons, List.mem_append, List.mem_cons] at h ⊢
          tauto)
  have p₀ : LaxND (Γ ++ L) (somehow φ) :=
    (LaxND.laxIntro p).rename (by
      intro θ h
      simp only [List.mem_append] at h ⊢
      tauto)
  have p₁ := key Γ L p₀
  refine hc _ ⟨Γ.map somehow, ?_, L, hL, ⟨p₁.rename ?_⟩⟩
  · intro ψ h
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp h
    exact hΓ θ hθ
  · intro θ h
    simp only [List.mem_append] at h ⊢
    tauto

/-! ## The canonical model -/

/-- Worlds: deductively closed prime sets (the improper set included —
it is the fallible world). -/
def Wld : Type := {T : Set PLLFormula // SClosed T ∧ SPrime T}

/-- The canonical confluent model. -/
@[reducible] def canonU : ConstraintModel where
  W := Wld
  Ri T U := T.1 ⊆ U.1
  Rm T U := T.1 ⊆ U.1 ∧ ∀ ψ ∈ U.1, somehow ψ ∈ T.1
  F := {T | falsePLL ∈ T.1}
  V a := {T | prop a ∈ T.1}
  refl_i _ := le_refl _
  trans_i h h' := le_trans h h'
  refl_m {T} := ⟨le_refl _, fun _ h => subset_obInv T.2.1 h⟩
  trans_m := by
    intro T U W h h'
    refine ⟨le_trans h.1 h'.1, fun ψ hψ => ?_⟩
    have hmm : somehow (somehow ψ) ∈ T.1 := h.2 _ (h'.2 ψ hψ)
    have hM : LaxND ([] : List PLLFormula)
        ((somehow (somehow ψ)).ifThen (somehow ψ)) :=
      .impIntro (.laxElim (φ := somehow ψ)
        (.iden (by simp)) (.iden (by simp)))
    exact T.2.1 _ (SDeriv.mp ⟨[], by simp, .of_nd hM⟩ (SDeriv.of_mem hmm))
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := h hw
  full_F {a T} hT :=
    T.2.1 _ ⟨[falsePLL], by simpa using hT,
      .of_nd (.falsoElim _ (.iden (by simp)))⟩

/-- The `obInv` world over a world. -/
def obInvW (T : Wld) : Wld :=
  ⟨obInv T.1, obInv_closed T.2.1, obInv_prime T.2.1 T.2.2⟩

theorem rm_obInvW (T : Wld) : canonU.Rm T (obInvW T) :=
  ⟨subset_obInv T.2.1, fun _ h => h⟩

/-- **The canonical model is mutually confluent** — witness `obInv` of
the `Rᵢ`-successor. -/
theorem canonU_confluent : MutuallyConfluent canonU := by
  intro T U V hm hi
  exact ⟨obInvW V, fun ψ hψ => hi (hm.2 ψ hψ), rm_obInvW V⟩

/-! ## Lindenbaum: prime extension avoiding a formula -/

theorem chain_finite {c : Set (Set PLLFormula)} (hc : IsChain (· ≤ ·) c)
    {V₀ : Set PLLFormula} (h₀ : V₀ ∈ c) :
    ∀ Γ : List PLLFormula, (∀ ψ ∈ Γ, ψ ∈ ⋃₀ c) →
      ∃ V ∈ c, ∀ ψ ∈ Γ, ψ ∈ V := by
  intro Γ
  induction Γ with
  | nil => exact fun _ => ⟨V₀, h₀, by simp⟩
  | cons φ Γ ih =>
      intro h
      obtain ⟨V, hV, hΓ⟩ := ih (fun ψ hψ => h ψ (by simp [hψ]))
      obtain ⟨W, hW, hφ⟩ := h φ (by simp)
      rcases eq_or_ne V W with rfl | hVW
      · exact ⟨V, hV, by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          exacts [hφ, hΓ ψ hψ]⟩
      rcases hc.total hV hW with hle | hle
      · exact ⟨W, hW, by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          exacts [hφ, hle (hΓ ψ hψ)]⟩
      · exact ⟨V, hV, by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          exacts [hle hφ, hΓ ψ hψ]⟩

/-- Every set not deriving `B` extends to a closed prime set still
avoiding `B` (Zorn; closure and primeness by maximality, primeness
through `SDeriv.or_elim`). -/
theorem prime_extension {S : Set PLLFormula} {B : PLLFormula}
    (h : ¬ SDeriv S B) :
    ∃ T : Wld, S ⊆ T.1 ∧ B ∉ T.1 := by
  have hchain : ∀ c ⊆ {V : Set PLLFormula | S ⊆ V ∧ ¬ SDeriv V B},
      IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {V : Set PLLFormula | S ⊆ V ∧ ¬ SDeriv V B},
        ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    refine ⟨⋃₀ c,
      ⟨fun ψ hψ => Set.mem_sUnion.mpr ⟨y, hy, (hcS hy).1 hψ⟩, ?_⟩,
      fun z hz => Set.subset_sUnion_of_mem hz⟩
    rintro ⟨Γ, hΓ, hd⟩
    obtain ⟨V, hV, hΓV⟩ := chain_finite hc hy Γ hΓ
    exact (hcS hV).2 ⟨Γ, hΓV, hd⟩
  obtain ⟨M, hM₀, hMmem, hMmax⟩ :=
    zorn_le_nonempty₀ {V : Set PLLFormula | S ⊆ V ∧ ¬ SDeriv V B} hchain S
      ⟨le_refl S, h⟩
  have hext : ∀ φ, φ ∉ M → SDeriv (insert φ M) B := by
    intro φ hφ
    by_contra hnd
    have hle : insert φ M ≤ M :=
      hMmax ⟨le_trans hM₀ (Set.subset_insert φ M), hnd⟩
        (Set.subset_insert φ M)
    exact hφ (hle (Set.mem_insert φ M))
  have hclosed : SClosed M := by
    intro φ hd
    by_contra hφ
    exact hMmem.2 ((SDeriv.deduction (hext φ hφ)).mp hd)
  have hprime : SPrime M := by
    intro A₁ A₂ hor
    by_contra hne
    rw [not_or] at hne
    exact hMmem.2 (SDeriv.or_elim (SDeriv.of_mem hor)
      (SDeriv.deduction (hext A₁ hne.1))
      (SDeriv.deduction (hext A₂ hne.2)))
  exact ⟨⟨M, hclosed, hprime⟩, hM₀,
    fun hB => hMmem.2 (SDeriv.of_mem hB)⟩

/-! ## The truth lemma -/

theorem truth : ∀ (φ : PLLFormula) (T : Wld),
    canonU.force T φ ↔ φ ∈ T.1 := by
  intro φ
  induction φ with
  | prop a => exact fun T => Iff.rfl
  | falsePLL => exact fun T => Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro T
      constructor
      · rintro ⟨h₁, h₂⟩
        exact T.2.1 _ (SDeriv.andI
          (SDeriv.of_mem ((ihφ T).mp h₁))
          (SDeriv.of_mem ((ihψ T).mp h₂)))
      · intro h
        exact ⟨(ihφ T).mpr (T.2.1 _ (SDeriv.andE₁ (SDeriv.of_mem h))),
          (ihψ T).mpr (T.2.1 _ (SDeriv.andE₂ (SDeriv.of_mem h)))⟩
  | or φ ψ ihφ ihψ =>
      intro T
      constructor
      · rintro (h | h)
        · exact T.2.1 _ (SDeriv.orI₁ (SDeriv.of_mem ((ihφ T).mp h)))
        · exact T.2.1 _ (SDeriv.orI₂ (SDeriv.of_mem ((ihψ T).mp h)))
      · intro h
        rcases T.2.2 _ _ h with h | h
        exacts [Or.inl ((ihφ T).mpr h), Or.inr ((ihψ T).mpr h)]
  | ifThen φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro hf
        by_contra hmem
        have hnd : ¬ SDeriv (insert φ T.1) ψ := by
          intro hd
          exact hmem (T.2.1 _ hd.deduction)
        obtain ⟨U, hTU, hψU⟩ := prime_extension hnd
        have hφU : φ ∈ U.1 := hTU (Set.mem_insert φ T.1)
        have hfU := hf U (le_trans (Set.subset_insert φ T.1) hTU)
          ((ihφ U).mpr hφU)
        exact hψU ((ihψ U).mp hfU)
      · intro h U hTU hφ
        exact (ihψ U).mpr (U.2.1 _ ((SDeriv.of_mem (hTU h)).mp
          (SDeriv.of_mem ((ihφ U).mp hφ))))
  | somehow φ ih =>
      intro T
      rw [force_somehow_iff_of_confluent canonU_confluent]
      constructor
      · rintro ⟨U, hRm, hU⟩
        exact hRm.2 φ ((ih U).mp hU)
      · intro h
        exact ⟨obInvW T, rm_obInvW T, (ih (obInvW T)).mpr h⟩

/-! ## Soundness, and the theorem -/

/-- Soundness of the extended system over mutually confluent models. -/
theorem derivU_sound {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivU Γ φ)
    {C : ConstraintModel} (hc : MutuallyConfluent C) (w : C.W)
    (hΓ : ∀ ψ ∈ Γ, C.force w ψ) : C.force w φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine soundness p C w ?_
  intro ψ hψ
  rcases List.mem_append.mp hψ with hψ | hψ
  · obtain ⟨A, B, rfl⟩ := hL ψ hψ
    exact force_somehow_or_dist_of_confluent hc w A B
  · exact hΓ ψ hψ

/-- **PLL + `◯(A∨B) ⊃ (◯A∨◯B)` is sound and complete for mutually
confluent constraint models** — the completeness side of the F&M
Theorem 4.5 correspondence, over the soundness side of
`PLLFrames.lean`. -/
theorem derivU_iff_confluent_valid {Γ : List PLLFormula} {φ : PLLFormula} :
    DerivU Γ φ ↔
      ∀ (C : ConstraintModel), MutuallyConfluent C →
        ∀ w : C.W, (∀ ψ ∈ Γ, C.force w ψ) → C.force w φ := by
  constructor
  · intro h C hc w hΓ
    exact derivU_sound h hc w hΓ
  · intro hval
    by_contra hnd
    have hS : ¬ SDeriv {ψ | ψ ∈ Γ} φ := by
      rintro ⟨Γ', hΓ', hd⟩
      exact hnd (hd.rename hΓ')
    obtain ⟨T, hΓT, hφT⟩ := prime_extension hS
    have hfT := hval canonU canonU_confluent T
      (fun ψ hψ => (truth ψ T).mpr (hΓT hψ))
    exact hφT ((truth φ T).mp hfT)

/-! ### Axiom audit — clean-classical (Zorn in `prime_extension`),
measured and pinned on creation (2026-07-19) -/

/--
info: 'PLLND.ConfluentU.derivU_iff_confluent_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms derivU_iff_confluent_valid

/--
info: 'PLLND.ConfluentU.canonU_confluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms canonU_confluent

/--
info: 'PLLND.ConfluentU.truth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms truth

end ConfluentU
end PLLND
