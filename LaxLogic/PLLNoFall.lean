import LaxLogic.PLLConfluentComplete

/-!
# PCLL + `¬◯⊥`: the infallible extension, and its one-variable uniform interpolation

This file sets up the extension of PCLL (PLL plus the distribution scheme
`◯(A∨B) ⊃ (◯A∨◯B)`, system `ConfluentU.DerivU`) by the single axiom

    nobot  :=  ¬◯⊥

and proves, sorry-free:

1. **The system** (`DerivUNoFall`).  `DerivUNoFall Γ φ := DerivU (nobot :: Γ) φ`.
   Adding the single closed formula `¬◯⊥` as an axiom is the same as adding
   it as a persistent hypothesis: no rule of the calculus *restricts* its
   context (every premise context extends the conclusion's, so a hypothesis
   persists to every node of a derivation), and weakening, exchange and
   contraction are admissible via the membership-based `LaxND.rename`.  Two
   points carry the identification: there is no empty-context
   (necessitation-style) rule — the unit `laxIntro` applies under hypotheses
   — and `nobot` is variable-free, so the single-formula and scheme readings
   of the extension coincide (for an axiom with variables the hypothesis form
   would be strictly weaker than the substitution-closed extension).

2. **The variable-free collapse** (`varfree_dichotomy`): every variable-free
   formula is derivable or inconsistent — the variable-free fragment is
   `{⊥, ⊤}` up to interderivability.  In PLL and PCLL that fragment is
   infinite (`◯⊥` generates a Rieger–Nishimura-style ladder); the axiom
   `¬◯⊥` collapses it.  The proof is a structural induction in which the
   axiom is used exactly once, in the `◯`-case (`◯A ⊢ ◯⊥ ⊢ ⊥` for
   inconsistent `A`); the distribution scheme is never used, so the same
   proof applies verbatim to PLL + `¬◯⊥`.

3. **Uniform interpolation into the variable-free fragment** (`exUI`,
   `allUI`): every formula `φ` has a strongest variable-free consequence and
   a weakest variable-free antecedent (`⊤` or `⊥`, decided by consistency
   resp. derivability of `φ`).  For a **one-variable** `φ` these are the
   uniform interpolants `∃p.φ` and `∀p.φ` of the one-variable language,
   since the `p`-free formulas of that language are exactly the
   variable-free ones.  Against `p`-free formulas over *additional*
   variables the interpolation property is deliberately not asserted here —
   that is the ≥ 2-variable problem.

4. **Semantics**: `DerivUNoFall` is sound and complete for mutually
   confluent constraint models **with no fallible worlds**
   (`derivUNoFall_iff_infallible_valid`), by relativising the canonical
   model of `PLLConfluentComplete.lean` to the proper prime theories
   containing `nobot`.  The relativisation is cheap: `obInv` preserves both
   extra properties (`nobot ∈ obInv T` because `¬◯⊥ ⊢ ◯¬◯⊥` by the unit,
   `⊥ ∉ obInv T` because `◯⊥` together with `¬◯⊥` is inconsistent), and
   `prime_extension` needs no re-run because a theory avoiding a formula is
   automatically proper.

5. **Consistency** (`consistent`), via the one-world infallible model, and
   hence the non-triviality of the dichotomy.
-/

open PLLFormula

namespace PLLND
namespace NoFall

open ConfluentU

/-! ## 1. The system -/

/-- The axiom `¬◯⊥`, spelled with the abbreviations of `PLLFormula`
(`notPLL F = F ⊃ ⊥`). -/
def nobot : PLLFormula := notPLL (somehow falsePLL)

/-- Derivability in **PCLL + `¬◯⊥`**: `DerivU` with the axiom available as a
persistent hypothesis.  This is the axiomatic extension of PCLL by the single
formula `¬◯⊥` (see the header for why hypothesis form and axiom form
agree). -/
def DerivUNoFall (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  DerivU (nobot :: Γ) φ

namespace DerivUNoFall

theorem of_derivU {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivU Γ φ) :
    DerivUNoFall Γ φ :=
  h.rename fun _ hm => List.mem_cons_of_mem _ hm

theorem of_nd {Γ : List PLLFormula} {φ : PLLFormula} (p : LaxND Γ φ) :
    DerivUNoFall Γ φ :=
  of_derivU (DerivU.of_nd p)

theorem hyp {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) :
    DerivUNoFall Γ φ :=
  DerivU.hyp (List.mem_cons_of_mem _ h)

/-- The axiom. -/
theorem nobot_ax {Γ : List PLLFormula} : DerivUNoFall Γ nobot :=
  DerivU.hyp (List.mem_cons_self ..)

theorem mp {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h₁ : DerivUNoFall Γ (φ.ifThen ψ)) (h₂ : DerivUNoFall Γ φ) :
    DerivUNoFall Γ ψ :=
  DerivU.mp h₁ h₂

theorem unit {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivUNoFall Γ φ) :
    DerivUNoFall Γ (somehow φ) :=
  DerivU.unit h

theorem rename {Γ Γ' : List PLLFormula} {φ : PLLFormula}
    (H : ∀ ψ ∈ Γ, ψ ∈ Γ') (h : DerivUNoFall Γ φ) : DerivUNoFall Γ' φ := by
  refine DerivU.rename ?_ h
  intro ψ hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (H ψ hm)

theorem deduction {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h : DerivUNoFall (φ :: Γ) ψ) : DerivUNoFall Γ (φ.ifThen ψ) := by
  refine DerivU.deduction (DerivU.rename ?_ h)
  intro θ hm
  simp only [List.mem_cons] at hm ⊢
  tauto

theorem cut {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h₁ : DerivUNoFall Γ φ) (h₂ : DerivUNoFall (φ :: Γ) ψ) :
    DerivUNoFall Γ ψ :=
  mp (deduction h₂) h₁

theorem exfalso {Γ : List PLLFormula} (h : DerivUNoFall Γ falsePLL)
    (φ : PLLFormula) : DerivUNoFall Γ φ :=
  mp (of_nd (.impIntro (.falsoElim φ (.iden (List.mem_cons_self ..))))) h

end DerivUNoFall

/-! ## 2. The variable-free collapse -/

/-- Variable-free: no propositional variable (`prop`) occurs.  The constant
`⊥` — and hence `⊤` and negation — is allowed. -/
def VarFree : PLLFormula → Prop
  | .prop _ => False
  | .falsePLL => True
  | .and φ ψ => VarFree φ ∧ VarFree ψ
  | .or φ ψ => VarFree φ ∧ VarFree ψ
  | .ifThen φ ψ => VarFree φ ∧ VarFree ψ
  | .somehow φ => VarFree φ

theorem varFree_truePLL : VarFree truePLL := ⟨trivial, trivial⟩

/-- From `[ψ] ⊢ ⊥` and `Γ ⊢ ψ` conclude `Γ ⊢ ⊥`. -/
private theorem bot_of {Γ : List PLLFormula} {ψ : PLLFormula}
    (h₁ : DerivUNoFall [ψ] falsePLL) (h₂ : DerivUNoFall Γ ψ) :
    DerivUNoFall Γ falsePLL :=
  DerivUNoFall.mp ((DerivUNoFall.deduction h₁).rename (by simp)) h₂

private theorem and_intro {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h₁ : DerivUNoFall Γ φ) (h₂ : DerivUNoFall Γ ψ) :
    DerivUNoFall Γ (φ.and ψ) :=
  DerivUNoFall.mp (DerivUNoFall.mp (DerivUNoFall.of_nd
    (.impIntro (.impIntro (.andIntro (.iden (by simp)) (.iden (by simp))))))
    h₁) h₂

/-- `∨`-elimination into `⊥`, singleton-context form. -/
private theorem or_elim_bot {φ ψ : PLLFormula}
    (h₁ : DerivUNoFall [φ] falsePLL) (h₂ : DerivUNoFall [ψ] falsePLL) :
    DerivUNoFall [φ.or ψ] falsePLL := by
  have d₁ : DerivUNoFall [φ.or ψ] (φ.ifThen falsePLL) :=
    (DerivUNoFall.deduction h₁).rename (by simp)
  have d₂ : DerivUNoFall [φ.or ψ] (ψ.ifThen falsePLL) :=
    (DerivUNoFall.deduction h₂).rename (by simp)
  have base : DerivUNoFall [φ.or ψ]
      ((φ.ifThen falsePLL).ifThen ((ψ.ifThen falsePLL).ifThen falsePLL)) :=
    DerivUNoFall.of_nd (.impIntro (.impIntro (.orElim (φ := φ) (ψ := ψ)
      (.iden (by simp))
      (.impElim (φ := φ) (.iden (by simp)) (.iden (by simp)))
      (.impElim (φ := ψ) (.iden (by simp)) (.iden (by simp))))))
  exact (base.mp d₁).mp d₂

/-- `◯`-monotonicity into `◯⊥`, singleton-context form: from `[φ] ⊢ ⊥`
conclude `[◯φ] ⊢ ◯⊥`. -/
private theorem ob_bot_of {φ : PLLFormula} (h : DerivUNoFall [φ] falsePLL) :
    DerivUNoFall [somehow φ] (somehow falsePLL) := by
  have d : DerivUNoFall [somehow φ] (φ.ifThen falsePLL) :=
    (DerivUNoFall.deduction h).rename (by simp)
  have base : DerivUNoFall [somehow φ]
      ((φ.ifThen falsePLL).ifThen (somehow falsePLL)) :=
    DerivUNoFall.of_nd (.impIntro (.laxElim (φ := φ) (.iden (by simp))
      (.laxIntro (.impElim (φ := φ) (.iden (by simp)) (.iden (by simp))))))
  exact base.mp d

/-- **The variable-free collapse**: in PCLL + `¬◯⊥` every variable-free
formula is derivable or inconsistent.  The axiom is used exactly once, in the
`◯`-case; the distribution scheme is never used, so the statement holds for
PLL + `¬◯⊥` by the same proof. -/
theorem varfree_dichotomy : ∀ {A : PLLFormula}, VarFree A →
    DerivUNoFall [] A ∨ DerivUNoFall [A] falsePLL := by
  intro A hA
  induction A with
  | prop a => exact hA.elim
  | falsePLL => exact Or.inr (DerivUNoFall.hyp (by simp))
  | and φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := hA
      rcases ihφ hφ with h₁ | h₁
      · rcases ihψ hψ with h₂ | h₂
        · exact Or.inl (and_intro h₁ h₂)
        · exact Or.inr (bot_of h₂
            (DerivUNoFall.of_nd (.andElim2 (φ := φ) (.iden (by simp)))))
      · exact Or.inr (bot_of h₁
          (DerivUNoFall.of_nd (.andElim1 (ψ := ψ) (.iden (by simp)))))
  | or φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := hA
      rcases ihφ hφ with h₁ | h₁
      · exact Or.inl (DerivUNoFall.mp
          (DerivUNoFall.of_nd (.impIntro (.orIntro1 (.iden (by simp))))) h₁)
      · rcases ihψ hψ with h₂ | h₂
        · exact Or.inl (DerivUNoFall.mp
            (DerivUNoFall.of_nd (.impIntro (.orIntro2 (.iden (by simp))))) h₂)
        · exact Or.inr (or_elim_bot h₁ h₂)
  | ifThen φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := hA
      rcases ihψ hψ with h₂ | h₂
      · exact Or.inl (DerivUNoFall.deduction (h₂.rename (by simp)))
      · rcases ihφ hφ with h₁ | h₁
        · refine Or.inr (bot_of h₂ ?_)
          exact DerivUNoFall.mp (DerivUNoFall.hyp (by simp))
            (h₁.rename (by simp))
        · exact Or.inl (DerivUNoFall.deduction
            (DerivUNoFall.exfalso (h₁.rename (by simp)) ψ))
  | somehow φ ih =>
      rcases ih hA with h | h
      · exact Or.inl h.unit
      · -- `[◯φ] ⊢ ◯⊥`, then the axiom `¬◯⊥` gives `⊥`.
        exact Or.inr (DerivUNoFall.mp DerivUNoFall.nobot_ax (ob_bot_of h))

/-! ## 3. Uniform interpolation into the variable-free fragment -/

/-- **∃-side uniform interpolation, variable-free target** (the Pitts
specification, biconditional form): every `φ` has a variable-free consequence
`E` — namely `⊤` if `φ` is consistent and `⊥` if not — such that for every
variable-free `ψ`, `φ ⊢ ψ` iff `E ⊢ ψ`.  For one-variable `φ` this is the
uniform interpolant `∃p.φ` of the one-variable language (whose `p`-free
formulas are exactly the variable-free ones). -/
theorem exUI (φ : PLLFormula) :
    ∃ E, VarFree E ∧ DerivUNoFall [φ] E ∧
      ∀ ψ, VarFree ψ → (DerivUNoFall [φ] ψ ↔ DerivUNoFall [E] ψ) := by
  by_cases hc : DerivUNoFall [φ] falsePLL
  · refine ⟨falsePLL, trivial, hc, fun ψ _ => ⟨?_, ?_⟩⟩
    · exact fun _ => DerivUNoFall.exfalso (DerivUNoFall.hyp (by simp)) ψ
    · exact fun h => hc.cut (h.rename (by simp))
  · refine ⟨truePLL, varFree_truePLL,
      DerivUNoFall.of_nd (.impIntro (.iden (by simp))), ?_⟩
    intro ψ hψ
    constructor
    · intro hd
      rcases varfree_dichotomy hψ with h | h
      · exact h.rename (by simp)
      · exact absurd (bot_of h hd) hc
    · intro h
      have hτ : DerivUNoFall [φ] truePLL :=
        DerivUNoFall.of_nd (.impIntro (.iden (by simp)))
      exact hτ.cut (h.rename (by simp))

/-- **∀-side uniform interpolation, variable-free target** (the Pitts
specification, biconditional form): every `φ` has a variable-free antecedent
`A` — namely `⊤` if `φ` is derivable and `⊥` if not — such that for every
variable-free `ψ`, `ψ ⊢ φ` iff `ψ ⊢ A`.  For one-variable `φ` this is the
uniform interpolant `∀p.φ` of the one-variable language. -/
theorem allUI (φ : PLLFormula) :
    ∃ A, VarFree A ∧ DerivUNoFall [A] φ ∧
      ∀ ψ, VarFree ψ → (DerivUNoFall [ψ] φ ↔ DerivUNoFall [ψ] A) := by
  by_cases hd : DerivUNoFall [] φ
  · refine ⟨truePLL, varFree_truePLL, hd.rename (by simp), fun ψ _ => ⟨?_, ?_⟩⟩
    · exact fun _ => DerivUNoFall.of_nd (.impIntro (.iden (by simp)))
    · exact fun _ => hd.rename (by simp)
  · refine ⟨falsePLL, trivial,
      DerivUNoFall.exfalso (DerivUNoFall.hyp (by simp)) φ, ?_⟩
    intro ψ hψ
    constructor
    · intro hdψ
      rcases varfree_dichotomy hψ with h | h
      · exact absurd (h.cut hdψ) hd
      · exact h
    · intro h
      exact DerivUNoFall.exfalso h φ

/-! ## 4. Semantics: infallible confluent models -/

/-- No fallible worlds. -/
def Infallible (C : ConstraintModel) : Prop := C.F = ∅

/-- `¬◯⊥` is forced everywhere on an infallible model (this is
`force_not_somehow_false_of_F_empty` of `PLLFrames.lean`). -/
theorem force_nobot {C : ConstraintModel} (hC : Infallible C) (w : C.W) :
    C.force w nobot :=
  force_not_somehow_false_of_F_empty C hC w

/-- **Soundness** of PCLL + `¬◯⊥` over mutually confluent infallible
models. -/
theorem sound {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivUNoFall Γ φ)
    {C : ConstraintModel} (hc : MutuallyConfluent C) (hi : Infallible C)
    (w : C.W) (hΓ : ∀ ψ ∈ Γ, C.force w ψ) : C.force w φ := by
  refine derivU_sound h hc w ?_
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact force_nobot hi w
  · exact hΓ ψ hψ

/-- The one-world infallible model. -/
def unitModel : ConstraintModel where
  W := Unit
  Ri _ _ := True
  Rm _ _ := True
  F := ∅
  V _ := ∅
  refl_i _ := trivial
  trans_i _ _ := trivial
  refl_m _ := trivial
  trans_m _ _ := trivial
  sub_mi _ := trivial
  hered_F _ h := (Set.notMem_empty _ h).elim
  hered_V _ h := (Set.notMem_empty _ h).elim
  full_F h := (Set.notMem_empty _ h).elim

theorem unitModel_confluent : MutuallyConfluent unitModel :=
  fun _ _ => ⟨(), trivial, trivial⟩

theorem unitModel_infallible : Infallible unitModel := rfl

/-- **Consistency**: PCLL + `¬◯⊥` does not derive `⊥`, so the dichotomy is
not trivial. -/
theorem consistent : ¬ DerivUNoFall [] falsePLL := by
  intro h
  have hf := sound h unitModel_confluent unitModel_infallible ()
    (by intro ψ hψ; simp at hψ)
  exact Set.notMem_empty _ hf

/-! ## 5. Completeness: the relativised canonical model

Worlds are the closed prime **proper** theories **containing `nobot`**; the
relations, valuation and confluence witness are those of `canonU`, restricted.
-/

/-- Worlds of the relativised canonical model. -/
def NWld : Type :=
  {T : Set PLLFormula //
    SClosed T ∧ SPrime T ∧ nobot ∈ T ∧ falsePLL ∉ T}

theorem nobot_mem_obInv {T : Set PLLFormula} (hc : SClosed T)
    (hn : nobot ∈ T) : nobot ∈ obInv T :=
  hc _ ((SDeriv.of_mem hn).unit)

theorem bot_not_mem_obInv {T : Set PLLFormula} (hc : SClosed T)
    (hn : nobot ∈ T) (hb : falsePLL ∉ T) : falsePLL ∉ obInv T :=
  fun h => hb (hc _ ((SDeriv.of_mem hn).mp (SDeriv.of_mem h)))

/-- The relativised canonical model: `canonU` restricted to the proper prime
theories containing `nobot`, with the fallible set empty. -/
@[reducible] def canonN : ConstraintModel where
  W := NWld
  Ri T U := T.1 ⊆ U.1
  Rm T U := T.1 ⊆ U.1 ∧ ∀ ψ ∈ U.1, somehow ψ ∈ T.1
  F := ∅
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
  hered_F _ hw := (Set.notMem_empty _ hw).elim
  hered_V h hw := h hw
  full_F hT := (Set.notMem_empty _ hT).elim

/-- The `obInv` world over a relativised world: closure, primeness, `nobot`
and properness all transfer. -/
def obInvNW (T : NWld) : NWld :=
  ⟨obInv T.1, obInv_closed T.2.1, obInv_prime T.2.1 T.2.2.1,
    nobot_mem_obInv T.2.1 T.2.2.2.1,
    bot_not_mem_obInv T.2.1 T.2.2.2.1 T.2.2.2.2⟩

theorem rm_obInvNW (T : NWld) : canonN.Rm T (obInvNW T) :=
  ⟨subset_obInv T.2.1, fun _ h => h⟩

theorem canonN_confluent : MutuallyConfluent canonN := by
  intro T U V hm hi
  exact ⟨obInvNW V, fun ψ hψ => hi (hm.2 ψ hψ), rm_obInvNW V⟩

theorem canonN_infallible : Infallible canonN := rfl

/-- Relativised Lindenbaum: a set containing `nobot` and not deriving `B`
extends to a **relativised** world avoiding `B`.  No new Zorn argument:
`prime_extension` already returns a theory that avoids `B`, hence is proper
(`⊥ ∈ T` would give `B ∈ T` by `falsoElim` and closure). -/
theorem prime_extension_N {S : Set PLLFormula} {B : PLLFormula}
    (hS : nobot ∈ S) (h : ¬ SDeriv S B) :
    ∃ T : NWld, S ⊆ T.1 ∧ B ∉ T.1 := by
  obtain ⟨T, hST, hBT⟩ := prime_extension h
  refine ⟨⟨T.1, T.2.1, T.2.2, hST hS, fun hb => hBT (T.2.1 _ ?_)⟩, hST, hBT⟩
  exact ⟨[falsePLL], by simpa using hb,
    .of_nd (.falsoElim B (.iden (by simp)))⟩

/-- The truth lemma for the relativised model. -/
theorem truthN : ∀ (φ : PLLFormula) (T : NWld),
    canonN.force T φ ↔ φ ∈ T.1 := by
  intro φ
  induction φ with
  | prop a => exact fun T => Iff.rfl
  | falsePLL =>
      intro T
      constructor
      · exact fun h => (Set.notMem_empty _ h).elim
      · exact fun h => (T.2.2.2.2 h).elim
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
        rcases T.2.2.1 _ _ h with h | h
        exacts [Or.inl ((ihφ T).mpr h), Or.inr ((ihψ T).mpr h)]
  | ifThen φ ψ ihφ ihψ =>
      intro T
      constructor
      · intro hf
        by_contra hmem
        have hnd : ¬ SDeriv (insert φ T.1) ψ := by
          intro hd
          exact hmem (T.2.1 _ hd.deduction)
        obtain ⟨U, hTU, hψU⟩ := prime_extension_N
          (Set.mem_insert_of_mem _ T.2.2.2.1) hnd
        have hφU : φ ∈ U.1 := hTU (Set.mem_insert φ T.1)
        have hfU := hf U (le_trans (Set.subset_insert φ T.1) hTU)
          ((ihφ U).mpr hφU)
        exact hψU ((ihψ U).mp hfU)
      · intro h U hTU hφ
        exact (ihψ U).mpr (U.2.1 _ ((SDeriv.of_mem (hTU h)).mp
          (SDeriv.of_mem ((ihφ U).mp hφ))))
  | somehow φ ih =>
      intro T
      rw [force_somehow_iff_of_confluent canonN_confluent]
      constructor
      · rintro ⟨U, hRm, hU⟩
        exact hRm.2 φ ((ih U).mp hU)
      · intro h
        exact ⟨obInvNW T, rm_obInvNW T, (ih (obInvNW T)).mpr h⟩

/-- **PCLL + `¬◯⊥` is sound and complete for mutually confluent infallible
constraint models.** -/
theorem derivUNoFall_iff_infallible_valid {Γ : List PLLFormula}
    {φ : PLLFormula} :
    DerivUNoFall Γ φ ↔
      ∀ (C : ConstraintModel), MutuallyConfluent C → Infallible C →
        ∀ w : C.W, (∀ ψ ∈ Γ, C.force w ψ) → C.force w φ := by
  constructor
  · intro h C hc hi w hΓ
    exact sound h hc hi w hΓ
  · intro hval
    by_contra hnd
    have hS : ¬ SDeriv {ψ | ψ ∈ nobot :: Γ} φ := by
      rintro ⟨Γ', hΓ', hd⟩
      exact hnd (hd.rename hΓ')
    obtain ⟨T, hΓT, hφT⟩ := prime_extension_N (List.mem_cons_self ..) hS
    have hfT := hval canonN canonN_confluent canonN_infallible T
      (fun ψ hψ => (truthN ψ T).mpr (hΓT (List.mem_cons_of_mem _ hψ)))
    exact hφT ((truthN φ T).mp hfT)

end NoFall
end PLLND

/-! ### Axiom audit — clean-classical, measured and pinned on creation
(2026-07-27); `consistent` needs `propext` only. -/

/-- info: 'PLLND.NoFall.varfree_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.varfree_dichotomy

/-- info: 'PLLND.NoFall.exUI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.exUI

/-- info: 'PLLND.NoFall.allUI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.allUI

/-- info: 'PLLND.NoFall.consistent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.NoFall.consistent

/-- info: 'PLLND.NoFall.derivUNoFall_iff_infallible_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.derivUNoFall_iff_infallible_valid
