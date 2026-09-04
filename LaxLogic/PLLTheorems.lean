import LaxLogic.PLLConsequence

/-!
# Proof-theoretic results for PLL (F&M §2)

Over the slime-free system `PLLND.LaxND`:

* the Deduction Theorem (F&M Proposition 2.2) — one line each way, because
  natural deduction internalises it;
* the `◯`-theorem zoo: functoriality `(M ⊃ N) ⊃ (◯M ⊃ ◯N)`, and the three
  Hilbert axioms `◯R`, `◯M`, `◯S`;
* **Strong Extensionality** (F&M Theorem 2.5): the scheme
  `(M ≡ N) ⊃ (C[M] ≡ C[N])` for an arbitrary syntactic context `C[·]`,
  realised as substitution for a propositional constant.
-/

open PLLFormula

namespace PLLND

/-- Internal equivalence `M ≡ N`. -/
abbrev iffPLL (M N : PLLFormula) : PLLFormula := (M.ifThen N).and (N.ifThen M)

/-! ### Deduction theorem (F&M Proposition 2.2) -/

/-- Deduction theorem, both directions.  In the Hilbert presentation this
needs an induction (F&M Prop. 2.2); natural deduction internalises it. -/
theorem deduction_iff {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Nonempty (LaxND (φ :: Γ) ψ) ↔ Nonempty (LaxND Γ (φ.ifThen ψ)) :=
  ⟨fun ⟨p⟩ => ⟨.impIntro p⟩,
   fun ⟨p⟩ => ⟨.impElim (p.weaken φ) (.iden (.head _))⟩⟩

/-! ### The `◯`-theorem zoo -/

/-- `◯R` (the unit): `⊢ M ⊃ ◯M`. -/
def somehowR (Γ : List PLLFormula) (M : PLLFormula) :
    LaxND Γ (M.ifThen (.somehow M)) :=
  OI Γ M

/-- `◯M` (the multiplication): `⊢ ◯◯M ⊃ ◯M`. -/
def somehowM (Γ : List PLLFormula) (M : PLLFormula) :
    LaxND Γ ((somehow (somehow M)).ifThen (.somehow M)) :=
  OM Γ M

/-- `◯S` (the strength): `⊢ (◯M ∧ ◯N) ⊃ ◯(M ∧ N)`. -/
def somehowS (Γ : List PLLFormula) (M N : PLLFormula) :
    LaxND Γ ((and (somehow M) (somehow N)).ifThen (.somehow (M.and N))) :=
  OSR Γ M N

/-- Functoriality of `◯` as an internal theorem:
`⊢ (M ⊃ N) ⊃ (◯M ⊃ ◯N)`.  (F&M derive this from `◯R`, `◯M`, `◯S`; in
natural deduction it is a direct combination of the two lax rules.) -/
def somehowFunctor (Γ : List PLLFormula) (M N : PLLFormula) :
    LaxND Γ ((M.ifThen N).ifThen ((somehow M).ifThen (somehow N))) :=
  .impIntro <| .impIntro <|
    .laxElim (.iden (.head _))
      (.laxIntro (.impElim
        (.iden (.tail _ (.tail _ (.head _))))
        (.iden (.head _))))

/-! ### Strong extensionality (F&M Theorem 2.5)

A "syntactic context `C[·]`" is a formula `C` with a designated
propositional constant `a` marking the hole; `C[M]` is substitution
`substProp a M C`. -/

/-- Substitute `M` for the propositional constant `a`. -/
def substProp (a : String) (M : PLLFormula) : PLLFormula → PLLFormula
  | .prop b => if b = a then M else .prop b
  | .falsePLL => .falsePLL
  | .and φ ψ => .and (substProp a M φ) (substProp a M ψ)
  | .or φ ψ => .or (substProp a M φ) (substProp a M ψ)
  | .ifThen φ ψ => .ifThen (substProp a M φ) (substProp a M ψ)
  | .somehow φ => .somehow (substProp a M φ)

namespace SetDeriv

variable {Γ : Set PLLFormula}

theorem andI {φ ψ : PLLFormula} (h₁ : Γ ⊩ φ) (h₂ : Γ ⊩ ψ) : Γ ⊩ φ.and ψ :=
  map₂ (fun p₁ p₂ => .andIntro p₁ p₂) h₁ h₂

theorem andE1 {φ ψ : PLLFormula} (h : Γ ⊩ φ.and ψ) : Γ ⊩ φ :=
  map (fun p => .andElim1 p) h

theorem andE2 {φ ψ : PLLFormula} (h : Γ ⊩ φ.and ψ) : Γ ⊩ ψ :=
  map (fun p => .andElim2 p) h

/-- `≡` is reflexive. -/
theorem iff_refl (φ : PLLFormula) : Γ ⊩ iffPLL φ φ :=
  andI (deduct (of_mem (Set.mem_insert ..))) (deduct (of_mem (Set.mem_insert ..)))

/-- Congruence of `≡` for a binary connective, given the two implications
are compatible with it argument-wise.  Used via the three instances below. -/
theorem iff_congr₂ {P P' Q Q' : PLLFormula}
    (conn : PLLFormula → PLLFormula → PLLFormula)
    (compat : ∀ {Δ : Set PLLFormula} {X X' Y Y' : PLLFormula},
      Δ ⊩ iffPLL X X' → Δ ⊩ iffPLL Y Y' → Δ ⊩ (conn X Y).ifThen (conn X' Y'))
    (h₁ : Γ ⊩ iffPLL P P') (h₂ : Γ ⊩ iffPLL Q Q') :
    Γ ⊩ iffPLL (conn P Q) (conn P' Q') := by
  refine andI (compat h₁ h₂) (compat ?_ ?_)
  · exact andI (andE2 h₁) (andE1 h₁)
  · exact andI (andE2 h₂) (andE1 h₂)

theorem iff_congr_and {P P' Q Q' : PLLFormula}
    (h₁ : Γ ⊩ iffPLL P P') (h₂ : Γ ⊩ iffPLL Q Q') :
    Γ ⊩ iffPLL (P.and Q) (P'.and Q') := by
  refine iff_congr₂ PLLFormula.and (fun {Δ X X' Y Y'} hX hY => deduct ?_) h₁ h₂
  have hXY : insert (X.and Y) Δ ⊩ X.and Y := of_mem (Set.mem_insert ..)
  have hX' : insert (X.and Y) Δ ⊩ iffPLL X X' :=
    mono (Set.subset_insert ..) hX
  have hY' : insert (X.and Y) Δ ⊩ iffPLL Y Y' :=
    mono (Set.subset_insert ..) hY
  exact andI (mp (andE1 hX') (andE1 hXY)) (mp (andE1 hY') (andE2 hXY))

theorem iff_congr_or {P P' Q Q' : PLLFormula}
    (h₁ : Γ ⊩ iffPLL P P') (h₂ : Γ ⊩ iffPLL Q Q') :
    Γ ⊩ iffPLL (P.or Q) (P'.or Q') := by
  refine iff_congr₂ PLLFormula.or (fun {Δ X X' Y Y'} hX hY => deduct ?_) h₁ h₂
  refine orE (of_mem (Set.mem_insert ..)) ?_ ?_
  · refine orL _ (mp ?_ (of_mem (Set.mem_insert ..)))
    exact mono ((Set.subset_insert ..).trans (Set.subset_insert ..)) (andE1 hX)
  · refine orR _ (mp ?_ (of_mem (Set.mem_insert ..)))
    exact mono ((Set.subset_insert ..).trans (Set.subset_insert ..)) (andE1 hY)

theorem iff_congr_imp {P P' Q Q' : PLLFormula}
    (h₁ : Γ ⊩ iffPLL P P') (h₂ : Γ ⊩ iffPLL Q Q') :
    Γ ⊩ iffPLL (P.ifThen Q) (P'.ifThen Q') := by
  refine iff_congr₂ PLLFormula.ifThen
    (fun {Δ X X' Y Y'} hX hY => deduct (deduct ?_)) h₁ h₂
  -- context:  X', X ⊃ Y, Δ  ⊢  Y'   (note `⊃` is contravariant on the left)
  have hX'w : insert X' (insert (X.ifThen Y) Δ) ⊩ X := by
    refine mp ?_ (of_mem (Set.mem_insert ..))
    exact mono ((Set.subset_insert ..).trans (Set.subset_insert ..)) (andE2 hX)
  have hY₀ : insert X' (insert (X.ifThen Y) Δ) ⊩ Y :=
    mp (of_mem (Set.mem_insert_of_mem _ (Set.mem_insert ..))) hX'w
  refine mp ?_ hY₀
  exact mono ((Set.subset_insert ..).trans (Set.subset_insert ..)) (andE1 hY)

theorem iff_congr_somehow {P P' : PLLFormula}
    (h : Γ ⊩ iffPLL P P') : Γ ⊩ iffPLL (somehow P) (somehow P') := by
  have half : ∀ {X X' : PLLFormula}, Γ ⊩ iffPLL X X' →
      Γ ⊩ (somehow X).ifThen (somehow X') := by
    intro X X' hX
    refine deduct ?_
    refine somehow_mono (of_mem (Set.mem_insert ..)) ?_
    exact mp
      (mono ((Set.subset_insert ..).trans (Set.subset_insert ..)) (andE1 hX))
      (of_mem (Set.mem_insert ..))
  exact andI (half h) (half (andI (andE2 h) (andE1 h)))

end SetDeriv

open SetDeriv in
/-- **Strong extensionality** (F&M Theorem 2.5), set-level core:
from `M ≡ N` conclude `C[M] ≡ C[N]` for any context `C`. -/
theorem extensionality_setDeriv (a : String) (M N : PLLFormula) :
    ∀ C : PLLFormula,
      ({iffPLL M N} : Set PLLFormula) ⊩ iffPLL (substProp a M C) (substProp a N C)
  | .prop b => by
      by_cases h : b = a
      · simp only [substProp, if_pos h]
        exact of_mem rfl
      · simp only [substProp, if_neg h]
        exact iff_refl (.prop b)
  | .falsePLL => iff_refl _
  | .and φ ψ =>
      iff_congr_and (extensionality_setDeriv a M N φ) (extensionality_setDeriv a M N ψ)
  | .or φ ψ =>
      iff_congr_or (extensionality_setDeriv a M N φ) (extensionality_setDeriv a M N ψ)
  | .ifThen φ ψ =>
      iff_congr_imp (extensionality_setDeriv a M N φ) (extensionality_setDeriv a M N ψ)
  | .somehow φ =>
      iff_congr_somehow (extensionality_setDeriv a M N φ)

/-- **Strong extensionality** (F&M Theorem 2.5), schematic form:
`⊢ (M ≡ N) ⊃ (C[M] ≡ C[N])`. -/
theorem strong_extensionality (a : String) (M N C : PLLFormula) :
    Nonempty (LaxND [] ((iffPLL M N).ifThen
      (iffPLL (substProp a M C) (substProp a N C)))) := by
  have h1 : insert (iffPLL M N) (∅ : Set PLLFormula) ⊩
      iffPLL (substProp a M C) (substProp a N C) := by
    refine SetDeriv.mono ?_ (extensionality_setDeriv a M N C)
    intro x hx
    exact Set.mem_insert_iff.mpr (.inl hx)
  obtain ⟨L, hL, ⟨p⟩⟩ := SetDeriv.deduct h1
  have hnil : L = [] := by
    cases L with
    | nil => rfl
    | cons ψ L => exact absurd (hL ψ (List.mem_cons_self ..)) (by simp)
  subst hnil
  exact ⟨p⟩

end PLLND
