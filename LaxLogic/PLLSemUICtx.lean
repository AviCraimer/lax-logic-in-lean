import LaxLogic.PLLSemUI
import LaxLogic.PLLCtxCompleteness

/-!
# The constraint route vs the semantic quantifiers: the sandwich lemmas

Two candidate constructions of `∀p M` are on the table (2026-07-19):

* the **ladder route**: `∀p M` as a meet of generator instances —
  substitutions `M[p := χ]` at closed-fragment rungs `χ`, plus the
  frame-changing transforms `lowT`/`sideT` (`LaxLogic/PLLSemUI.lean`);
* the **constraint route**: translate `M` by a standard constraint `C`
  (each `◯ψ ↦ C[ψ^C]`, the TYPES-paper substitution `subC`), compute
  the IPC uniform interpolant of the box-free translation `M^C`, and
  read the value back.

This file proves the precise relation — the two routes agree exactly on
the substitution fragment, and every constraint-route value is
**sandwiched**:

    ξ^C  ⊢ᴵᴾᶜ  ∀ᴵᴾᶜp.(M^C)  ⊢ᴵᴾᶜ  (M[p := χ])^C     (all χ)

where `ξ` is any PLL lower bound of `M` (in particular the semantic
∀p-value, via `semAll_lower`), and dually on the ∃-side.  The IPC
quantifier is abstracted as a Pitts-style spec (`IsIPCAll`/`IsIPCEx`)
so the file needs no interpolant implementation; the packaged
quantifiers `forallP`/`existsP` of the box-free crown
(`uniform_interpolation_IPC`, wip tower) satisfy the spec and
instantiate everything.

Consequences, in order of appearance:

* `substND` — natural deduction is closed under atom substitution
  (derivation-level, no semantics);
* `subC_substP` — the **bridge**: translation commutes with
  substitution, `(M[p := χ])^C = (M^C)[p := χ^C]`, for `p`-free `C`;
* `ctxAll_ge_value` / `ctxEx_le_value` — the constraint route can only
  ever OVER-approximate `∀p` (and under-approximate `∃p`): the
  translated PLL value derives the IPC value;
* `ctxAll_le_instance` / `ctxEx_ge_instance` — the IPC value derives
  every translated substitution instance: the constraint route reaches
  AT LEAST the whole substitution part of the ladder route;
* `ctx_sandwich_all` / `ctx_sandwich_ex` — the packaged statements,
  with the spec-level hypotheses `IsSemAll`/`IsSemEx`.

The gap between the two sandwich bounds is therefore exactly the
frame-changing content of the ladder route (`lowT`/`sideT`): the
machine-checked witness is `M = ◯p ⊃ p` over the two-world chain,
where the translated value is `⊥` but the IPC value is `a1` (the
oracle-verified Peirce failure of the constraint-commutation
experiment, docs/semantic-ui-route.md §0(j)).  Equality for a single
frozen `C` is REFUTED there; the frame-relative repair and the
variant-constraint correspondence remain OPEN.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open Ctx

/-! ## Substitution through derivations -/

/-- Natural deduction is closed under substitution of a formula for an
atom: every rule is homomorphic because `substP` commutes with every
connective (including `◯`). -/
def substND (p : String) (χ : PLLFormula) :
    {Γ : List PLLFormula} → {φ : PLLFormula} →
    LaxND Γ φ → LaxND (Γ.map (substP p χ)) (substP p χ φ)
  | _, _, .iden h          => .iden (List.mem_map_of_mem h)
  | _, _, .falsoElim φ d   => .falsoElim (substP p χ φ) (substND p χ d)
  | _, _, .impIntro d      => .impIntro (substND p χ d)
  | _, _, .impElim d₁ d₂   => .impElim (substND p χ d₁) (substND p χ d₂)
  | _, _, .andIntro d₁ d₂  => .andIntro (substND p χ d₁) (substND p χ d₂)
  | _, _, .andElim1 d      => .andElim1 (substND p χ d)
  | _, _, .andElim2 d      => .andElim2 (substND p χ d)
  | _, _, .orIntro1 d      => .orIntro1 (substND p χ d)
  | _, _, .orIntro2 d      => .orIntro2 (substND p χ d)
  | _, _, .orElim d₀ d₁ d₂ => .orElim (substND p χ d₀) (substND p χ d₁) (substND p χ d₂)
  | _, _, .laxIntro d      => .laxIntro (substND p χ d)
  | _, _, .laxElim d₁ d₂   => .laxElim (substND p χ d₁) (substND p χ d₂)

/-! ## `p`-free constraints and the bridge lemma -/

/-- The atom `p` occurs nowhere in the constraint's `K,L` formulas. -/
def CtxPFree (p : String) (C : StdCtx) : Prop :=
  ∀ kl ∈ C, p ∉ kl.1.atoms ∧ p ∉ kl.2.atoms

/-- Substitution passes through a `p`-free constraint application. -/
theorem substP_applyC {p : String} {χ : PLLFormula} {C : StdCtx}
    (hC : CtxPFree p C) (x : PLLFormula) :
    substP p χ (applyC C x) = applyC C (substP p χ x) := by
  induction C with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hKL := hC (K, L) (List.mem_cons_self ..)
      simp only [applyC, basic, substP,
        substP_of_not_mem hKL.1, substP_of_not_mem hKL.2,
        ih (fun kl h => hC kl (List.mem_cons_of_mem _ h))]

/-- **The bridge**: constraint translation commutes with substitution,
`(M[p := χ])^C = (M^C)[p := χ^C]`, when `C` is `p`-free.  This is what
identifies the ladder route's substitution instances with IPC
instances of the translation. -/
theorem subC_substP {p : String} {χ : PLLFormula} {C : StdCtx}
    (hC : CtxPFree p C) :
    ∀ M, subC C (substP p χ M) = substP p (subC C χ) (subC C M)
  | .prop a => by
      by_cases h : a = p <;> simp [substP, subC, h]
  | .falsePLL => rfl
  | .and A B => by
      simp only [substP, subC, subC_substP hC A, subC_substP hC B]
  | .or A B => by
      simp only [substP, subC, subC_substP hC A, subC_substP hC B]
  | .ifThen A B => by
      simp only [substP, subC, subC_substP hC A, subC_substP hC B]
  | .somehow A => by
      simp only [substP, subC, subC_substP hC A, substP_applyC hC]

/-- Applying a `p`-free constraint to a `p`-free formula is `p`-free. -/
theorem applyC_pfree {p : String} {C : StdCtx} (hC : CtxPFree p C)
    {x : PLLFormula} (hx : p ∉ x.atoms) : p ∉ (applyC C x).atoms := by
  induction C with
  | nil => simp [applyC, truePLL, PLLFormula.atoms]
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hKL := hC (K, L) (List.mem_cons_self ..)
      have htl := ih (fun kl h => hC kl (List.mem_cons_of_mem _ h))
      simp only [applyC, basic]
      intro hmem
      rcases (by simpa using hmem :
          p ∈ K.atoms ∨ p ∈ x.atoms ∨ p ∈ L.atoms ∨ p ∈ (applyC tl x).atoms) with
        h | h | h | h
      · exact hKL.1 h
      · exact hx h
      · exact hKL.2 h
      · exact htl h

/-- Translating a `p`-free formula by a `p`-free constraint is `p`-free. -/
theorem subC_pfree {p : String} {C : StdCtx} (hC : CtxPFree p C) :
    ∀ {ξ : PLLFormula}, p ∉ ξ.atoms → p ∉ (subC C ξ).atoms
  | .prop a, h => by simpa [subC] using h
  | .falsePLL, h => by simp [subC]
  | .and A B, h => by
      have hA : p ∉ A.atoms := fun hm => h (by simp [hm])
      have hB : p ∉ B.atoms := fun hm => h (by simp [hm])
      simpa [subC] using
        (by simp [subC_pfree hC hA, subC_pfree hC hB] :
          ¬ (p ∈ (subC C A).atoms ∨ p ∈ (subC C B).atoms))
  | .or A B, h => by
      have hA : p ∉ A.atoms := fun hm => h (by simp [hm])
      have hB : p ∉ B.atoms := fun hm => h (by simp [hm])
      simpa [subC] using
        (by simp [subC_pfree hC hA, subC_pfree hC hB] :
          ¬ (p ∈ (subC C A).atoms ∨ p ∈ (subC C B).atoms))
  | .ifThen A B, h => by
      have hA : p ∉ A.atoms := fun hm => h (by simp [hm])
      have hB : p ∉ B.atoms := fun hm => h (by simp [hm])
      simpa [subC] using
        (by simp [subC_pfree hC hA, subC_pfree hC hB] :
          ¬ (p ∈ (subC C A).atoms ∨ p ∈ (subC C B).atoms))
  | .somehow A, h => by
      have hA : p ∉ A.atoms := fun hm => h (by simpa using hm)
      simpa [subC] using applyC_pfree hC (subC_pfree hC hA)

/-! ## The IPC quantifier specs, abstractly

Pitts-style universal properties on the box-free side, stated for an
arbitrary comparison class `P` (instantiated with `isIPL`).  Any
implementation of the IPC uniform interpolants satisfies them — in
particular the packaged `forallP`/`existsP` of the box-free crown
`uniform_interpolation_IPC` (wip tower), modulo the `G4c ↔ LaxND`
equivalence `G4c.equiv_nd`. -/

/-- `A` behaves as `∀ᴵᴾᶜp.X` against comparisons in `P`: it is a
`p`-free lower bound of `X`, and the greatest among `P`. -/
structure IsIPCAll (p : String) (P : PLLFormula → Prop) (X A : PLLFormula) : Prop where
  pfree : p ∉ A.atoms
  lower : Nonempty (LaxND [A] X)
  greatest : ∀ ψ, P ψ → p ∉ ψ.atoms → Nonempty (LaxND [ψ] X) →
    Nonempty (LaxND [ψ] A)

/-- `E` behaves as `∃ᴵᴾᶜp.X` against comparisons in `P`: it is a
`p`-free upper bound of `X`, and the least among `P`. -/
structure IsIPCEx (p : String) (P : PLLFormula → Prop) (X E : PLLFormula) : Prop where
  pfree : p ∉ E.atoms
  upper : Nonempty (LaxND [X] E)
  least : ∀ ψ, P ψ → p ∉ ψ.atoms → Nonempty (LaxND [X] ψ) →
    Nonempty (LaxND [E] ψ)

/-! ## The comparison: translated PLL value vs IPC value -/

/-- **∀-side lower bound (the constraint route over-approximates)**:
for any IPL, `p`-free constraint `C`, the translation of ANY `p`-free
PLL lower bound `ξ` of `M` derives the IPC ∀p-value of the translation
`M^C`.  With `ξ` the semantic value (via `semAll_lower`) this says the
constraint route can only ever land ON or ABOVE the translated true
value — never below. -/
theorem ctxAll_ge_value {p : String} {C : StdCtx} {M ξ A : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C)
    (hξp : p ∉ ξ.atoms) (hlow : Nonempty (LaxND [ξ] M))
    (hA : IsIPCAll p isIPL (subC C M) A) :
    Nonempty (LaxND [subC C ξ] A) := by
  obtain ⟨d⟩ := hlow
  exact hA.greatest _ (subC_isIPL hCipl ξ) (subC_pfree hCp hξp)
    ⟨translate C d⟩

/-- **∃-side upper bound (dual)**: the IPC ∃p-value of `M^C` derives
the translation of any `p`-free PLL upper bound of `M`. -/
theorem ctxEx_le_value {p : String} {C : StdCtx} {M ξ E : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C)
    (hξp : p ∉ ξ.atoms) (hup : Nonempty (LaxND [M] ξ))
    (hE : IsIPCEx p isIPL (subC C M) E) :
    Nonempty (LaxND [E] (subC C ξ)) := by
  obtain ⟨d⟩ := hup
  exact hE.least _ (subC_isIPL hCipl ξ) (subC_pfree hCp hξp)
    ⟨translate C d⟩

/-- **∀-side upper bound (the constraint route reaches the whole
substitution fragment)**: the IPC ∀p-value of `M^C` derives the
translation of EVERY substitution instance `M[p := χ]` — via the
bridge `(M[p := χ])^C = (M^C)[p := χ^C]` and substitution through the
derivation `A ⊢ M^C`. -/
theorem ctxAll_le_instance {p : String} {C : StdCtx} {M A : PLLFormula}
    (hCp : CtxPFree p C) (hA : IsIPCAll p isIPL (subC C M) A)
    (χ : PLLFormula) :
    Nonempty (LaxND [A] (subC C (substP p χ M))) := by
  rw [subC_substP hCp]
  obtain ⟨d⟩ := hA.lower
  have d' := substND p (subC C χ) d
  rw [List.map_cons, List.map_nil, substP_of_not_mem hA.pfree] at d'
  exact ⟨d'⟩

/-- **∃-side instance bound (dual)**: every translated substitution
instance derives the IPC ∃p-value of `M^C`. -/
theorem ctxEx_ge_instance {p : String} {C : StdCtx} {M E : PLLFormula}
    (hCp : CtxPFree p C) (hE : IsIPCEx p isIPL (subC C M) E)
    (χ : PLLFormula) :
    Nonempty (LaxND [subC C (substP p χ M)] E) := by
  rw [subC_substP hCp]
  obtain ⟨d⟩ := hE.upper
  have d' := substND p (subC C χ) d
  rw [List.map_cons, List.map_nil, substP_of_not_mem hE.pfree] at d'
  exact ⟨d'⟩

/-! ## The sandwich theorems, at the semantic specs -/

/-- **The ∀-sandwich**: if `ξ` is the semantic ∀p-value of `M`
(`IsSemAll`) and `A` is the IPC ∀p-value of the translation `M^C`,
then

    ξ^C ⊢ A   and   A ⊢ (M[p := χ])^C for every χ.

So the constraint route computes a value squeezed between the
translated semantic value and the translated substitution instances —
it agrees with the ladder route EXACTLY on the substitution fragment,
and the residual gap `A ⊬ ξ^C` (oracle-witnessed at `M = ◯p ⊃ p`) is
precisely the frame-changing content (`lowT`/`sideT`). -/
theorem ctx_sandwich_all {p : String} {C : StdCtx} {M ξ A : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C)
    (hval : IsSemAll p M ξ)
    (hA : IsIPCAll p isIPL (subC C M) A) :
    Nonempty (LaxND [subC C ξ] A) ∧
    ∀ χ, Nonempty (LaxND [A] (subC C (substP p χ M))) :=
  ⟨ctxAll_ge_value hCipl hCp hval.1 (semAll_lower hval) hA,
   fun χ => ctxAll_le_instance hCp hA χ⟩

/-- **The ∃-sandwich** (dual): with `ξ` the semantic ∃p-value and `E`
the IPC ∃p-value of `M^C`,

    (M[p := χ])^C ⊢ E for every χ,   and   E ⊢ ξ^C. -/
theorem ctx_sandwich_ex {p : String} {C : StdCtx} {M ξ E : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C)
    (hval : IsSemEx p M ξ)
    (hE : IsIPCEx p isIPL (subC C M) E) :
    (∀ χ, Nonempty (LaxND [subC C (substP p χ M)] E)) ∧
    Nonempty (LaxND [E] (subC C ξ)) :=
  ⟨fun χ => ctxEx_ge_instance hCp hE χ,
   ctxEx_le_value hCipl hCp hval.1 (semEx_upper hval) hE⟩

end SemUI
end PLLND
