import LaxLogic.PLLSearch
import LaxLogic.PLLSemUIFrag
import LaxLogic.PLLG4HComp

/-!
# `nfcorrect` — the search normaliser is a PLL equivalence

`PLLND.Search.nf` (`LaxLogic/PLLSearch.lean` §0) is the bottom-up pass of
Heyting `⊥`/`⊤` laws plus `◯⊤ ≡ ⊤`, `◯◯ ≡ ◯` that shrinks formulas before
the untrusted stages of `PLLND.Search`.  Inside the search its correctness
is *irrelevant* — every certificate is re-checked against the original
sequent — but outside it, `nf` is what makes large machine-computed
formulas legible, and any verdict read off `nf φ` is a verdict about `φ`
only if `nf` is an equivalence.

This module proves that, with no side conditions:

    theorem smash_interd  : ∀ φ, Interd φ (smash φ)
    theorem nf_interd     : ∀ φ, Interd φ (nf φ)
    theorem nfIter_interd : ∀ n φ, Interd φ (nfIter n φ)

`nfIter` is the *total* form of the fixpoint iteration that consumers run
(`wip/towertest.lean`'s `partial def nfStar`): `nfIter n` is `n` passes of
`nf`, and each pass composes by `Interd.trans`.

The last section records the transfer rules the consumers actually use: a
certificate about `nf φ` cuts down to one about `φ`, in either direction and
in either calculus.
-/

open PLLFormula
open PLLND.SemUI

namespace PLLND.SemUI

/-! ## Derivation helpers the fragment file does not carry -/

/-- `⊤` is derivable in every context. -/
theorem Deriv.top (Γ : List PLLFormula) : Deriv Γ truePLL :=
  Deriv.impIntro (Deriv.iden (.head _))

/-- `◯`-unit. -/
theorem Deriv.laxIntro {Γ : List PLLFormula} {φ : PLLFormula} :
    Deriv Γ φ → Deriv Γ (PLLFormula.somehow φ)
  | ⟨p⟩ => ⟨.laxIntro p⟩

/-- `◯`-elimination. -/
theorem Deriv.laxElim {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (PLLFormula.somehow φ) → Deriv (φ :: Γ) (PLLFormula.somehow ψ) →
    Deriv Γ (PLLFormula.somehow ψ)
  | ⟨p⟩, ⟨q⟩ => ⟨.laxElim p q⟩

end PLLND.SemUI

namespace PLLND.Search

/-! ## 1.  `isTop` recognises exactly `⊤` -/

theorem isTop_eq {A : PLLFormula} (h : isTop A = true) : A = truePLL := by
  unfold isTop at h
  split at h
  · rfl
  · exact absurd h (by simp)

/-! ## 2.  One layer: `smash` is an equivalence -/

theorem smash_interd : ∀ φ : PLLFormula, Interd φ (smash φ)
  | .prop _ => Interd.refl _
  | .falsePLL => Interd.refl _
  | .and A B => by
      simp only [smash]
      split_ifs with h1 h2 h3 h4
      · -- one conjunct is `⊥`
        simp only [Bool.or_eq_true, beq_iff_eq] at h1
        refine ⟨?_, Deriv.falsoElim _ (Deriv.iden (.head _))⟩
        rcases h1 with rfl | rfl
        · exact Deriv.andElim1 (Deriv.iden (.head _))
        · exact Deriv.andElim2 (Deriv.iden (.head _))
      · -- `A = ⊤`
        have hA := isTop_eq h2
        subst hA
        exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
          Deriv.andIntro (Deriv.top _) (Deriv.iden (.head _))⟩
      · -- `B = ⊤`
        have hA := isTop_eq h3
        subst hA
        exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
          Deriv.andIntro (Deriv.iden (.head _)) (Deriv.top _)⟩
      · -- `A = B`
        rw [beq_iff_eq] at h4
        subst h4
        exact ⟨Deriv.andElim1 (Deriv.iden (.head _)),
          Deriv.andIntro (Deriv.iden (.head _)) (Deriv.iden (.head _))⟩
      · exact Interd.refl _
  | .or A B => by
      simp only [smash]
      split_ifs with h1 h2 h3 h4
      · -- one disjunct is `⊤`
        simp only [Bool.or_eq_true] at h1
        refine ⟨Deriv.top _, ?_⟩
        rcases h1 with h | h
        · exact Deriv.orIntro1 (by rw [isTop_eq h]; exact Deriv.top _)
        · exact Deriv.orIntro2 (by rw [isTop_eq h]; exact Deriv.top _)
      · -- `A = ⊥`
        rw [beq_iff_eq] at h2
        subst h2
        exact ⟨Deriv.orElim (Deriv.iden (.head _))
            (Deriv.falsoElim _ (Deriv.iden (.head _))) (Deriv.iden (.head _)),
          Deriv.orIntro2 (Deriv.iden (.head _))⟩
      · -- `B = ⊥`
        rw [beq_iff_eq] at h3
        subst h3
        exact ⟨Deriv.orElim (Deriv.iden (.head _))
            (Deriv.iden (.head _)) (Deriv.falsoElim _ (Deriv.iden (.head _))),
          Deriv.orIntro1 (Deriv.iden (.head _))⟩
      · -- `A = B`
        rw [beq_iff_eq] at h4
        subst h4
        exact ⟨Deriv.orElim (Deriv.iden (.head _))
            (Deriv.iden (.head _)) (Deriv.iden (.head _)),
          Deriv.orIntro1 (Deriv.iden (.head _))⟩
      · exact Interd.refl _
  | .ifThen A B => by
      simp only [smash]
      split_ifs with h1 h2 h3
      · -- `A = ⊥`, or `B = ⊤`
        simp only [Bool.or_eq_true, beq_iff_eq] at h1
        refine ⟨Deriv.top _, ?_⟩
        rcases h1 with rfl | h
        · exact Deriv.impIntro (Deriv.falsoElim _ (Deriv.iden (.head _)))
        · exact Deriv.impIntro (by rw [isTop_eq h]; exact Deriv.top _)
      · -- `A = ⊤`
        have hA := isTop_eq h2
        subst hA
        exact ⟨Deriv.impElim (Deriv.iden (.head _)) (Deriv.top _),
          Deriv.impIntro (Deriv.iden (.tail _ (.head _)))⟩
      · -- `A = B`
        rw [beq_iff_eq] at h3
        subst h3
        exact ⟨Deriv.top _, Deriv.impIntro (Deriv.iden (.head _))⟩
      · exact Interd.refl _
  | .somehow A => by
      simp only [smash]
      split_ifs with h1
      · -- `◯⊤ ≡ ⊤`
        have hA := isTop_eq h1
        subst hA
        exact ⟨Deriv.top _, Deriv.laxIntro (Deriv.top _)⟩
      · cases A with
        | somehow B =>
            -- `◯◯B ≡ ◯B`
            exact ⟨Deriv.laxElim (Deriv.iden (.head _)) (Deriv.iden (.head _)),
              Deriv.laxIntro (Deriv.iden (.head _))⟩
        | prop _ => exact Interd.refl _
        | falsePLL => exact Interd.refl _
        | and _ _ => exact Interd.refl _
        | or _ _ => exact Interd.refl _
        | ifThen _ _ => exact Interd.refl _

/-! ## 3.  The recursive normaliser is an equivalence -/

/-- **`nf` is a PLL equivalence.**  Bottom-up: the four congruence rules of
`Interd` push the induction hypotheses through the constructor, and
`smash_interd` closes the root layer. -/
theorem nf_interd : ∀ φ : PLLFormula, Interd φ (nf φ)
  | .prop _ => Interd.refl _
  | .falsePLL => Interd.refl _
  | .and A B =>
      (Interd.and_congr (nf_interd A) (nf_interd B)).trans (smash_interd _)
  | .or A B =>
      (Interd.or_congr (nf_interd A) (nf_interd B)).trans (smash_interd _)
  | .ifThen A B =>
      (Interd.imp_congr (nf_interd A) (nf_interd B)).trans (smash_interd _)
  | .somehow A =>
      (Interd.box_congr (nf_interd A)).trans (smash_interd _)

/-! ## 4.  Iteration to the fixpoint

Consumers iterate `nf` until it stops changing the formula
(`wip/towertest.lean`'s `partial def nfStar`).  `nfIter n` is the total
`n`-pass form; any concrete fixpoint run is `nfIter k` for the `k` the
run reports. -/

/-- `n` passes of `nf`. -/
def nfIter : Nat → PLLFormula → PLLFormula
  | 0, φ => φ
  | n + 1, φ => nfIter n (nf φ)

/-- **Every finite iteration of `nf` is a PLL equivalence.** -/
theorem nfIter_interd : ∀ (n : Nat) (φ : PLLFormula), Interd φ (nfIter n φ)
  | 0, φ => Interd.refl φ
  | n + 1, φ => (nf_interd φ).trans (nfIter_interd n (nf φ))

/-! ## 5.  Transfer: an `nf`-level verdict is a verdict about the original

These are the cut rules a consumer needs.  Nothing here evaluates `nf`:
the certificate is a `G4c`/`Deriv` object *about the term* `nf φ`, and the
cut replaces it by one about `φ`. -/

/-- `nf φ ⊢ ψ` gives `φ ⊢ ψ`. -/
theorem deriv_of_nf {φ ψ : PLLFormula} (h : Deriv [nf φ] ψ) : Deriv [φ] ψ :=
  Deriv.cutHead (nf_interd φ).1 h

/-- `ψ ⊢ nf φ` gives `ψ ⊢ φ`. -/
theorem deriv_to_nf {φ ψ : PLLFormula} (h : Deriv [ψ] (nf φ)) : Deriv [ψ] φ :=
  Deriv.cutHead h (nf_interd φ).2

/-- The same, `n` passes deep. -/
theorem deriv_of_nfIter {n : Nat} {φ ψ : PLLFormula} (h : Deriv [nfIter n φ] ψ) :
    Deriv [φ] ψ :=
  Deriv.cutHead (nfIter_interd n φ).1 h

/-- The same, `n` passes deep. -/
theorem deriv_to_nfIter {n : Nat} {φ ψ : PLLFormula} (h : Deriv [ψ] (nfIter n φ)) :
    Deriv [ψ] φ :=
  Deriv.cutHead h (nfIter_interd n φ).2

/-- Interderivability read off the normal form is interderivability. -/
theorem interd_of_nf {φ ψ : PLLFormula} (h : Interd (nf φ) ψ) : Interd φ ψ :=
  (nf_interd φ).trans h

/-- The same, `n` passes deep. -/
theorem interd_of_nfIter {n : Nat} {φ ψ : PLLFormula} (h : Interd (nfIter n φ) ψ) :
    Interd φ ψ :=
  (nfIter_interd n φ).trans h

/-! ### Calculus form

`PLLND.Search`'s certificates come out as `G4c` objects; `G4c.equiv_nd`
(unconditional, `LaxLogic/PLLG4HComp.lean`) moves them across. -/

/-- `G4c [nf φ] ψ` gives `G4c [φ] ψ`. -/
theorem g4c_of_nf {φ ψ : PLLFormula} (h : G4c [nf φ] ψ) : G4c [φ] ψ :=
  G4c.equiv_nd.mpr (deriv_of_nf (G4c.equiv_nd.mp h))

/-- `G4c [ψ] (nf φ)` gives `G4c [ψ] φ`. -/
theorem g4c_to_nf {φ ψ : PLLFormula} (h : G4c [ψ] (nf φ)) : G4c [ψ] φ :=
  G4c.equiv_nd.mpr (deriv_to_nf (G4c.equiv_nd.mp h))

/-- `G4c [nfIter n φ] ψ` gives `G4c [φ] ψ`. -/
theorem g4c_of_nfIter {n : Nat} {φ ψ : PLLFormula} (h : G4c [nfIter n φ] ψ) :
    G4c [φ] ψ :=
  G4c.equiv_nd.mpr (deriv_of_nfIter (G4c.equiv_nd.mp h))

/-- `G4c [ψ] (nfIter n φ)` gives `G4c [ψ] φ`. -/
theorem g4c_to_nfIter {n : Nat} {φ ψ : PLLFormula} (h : G4c [ψ] (nfIter n φ)) :
    G4c [ψ] φ :=
  G4c.equiv_nd.mpr (deriv_to_nfIter (G4c.equiv_nd.mp h))

/-! ## 6.  Axiom audits -/

/-- info: 'PLLND.Search.smash_interd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms smash_interd

/-- info: 'PLLND.Search.nf_interd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nf_interd

/-- info: 'PLLND.Search.nfIter_interd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms nfIter_interd

/-- info: 'PLLND.Search.g4c_of_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms g4c_of_nf

end PLLND.Search
