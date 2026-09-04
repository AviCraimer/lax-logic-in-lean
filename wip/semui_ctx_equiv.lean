import LaxLogic.PLLSemUICtx
import LaxLogic.PLLG4HComp
import final

/-!
# Instantiating the sandwich: the packaged IPC quantifiers satisfy the spec

`LaxLogic/PLLSemUICtx.lean` proves the constraint-route sandwich against
an ABSTRACT Pitts-style spec (`IsIPCAll`/`IsIPCEx`).  This file closes
the loop with the box-free crown `uniform_interpolation_IPC`
(`wip/final.lean`, sorryAx-free): the packaged quantifiers
`forallP p X` / `existsP p X` satisfy the spec for box-free `X`, so the
sandwich holds with the CONCRETE tower interpolants — the very objects
the constraint-commutation probe computes.

Build (tower oleans assumed in `.lake/wipdeps`, including `final.olean`):

    lake env sh -c 'LEAN_PATH="$LEAN_PATH:$PWD/.lake/wipdeps" lean wip/semui_ctx_equiv.lean'

Axiom audits at the end: everything ≤ [propext, Classical.choice,
Quot.sound] — the box-free route never touches the `◯`-band holdout
`cascade_low_pos`.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open Ctx

/-! ## `boxFree` = `isIPL` (two spellings of "no ◯") -/

theorem isIPL_of_boxFree : ∀ {φ : PLLFormula}, boxFree φ → isIPL φ
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .and _ _, h => ⟨isIPL_of_boxFree h.1, isIPL_of_boxFree h.2⟩
  | .or _ _, h => ⟨isIPL_of_boxFree h.1, isIPL_of_boxFree h.2⟩
  | .ifThen _ _, h => ⟨isIPL_of_boxFree h.1, isIPL_of_boxFree h.2⟩

theorem boxFree_of_isIPL : ∀ {φ : PLLFormula}, isIPL φ → boxFree φ
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .and _ _, h => ⟨boxFree_of_isIPL h.1, boxFree_of_isIPL h.2⟩
  | .or _ _, h => ⟨boxFree_of_isIPL h.1, boxFree_of_isIPL h.2⟩
  | .ifThen _ _, h => ⟨boxFree_of_isIPL h.1, boxFree_of_isIPL h.2⟩

/-! ## The packaged quantifiers satisfy the abstract specs -/

/-- `forallP p X` is an `IsIPCAll`-value for box-free `X` (crown ∀-half
+ `G4c ↔ LaxND`). -/
theorem forallP_isIPCAll (p : String) {X : PLLFormula} (hX : boxFree X) :
    IsIPCAll p isIPL X (forallP p X) := by
  obtain ⟨_, hpf, hsound, hadeq⟩ :=
    (uniform_interpolation_IPC p .falsePLL X trivial hX)
  exact
    { pfree := hpf
      lower := G4c.equiv_nd.mp hsound
      greatest := fun ψ hψ hp h =>
        G4c.equiv_nd.mp (hadeq ψ (boxFree_of_isIPL hψ) hp (G4c.equiv_nd.mpr h)) }

/-- `existsP p X` is an `IsIPCEx`-value for box-free `X` (crown ∃-half
+ `G4c ↔ LaxND`). -/
theorem existsP_isIPCEx (p : String) {X : PLLFormula} (hX : boxFree X) :
    IsIPCEx p isIPL X (existsP p X) := by
  obtain ⟨⟨hpf, hsound, hadeq⟩, _⟩ :=
    (uniform_interpolation_IPC p X .falsePLL hX trivial)
  exact
    { pfree := hpf
      upper := G4c.equiv_nd.mp hsound
      least := fun ψ hψ hp h =>
        G4c.equiv_nd.mp (hadeq ψ (boxFree_of_isIPL hψ) hp (G4c.equiv_nd.mpr h)) }

/-! ## The sandwich, concretely -/

/-- **∀-sandwich, concrete**: for an IPL `p`-free constraint `C` and
the semantic ∀p-value `ξ` of `M`,

    ξ^C ⊢ ∀ᴵᴾᶜp.(M^C)   and   ∀ᴵᴾᶜp.(M^C) ⊢ (M[p := χ])^C  (all χ)

with `∀ᴵᴾᶜp` the PACKAGED tower quantifier `forallP` — the object the
constraint-commutation probe computes. -/
theorem ctx_sandwich_all_forallP {p : String} {C : StdCtx} {M ξ : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C) (hval : IsSemAll p M ξ) :
    Nonempty (LaxND [subC C ξ] (forallP p (subC C M))) ∧
    ∀ χ, Nonempty (LaxND [forallP p (subC C M)] (subC C (substP p χ M))) :=
  ctx_sandwich_all hCipl hCp hval
    (forallP_isIPCAll p (boxFree_of_isIPL (subC_isIPL hCipl M)))

/-- **∃-sandwich, concrete** (dual). -/
theorem ctx_sandwich_ex_existsP {p : String} {C : StdCtx} {M ξ : PLLFormula}
    (hCipl : CtxIsIPL C) (hCp : CtxPFree p C) (hval : IsSemEx p M ξ) :
    (∀ χ, Nonempty (LaxND [subC C (substP p χ M)] (existsP p (subC C M)))) ∧
    Nonempty (LaxND [existsP p (subC C M)] (subC C ξ)) :=
  ctx_sandwich_ex hCipl hCp hval
    (existsP_isIPCEx p (boxFree_of_isIPL (subC_isIPL hCipl M)))

/-! ## Axiom audits -/

/--
info: 'PLLND.SemUI.ctx_sandwich_all_forallP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ctx_sandwich_all_forallP

/--
info: 'PLLND.SemUI.ctx_sandwich_ex_existsP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ctx_sandwich_ex_existsP

end SemUI
end PLLND
