import LaxLogic.PLLG4UITrunc
import absorb_base
import adequacy
import packaging
import indiff
import spaceindiff

/-!
# Final assembly — uniform interpolation for PLL, packaged and audited

This file discharges the two named hypothesis families of
`wip/packaging.lean` (hFI from `wip/indiff.lean`, hSI from
`wip/spaceindiff.lean`), instantiates Pitts condition (iv) and the
factorization corollaries hypothesis-free, and states the crown
theorem `uniform_interpolation_PLL` with pinned axiom audits.

## Assembly map

The tower, bottom to top (file — what it contributes):

* `LaxLogic/PLLG4UITrunc.lean` — base library: PLL formulas, `weight`,
  `atoms`, the sequent calculi `G4c`/`G4s`/`G4sh` with cut
  admissibility, the `defect`/`mu` measures, the truncated quantifier
  tables `itpE`/`itpA`, p-freeness `itp_pfree`, soundness `itp_sound`.
  Axiom-clean (no `sorryAx`).
* `wip/absorb_base.lean` — the `kcap` budget and the
  absorption/stabilization ladder up to `itp_stab_le` (budget
  monotonicity of the truncated quantifiers).  Contains **the single
  open kernel of the whole development**: `cascade_boxgoal_pos`
  (private), proved with `sorry` — the only point where `sorryAx`
  enters.  Round 4 (PROGRESS §60) replaced the former holdout
  `cascade_low_pos_box` by this strictly weaker `◯`-goal descent and
  deleted `cascade_low_pos`/`cascade_low` with it.
* `wip/adequacy.lean` — `PieceClosed` spaces and the sequent-level
  Pitts (iv): `itp_adequate`.  Sorry-free in itself; inherits
  `sorryAx` from `absorb_base` (see `itp_adequate_axiom_note` there).
* `wip/indiff.lean` — fuel indifference: above the recursion measure
  `mu`, the quantifiers are *syntactically equal* across fuels
  (`itp_indiff`, chained as `itpE_indiff_ge`/`itpA_indiff_ge`).
  Axiom-clean.
* `wip/spaceindiff.lean` — space indifference: two piece-closed spaces
  containing the closure of the data give equal quantifiers
  (`spaceIndiffE`/`spaceIndiffA` — packaging's hSI, verbatim).
  Axiom-clean.
* `wip/packaging.lean` — `pieceClosure`/`pieceClosureList` with the
  keystone `pieceClosed_pieceClosureList`; the uniform fuel `uiFuel`;
  the packaged quantifiers `existsP`/`forallP`; Pitts (i)–(iii)
  outright; (iv) and factorization modulo the named hypotheses
  `FuelIndiffE`/`FuelIndiffA` (hFI) and `SpaceIndiffE`/`SpaceIndiffA`
  (hSI).
* `wip/final.lean` (this file) — §1 discharges hFI (`fuelIndiffE`,
  `fuelIndiffA`) by bridging `uiFuel`'s weight-cap convention to
  `indiff`'s hypotheses; §2 bundles all four dischargers; §3 restates
  (iv) and the factorizations hypothesis-free; §4 the crown theorem;
  §5 pinned axiom audits.

## Build

Standalone oleans + `LEAN_PATH`, in dependency order (`<depdir>` is
the olean cache directory):

    lake env lean wip/absorb_base.lean -o <depdir>/absorb_base.olean
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/adequacy.lean -o <depdir>/adequacy.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/packaging.lean -o <depdir>/packaging.olean'
    lake env lean wip/indiff.lean -o <depdir>/indiff.olean
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/spaceindiff.lean -o <depdir>/spaceindiff.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/final.lean'
-/

open PLLFormula

namespace PLLND

/-! ### §1 Discharging hFI — the fuel-indifference hypotheses

`uiFuel S b slot Γ = mu S (S.sup weight + slot) b slot Γ + 1`, so the
weight cap is `W0 := S.sup weight + slot` (slot `0` on the E side,
`C.weight` on the A side).  `indiff`'s hypotheses then discharge:

* `S.sup weight ≤ W0` — arithmetic;
* the context cap `∀ F ∈ Γ, F.weight ≤ W0` — Γ-members lie in their
  own closure, hence in `pieceClosureList Γ ⊆ S`, hence their weight
  is at most `S.sup weight ≤ W0`;
* (A side) `C.weight ≤ W0` — arithmetic (`slot = C.weight`);
* `mu S W0 b slot Γ < f` — exactly `uiFuel S b slot Γ ≤ f` unfolded.
-/

/-- Γ-members of a space containing the context closure obey the
space's weight cap (shared bridging step of both dischargers). -/
private theorem cap_of_closure_subset {S : Finset PLLFormula}
    {Γ : List PLLFormula} (hsub : pieceClosureList Γ ⊆ S) {W0 : Nat}
    (hW : S.sup PLLFormula.weight ≤ W0) :
    ∀ F ∈ Γ, F.weight ≤ W0 := fun _ hF =>
  Nat.le_trans (Finset.le_sup (hsub (pieceClosureList_mem hF))) hW

/-- **hFI discharged (E side)**: packaging's `FuelIndiffE` holds. -/
theorem fuelIndiffE (p : String) : FuelIndiffE p := by
  intro S b Γ f f' _hPC hsub hf hf'
  unfold uiFuel at hf hf'
  exact itpE_indiff_ge p S (S.sup PLLFormula.weight + 0)
    (Nat.le_add_right _ 0)
    (cap_of_closure_subset hsub (Nat.le_add_right _ 0))
    (by omega) (by omega)

/-- **hFI discharged (A side)**: packaging's `FuelIndiffA` holds. -/
theorem fuelIndiffA (p : String) : FuelIndiffA p := by
  intro S b Γ C f f' _hPC hsubΓ _hsubC hf hf'
  unfold uiFuel at hf hf'
  exact itpA_indiff_ge p S (S.sup PLLFormula.weight + C.weight)
    (Nat.le_add_right _ _)
    (cap_of_closure_subset hsubΓ (Nat.le_add_right _ _))
    (Nat.le_add_left _ _)
    (by omega) (by omega)

/-! ### §2 The four dischargers, bundled

hSI is `spaceIndiffE`/`spaceIndiffA` of `wip/spaceindiff.lean`,
verbatim; restated here so this file names all four. -/

/-- All four indifference hypotheses of `wip/packaging.lean` hold. -/
theorem ui_dischargers (p : String) :
    FuelIndiffE p ∧ FuelIndiffA p ∧ SpaceIndiffE p ∧ SpaceIndiffA p :=
  ⟨fuelIndiffE p, fuelIndiffA p, spaceIndiffE p, spaceIndiffA p⟩

/-! ### §3 Pitts condition (iv) and factorization, hypothesis-free -/

/-- **(iv∃) ∃-universality, unconditional**: `φ, Δ ⊢ ψ` with `Δ, ψ`
p-free implies `∃p φ, Δ ⊢ ψ`. -/
theorem existsP_adequate' (p : String) {φ ψ : PLLFormula}
    {Δ : List PLLFormula} (hΔp : ∀ χ ∈ Δ, p ∉ χ.atoms)
    (hψp : p ∉ ψ.atoms) (h : G4c (φ :: Δ) ψ) :
    G4c (existsP p φ :: Δ) ψ :=
  existsP_adequate p (fuelIndiffE p) (spaceIndiffE p) hΔp hψp h

/-- **(iv∀) ∀-couniversality, unconditional**: `Δ ⊢ C` with `Δ`
p-free implies `Δ ⊢ ∀p C`. -/
theorem forallP_adequate' (p : String) {C : PLLFormula}
    {Δ : List PLLFormula} (hΔp : ∀ χ ∈ Δ, p ∉ χ.atoms)
    (h : G4c Δ C) : G4c Δ (forallP p C) :=
  forallP_adequate p (fuelIndiffA p) (spaceIndiffA p) hΔp h

/-- (iv∃), single-antecedent: `φ ⊢ ψ`, `ψ` p-free ⟹ `∃p φ ⊢ ψ`. -/
theorem existsP_adequate₀' (p : String) {φ ψ : PLLFormula}
    (hψp : p ∉ ψ.atoms) (h : G4c [φ] ψ) : G4c [existsP p φ] ψ :=
  existsP_adequate₀ p (fuelIndiffE p) (spaceIndiffE p) hψp h

/-- (iv∀), single-antecedent: `ψ ⊢ C`, `ψ` p-free ⟹ `ψ ⊢ ∀p C`. -/
theorem forallP_adequate₀' (p : String) {ψ C : PLLFormula}
    (hψp : p ∉ ψ.atoms) (h : G4c [ψ] C) : G4c [ψ] (forallP p C) :=
  forallP_adequate₀ p (fuelIndiffA p) (spaceIndiffA p) hψp h

/-- Factorization: `∃p (θ ∧ φ) ⊢ θ ∧ ∃p φ` for p-free `θ`. -/
theorem existsP_and_factor_l' (p : String) {θ φ : PLLFormula}
    (hθ : p ∉ θ.atoms) :
    G4c [existsP p (θ.and φ)] (θ.and (existsP p φ)) :=
  existsP_and_factor_l p (fuelIndiffE p) (spaceIndiffE p) hθ

/-- Factorization: `θ ∧ ∃p φ ⊢ ∃p (θ ∧ φ)` for p-free `θ`. -/
theorem existsP_and_factor_r' (p : String) {θ φ : PLLFormula}
    (hθ : p ∉ θ.atoms) :
    G4c [θ.and (existsP p φ)] (existsP p (θ.and φ)) :=
  existsP_and_factor_r p (fuelIndiffE p) (spaceIndiffE p) hθ

/-! ### §4 The crown -/

/-- **Uniform interpolation for PLL** (Pitts-style, packaged).  For
every atom `p` and formulas `φ, C`, the packaged quantifiers
`existsP p φ` and `forallP p C` are p-free uniform interpolants:

* `∃p φ` is p-free, `φ ⊢ ∃p φ`, and `∃p φ` is the *strongest* p-free
  consequence of `φ` — any p-free `ψ` with `φ ⊢ ψ` has `∃p φ ⊢ ψ`;
* `∀p C` is p-free, `∀p C ⊢ C`, and `∀p C` is the *weakest* p-free
  antecedent of `C` — any p-free `ψ` with `ψ ⊢ C` has `ψ ⊢ ∀p C`.

Sequents are `G4c`, the list-context G4-style calculus for PLL. -/
theorem uniform_interpolation_PLL (p : String) (φ C : PLLFormula) :
    (p ∉ (existsP p φ).atoms ∧ G4c [φ] (existsP p φ) ∧
      ∀ ψ, p ∉ ψ.atoms → G4c [φ] ψ → G4c [existsP p φ] ψ) ∧
    (p ∉ (forallP p C).atoms ∧ G4c [forallP p C] C ∧
      ∀ ψ, p ∉ ψ.atoms → G4c [ψ] C → G4c [ψ] (forallP p C)) :=
  ⟨⟨existsP_atoms p φ, existsP_sound p φ,
      fun _ψ hψp h => existsP_adequate₀' p hψp h⟩,
    ⟨forallP_atoms p C, forallP_sound p C,
      fun _ψ hψp h => forallP_adequate₀' p hψp h⟩⟩

/-! ### §5 Axiom audits, pinned

`sorryAx` enters the development through **exactly one declaration**:
`cascade_boxgoal_pos` in `wip/absorb_base.lean` — the quarantined open
kernel of the stabilization ladder (it feeds `cascade_boxgoal`, hence
`cascade_main`, hence `itp_stab`, `itp_stab_le` and the adequacy
consumers).  Every other layer of
the tower is axiom-clean in itself:

* `LaxLogic/PLLG4UITrunc.lean` — clean (see the `existsP_sound` audit
  below, whose cone is library + packaging only);
* `wip/adequacy.lean` — sorry-free in itself (its `itp_adequate`
  audit there pins the same inherited axiom list as here);
* `wip/indiff.lean`, `wip/spaceindiff.lean`, `wip/packaging.lean`,
  `wip/final.lean` — sorry-free.

So the crown's `sorryAx` disappears the moment `cascade_boxgoal_pos`
lands, with no other change anywhere. -/

/--
info: 'PLLND.uniform_interpolation_PLL' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_interpolation_PLL

/-- The contrast: condition (ii) alone never touches the open kernel —
its cone (library `itp_sound` + packaging) is `sorryAx`-free. -/
theorem existsP_sound_axiom_note : True := trivial

/--
info: 'PLLND.existsP_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms existsP_sound

/-! ### §6 Uniform interpolation for the box-free fragment (IPC)

The `◯`-free specialization: for box-free `φ`/`C` the interpolants
`existsP p φ`/`forallP p C` are uniform interpolants against every
box-free p-free `ψ`, and the derivation is **`sorryAx`-free** — it
routes through `itp_stab_bf`/`itp_adequate_bf`, never the `◯`-band
holdout `cascade_boxgoal_pos`.  `existsP_sound`/`forallP_sound` and the
atom lemmas are shared with the full-PLL crown (they never touch the
open kernel). -/

/-- (iv∃) box-free single-antecedent, indifference discharged. -/
theorem existsP_adequate₀_bf' (p : String) {φ ψ : PLLFormula}
    (hφbf : boxFree φ) (hψbf : boxFree ψ) (hψp : p ∉ ψ.atoms)
    (h : G4c [φ] ψ) : G4c [existsP p φ] ψ :=
  existsP_adequate₀_bf p (fuelIndiffE p) (spaceIndiffE p) hφbf hψbf hψp h

/-- (iv∀) box-free single-antecedent, indifference discharged. -/
theorem forallP_adequate₀_bf' (p : String) {ψ C : PLLFormula}
    (hψbf : boxFree ψ) (hCbf : boxFree C) (hψp : p ∉ ψ.atoms)
    (h : G4c [ψ] C) : G4c [ψ] (forallP p C) :=
  forallP_adequate₀_bf p (fuelIndiffA p) (spaceIndiffA p) hψbf hCbf hψp h

/-- **Uniform interpolation for IPC** (the `◯`-free fragment of PLL):
for box-free `φ, C` and every *box-free* p-free `ψ`, the packaged
quantifiers `existsP p φ` and `forallP p C` are p-free uniform
interpolants — the box-free mirror of `uniform_interpolation_PLL`, and
`sorryAx`-free:

* `∃p φ` is p-free, `φ ⊢ ∃p φ`, and any box-free p-free `ψ` with
  `φ ⊢ ψ` has `∃p φ ⊢ ψ`;
* `∀p C` is p-free, `∀p C ⊢ C`, and any box-free p-free `ψ` with
  `ψ ⊢ C` has `ψ ⊢ ∀p C`.

The `boxFree ψ` restriction is the natural one: the interpolants are
strongest/weakest *within the box-free fragment*, whose piece-closure
space carries no `◯`-clause (that is exactly what keeps the descent
off the open kernel). -/
theorem uniform_interpolation_IPC (p : String) (φ C : PLLFormula)
    (hφ : boxFree φ) (hC : boxFree C) :
    (p ∉ (existsP p φ).atoms ∧ G4c [φ] (existsP p φ) ∧
      ∀ ψ, boxFree ψ → p ∉ ψ.atoms → G4c [φ] ψ → G4c [existsP p φ] ψ) ∧
    (p ∉ (forallP p C).atoms ∧ G4c [forallP p C] C ∧
      ∀ ψ, boxFree ψ → p ∉ ψ.atoms → G4c [ψ] C → G4c [ψ] (forallP p C)) :=
  ⟨⟨existsP_atoms p φ, existsP_sound p φ,
      fun _ψ hψbf hψp h => existsP_adequate₀_bf' p hφ hψbf hψp h⟩,
    ⟨forallP_atoms p C, forallP_sound p C,
      fun _ψ hψbf hψp h => forallP_adequate₀_bf' p hψbf hC hψp h⟩⟩

/--
info: 'PLLND.uniform_interpolation_IPC' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms uniform_interpolation_IPC

end PLLND
