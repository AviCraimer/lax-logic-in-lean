import wip.towerkit
import packaging

/-!
# `towerpack` — the transcriptions really are `wip/packaging.lean`'s

`wip/absorb_base.lean`, `wip/adequacy.lean` and `wip/packaging.lean` use
root-level imports and are built standalone against a `LEAN_PATH` dependency
directory, so they are not Lake targets and `wip/towerkit.lean` cannot import
them.  This file *is* built that way, and checks by `rfl` that TowerKit's
transcriptions of `pieceClosure`, `kcap`, `uiFuel` are the originals, and
that `eTower φ (eBudget φ)` / `aTower C (aBudget C)` are exactly the
packaged `existsP` / `forallP` on the battery's (p-containing) formulas.

Build (from the repo root, `<dep>` the dependency directory holding
`absorb_base.olean`, `adequacy.olean`, `packaging.olean`):

    lake env lean wip/absorb_base.lean -o <dep>/absorb_base.olean
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<dep>" lean wip/adequacy.lean  -o <dep>/adequacy.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<dep>" lean wip/packaging.lean -o <dep>/packaging.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<dep>" lean wip/towerpack.lean'
-/

set_option autoImplicit false

open PLLFormula PLLND PLLND.RNEmbed

namespace TowerPack

/-! ## §1  The three transcribed definitions are the originals

`pieceClosure` is well-founded-recursive, so two copies of it are not
definitionally equal; the functional induction principle closes it. -/

theorem pieceClosure_eq (φ : PLLFormula) :
    TowerKit.pieceClosure φ = PLLND.pieceClosure φ := by
  induction φ using PLLND.pieceClosure.induct <;>
    simp_all [TowerKit.pieceClosure, PLLND.pieceClosure]

theorem kcap_eq : TowerKit.kcap = PLLND.kcap := rfl
theorem uiFuel_eq : TowerKit.uiFuel = PLLND.uiFuel := rfl

/-! ## §2  `eTower`/`aTower` at the prescribed budget are `existsP`/`forallP`

`existsP p φ` short-circuits to `φ` when `p ∉ φ.atoms`; on the battery `p`
always occurs, so the `itpE` branch is the one taken.  These identities are
stated with the branch condition as a hypothesis so that no formula-specific
computation is needed. -/

theorem existsP_eq_eTower (φ : PLLFormula) (h : pv ∈ φ.atoms) :
    existsP pv φ = TowerKit.eTower φ (TowerKit.eBudget φ) := by
  unfold existsP TowerKit.eTower TowerKit.eFuel TowerKit.eBudget
  rw [if_pos h, pieceClosure_eq, kcap_eq, uiFuel_eq]

theorem forallP_eq_aTower (C : PLLFormula) (h : pv ∈ C.atoms) :
    forallP pv C = TowerKit.aTower C (TowerKit.aBudget C) := by
  unfold forallP TowerKit.aTower TowerKit.aFuel TowerKit.aBudget
  rw [if_pos h, pieceClosure_eq, kcap_eq, uiFuel_eq]

end TowerPack
