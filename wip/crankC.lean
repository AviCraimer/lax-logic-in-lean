import LaxLogic.PLLSemUILayered
import LaxLogic.PLLFrames

/-!
# `crankC` and rank preservation for PCLL (bare possibility)

Branch `ui-confluence`.  On mutually confluent models the ∀∃-clause for
◯ collapses to bare possibility, so a ◯-move costs ONE modal step, not
two.  `crankC` charges ◯ = +1 (vs `crank`'s +2), and
`force_iff_of_layeredC` is `force_iff_of_layered` with that recalibration
— identical on every connective except `somehow`, whose case now uses
`force_somehow_iff_of_confluent` and a single `mforth`/`mback`.

Interactive development (Matthew + Claude): the `somehow` case is the one
open goal.
-/

open PLLFormula

namespace PLLND
open SemUI

/-- **`crankC`**: like `crank`, but ◯ costs 1 (bare possibility spends a
single `Rₘ`-move, no preceding `Rᵢ`-move). -/
def crankC : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and φ ψ => max (crankC φ) (crankC ψ)
  | .or φ ψ => max (crankC φ) (crankC ψ)
  | .ifThen φ ψ => max (crankC φ) (crankC ψ) + 1
  | .somehow φ => crankC φ + 1

/-- **Rank preservation under bare possibility.**  A level-`n` layered
link transfers every formula of `crankC ≤ n` (protected atoms) between
mutually confluent models.  Only the `somehow` case differs from
`force_iff_of_layered`: it spends one modal move, not two. -/
theorem force_iff_of_layeredC {A : String → Prop} {M N : ConstraintModel}
    (hM : MutuallyConfluent M) (hN : MutuallyConfluent N)
    (B : LayeredBisim A M N) :
    ∀ {φ : PLLFormula} {n : Nat}, crankC φ ≤ n →
    (∀ a ∈ φ.atoms, A a) →
    ∀ {w : M.W} {w' : N.W}, B.Z n w w' → (M.force w φ ↔ N.force w' φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro n _ hA w w' hZ
      simpa [ConstraintModel.force] using B.atoms hZ a (hA a (by simp))
  | falsePLL =>
      intro n _ _ w w' hZ
      simpa [ConstraintModel.force] using B.fall hZ
  | and φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr
        (ihφ (le_trans (le_max_left _ _) hc) h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc) h2 hZ)
  | or φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr
        (ihφ (le_trans (le_max_left _ _) hc) h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc) h2 hZ)
  | ifThen φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      have hc' : max (crankC φ) (crankC ψ) + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcφ : crankC φ ≤ m := by
        have h1 := le_max_left (crankC φ) (crankC ψ); omega
      have hcψ : crankC ψ ≤ m := by
        have h1 := le_max_right (crankC φ) (crankC ψ); omega
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv' hφ'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        exact (ihψ hcψ h2 hZv).mp (hf v hv ((ihφ hcφ h1 hZv).mpr hφ'))
      · intro hf v hv hφv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        exact (ihψ hcψ h2 hZv).mpr (hf v' hv' ((ihφ hcφ h1 hZv).mp hφv))
  | somehow φ ihφ =>
      intro n hc hA w w' hZ
      have hc' : crankC φ + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcφ : crankC φ ≤ m := by omega
      rw [force_somehow_iff_of_confluent hM, force_somehow_iff_of_confluent hN]
      constructor
      · rintro ⟨u, hu, hφu⟩
        obtain ⟨u', hu', hZu⟩ := B.mforth hZ hu
        exact ⟨u', hu', (ihφ hcφ hA hZu).mp hφu⟩
      · rintro ⟨u', hu', hφu'⟩
        obtain ⟨u, hu, hZu⟩ := B.mback hZ hu'
        exact ⟨u, hu, (ihφ hcφ hA hZu).mpr hφu'⟩


/-! ## The parity check — does the witnessing-triple gap dissolve?

The wall (`PLLSemUIHenkin.lean`, `WitTriple` + its analysis, lines 45–99):
the primed **reservoir** link sits at `2·d + 1`, one level above the base
link `2·d` (`d = canonDepth`).  A same-`val`-trace ◯-forward move (the
"promise pair") keeps depth `d`, so it needs a fresh **unprimed** link at
the base `2·d`.  A `crank`-◯ move is an `Rᵢ`-zigzag THEN an `Rₘ`-zigzag —
**cost 2** — so spending the reservoir yields `2d + 1 − 2 = 2d − 1`, one
short of `2d`.  Gap `= cost − surplus = 2 − 1 = 1`.

`crankC` (bare possibility) makes the ◯-move a **single** `Rₘ`-zigzag —
**cost 1** (`force_iff_of_layeredC`) — and recalibrates the links to
`d`, `d + 1`.  The reservoir spend now yields `d + 1 − 1 = d`, exactly the
base.  Gap `= 1 − 1 = 0`: financed.  The essential fact is that financing
depends only on `cost ≤ surplus`, and the surplus is structurally `1`. -/

/-- **The financing principle.**  A reservoir link at `base + surplus`,
spent by a move of `cost` levels, meets the required `base` **iff**
`cost ≤ surplus`.  (Robust to the exact `base`, so it survives whatever
the precise recalibrated entry budget turns out to be.) -/
theorem financed_iff {base surplus cost : Nat} (h : cost ≤ base + surplus) :
    base + surplus - cost ≥ base ↔ cost ≤ surplus := by omega

/-- `crank`'s ◯-move (cost 2) over the surplus-1 reservoir: **UNFINANCED**
at every positive depth — the `2d − 1 < 2d` wall. -/
theorem wall_crank (d : Nat) (hd : 1 ≤ d) : ¬ (2 * d + 1 - 2 ≥ 2 * d) := by
  omega

/-- `crankC`'s bare-possibility ◯-move (cost 1) over the surplus-1
reservoir: **FINANCED** at every depth — the gap dissolves. -/
theorem wall_crankC (d : Nat) : d + 1 - 1 ≥ d := by omega

/-- The two verdicts as one statement: with reservoir surplus `1`, a
same-depth ◯-forward move is financed **iff** the ◯-move costs at most one
level — i.e. exactly the `crank`-2 → `crankC`-1 recalibration. -/
theorem parity_verdict {base cost : Nat} (h : cost ≤ base + 1) :
    base + 1 - cost ≥ base ↔ cost ≤ 1 :=
  financed_iff h

-- audit: force_iff_of_layeredC is sorry-free
#print axioms force_iff_of_layeredC

end PLLND
