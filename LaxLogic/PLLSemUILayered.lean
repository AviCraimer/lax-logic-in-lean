import LaxLogic.PLLSemUITrace

/-!
# The Litak–Visser route: layered bisimulations for PLL

Following A. Visser, *Uniform interpolation and layered bisimulation*
(Gödel '96) and T. Litak & A. Visser, *Lewis and Brouwer meet Strong
Löb* (arXiv:2404.11969) §4.3–§5.1, which prove uniform interpolation
SEMANTICALLY for IPC/K/GL and for iSL — the latter an intuitionistic
modal logic sharing PLL's Strength axiom φ → ◯φ.  This file sets up
their machinery over our constraint models and states the pillar
lemmas of their route in our terms; the pillars that are theirs to
adapt are `sorry`-marked and named, so each can be attacked (or
refuted) separately.

## The route (their numbering)

1. **Complexity** c(φ): atoms/⊥ cost 0, ∧/∨ take max, →/⊰ add 1.
   Our ◯ is interpreted by the ∀∃-clause (an Rᵢ-move THEN an Rₘ-move),
   so it costs 2 here (`crank`); their Lewis arrow costs 1.  The
   fragment `C_r(V)` of p-free formulas of complexity ≤ r is finite up
   to interderivability (their Thm 4.5 for IPC; `frag_reps_exist`,
   OPEN for PLL — expected from the finite canonical model).
2. **Layered (bounded) bisimulation** (their §4.3): a level-indexed
   relation; atoms and fallibility demanded at EVERY level; the four
   zigzags each spend one level.  `LayeredBisim`.
3. **Rank preservation** (their Thm 4.6): a level-n link transfers
   forcing of formulas of complexity ≤ n.  PROVED below
   (`force_iff_of_layered`), with the unbounded invariance
   `force_iff_of_bisim` recovered as the constant-family corollary —
   the consistency test for the definitions.
4. **Characters** (their Thm 4.7): fragment-agreement at rank n
   conversely yields a level-n link, via the finite conjunction θ⁺ and
   disjunction θ⁻ of the rank-n fragment.  `layered_of_frag_agree`
   (OPEN).
5. **THE AMALGAMATION LEMMA** (their Lemma 5.4; Visser's Lemma 5.1):
   from a level-(2ν+1) link between k₀ and m₀ protecting the shared
   alphabet, a p-variant of M whose root agrees with k₀ on the whole
   adequate set.  Their proof: the amalgam's worlds are pairs
   ⟨Δ, m⟩ = (theory in the finite pre-Henkin model over X, world of
   M), admissible when a WITNESSING TRIPLE k′ ≼ k, k′ Z_{2d(k′)+1} m′,
   k Z_{2d(k′)} m exists — the budget is financed by the DEPTH d of
   the theory coordinate in the finite Henkin model, so near-maximal
   theories need almost no matching.  `amalgamation` (OPEN for PLL).

## Match against our development

* Their amalgam ⟨Δ, m⟩-pairs = our description graft's fibres
  (`descGraft`); their valuation "Δ ⊩ a or m ⊩ a" agrees with ours on
  shared atoms and reads the Henkin side for the quantified atom —
  our redecoration.  MATCH.
* Their budget bookkeeping is the exact repair of our measured dead
  end: our unbounded pairing (`Realises`) demanded zigzags at every
  level against the full canonical model and was computed EMPTY on
  F-free rows; the uniform depth-bounded approximants die by level 3.
  Their witnessing triples demand level 2d+1 only, d = Henkin depth
  of the theory — the everything-affirming theory has maximal depth,
  budget ≈ 0, and is harmless.  MISMATCH → their form wins.
* Their Θ⁺ ⊬ Θ⁻ ∨ φ underivability step (Thm 5.1(2)) is the
  rank-completed form of our pre-triple consistency
  (`preTripleAll_cons_of_residue` proved it NECESSARY); their
  characters replace our closure-only description by the full
  rank-bounded fragment.  PARTIAL MATCH — ours is the subformula
  shadow of theirs.
* Genuinely new for PLL, absent from iSL: fallible worlds (their
  frames have irreflexive ⊏ with dead ends where PLL needs F — our
  fallibility-absorption lemmas in `descGraft_force_iff` are the
  candidate technology), the interaction Rₘ ⊆ Rᵢ with BOTH relations
  reflexive, and the promise component of canonical theories (their
  theories are plain sets; our `trace_mforth` shows promises are
  functorial along Rₘ — the extra bookkeeping the ◯-clause needs).
  Their Remark 5.5: "something more complicated needs to be done for
  other intuitionistic modal logics" — this is that something.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## 1. Complexity -/

/-- Litak–Visser complexity, adapted: atoms and ⊥ cost 0, ∧/∨ take
the maximum, → adds 1, and ◯ adds 2 — its constraint-model clause
spends an Rᵢ-move AND an Rₘ-move.  (Calibration constant; their Lewis
arrow with its one-step clause costs 1.) -/
def crank : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and φ ψ => max (crank φ) (crank ψ)
  | .or φ ψ => max (crank φ) (crank ψ)
  | .ifThen φ ψ => max (crank φ) (crank ψ) + 1
  | .somehow φ => crank φ + 2

/-- The budget-financing count for an adequate set: its variables,
implications and ◯-formulas (their n_X). -/
def isBudget : PLLFormula → Bool
  | .prop _ => true
  | .ifThen _ _ => true
  | .somehow _ => true
  | _ => false

def nu (X : Finset PLLFormula) : Nat := (X.filter (isBudget · = true)).card

/-! ## 2. Layered bisimulation -/

/-- **Layered (bounded) bisimulation** for the protected alphabet
`A`: a level-indexed relation, downward closed, with atoms and
fallibility matched at every level and the four zigzags each spending
one level (their §4.3, with the fallibility clause PLL adds). -/
structure LayeredBisim (A : String → Prop) (M N : ConstraintModel) where
  Z : Nat → M.W → N.W → Prop
  mono : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → Z n w w'
  atoms : ∀ {n : Nat} {w w'}, Z n w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  fall : ∀ {n : Nat} {w w'}, Z n w w' → (w ∈ M.F ↔ w' ∈ N.F)
  iforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v}, M.Ri w v →
    ∃ v', N.Ri w' v' ∧ Z n v v'
  iback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v'}, N.Ri w' v' →
    ∃ v, M.Ri w v ∧ Z n v v'
  mforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u}, M.Rm w u →
    ∃ u', N.Rm w' u' ∧ Z n u u'
  mback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u'}, N.Rm w' u' →
    ∃ u, M.Rm w u ∧ Z n u u'

variable {A : String → Prop} {M N : ConstraintModel}

/-- Levels drop along `≤`. -/
theorem LayeredBisim.mono_le (B : LayeredBisim A M N) :
    ∀ {m n : Nat}, m ≤ n → ∀ {w w'}, B.Z n w w' → B.Z m w w' := by
  intro m n h
  induction h with
  | refl => exact fun h => h
  | step _ ih => exact fun h => ih (B.mono h)

/-- An unbounded bisimulation is a layered one at every level (the
constant family). -/
def LayeredBisim.ofABisim (B : ABisim A M N) : LayeredBisim A M N where
  Z := fun _ => B.Z
  mono := fun h => h
  atoms := fun h => B.atoms h
  fall := fun h => B.fall h
  iforth := by intro n w w' h v hv; exact B.iforth h hv
  iback := by intro n w w' h v' hv'; exact B.iback h hv'
  mforth := by intro n w w' h u hu; exact B.mforth h hu
  mback := by intro n w w' h u' hu'; exact B.mback h hu'

/-! ## 3. Rank preservation (their Theorem 4.6) — PROVED -/

/-- **A level-n link transfers formulas of complexity ≤ n** whose
atoms are protected.  The ⊃-case spends one level (one i-zigzag); the
◯-case spends two (an i-zigzag then an m-zigzag) — the reason ◯ costs
2 in `crank`. -/
theorem force_iff_of_layered (B : LayeredBisim A M N) :
    ∀ {φ : PLLFormula} {n : Nat}, crank φ ≤ n →
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
      have hc' : max (crank φ) (crank ψ) + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
        ⟨n - 1, by omega⟩
      have hcφ : crank φ ≤ m := by
        have h1 := le_max_left (crank φ) (crank ψ); omega
      have hcψ : crank ψ ≤ m := by
        have h1 := le_max_right (crank φ) (crank ψ); omega
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
      have hc' : crank φ + 2 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 :=
        ⟨n - 2, by omega⟩
      have hcφ : crank φ ≤ m := by omega
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv'
        obtain ⟨v, hv, hZv⟩ := B.iback hZ hv'
        obtain ⟨u, hu, hφu⟩ := hf v hv
        obtain ⟨u', hu', hZu⟩ := B.mforth hZv hu
        exact ⟨u', hu', (ihφ hcφ hA hZu).mp hφu⟩
      · intro hf v hv
        obtain ⟨v', hv', hZv⟩ := B.iforth hZ hv
        obtain ⟨u', hu', hφu'⟩ := hf v' hv'
        obtain ⟨u, hu, hZu⟩ := B.mback hZv hu'
        exact ⟨u, hu, (ihφ hcφ hA hZu).mpr hφu'⟩

/-- Consistency test: the constant family recovers the unbounded
invariance theorem exactly. -/
theorem force_iff_of_bisim_via_layered (B : ABisim A M N)
    {φ : PLLFormula} (hA : ∀ a ∈ φ.atoms, A a)
    {w : M.W} {w' : N.W} (hZ : B.Z w w') :
    (M.force w φ ↔ N.force w' φ) :=
  force_iff_of_layered (LayeredBisim.ofABisim B) le_rfl hA hZ

/-! ## 3′. The WEAKENED layered bisimulation (the repaired form)

The refutation below shows the full zigzags are too strong for PLL;
the repair is the `DescPack` clause shape: the i-zigzags may escape
at a fallible target (which forces everything, so constrains
nothing), the m-zigzags may pair fallible witnesses.  Rank
preservation goes through unchanged — every escape absorbs by
`force_of_fallible`, exactly as in `descGraft_force_iff` — and the
probe (wip/mforth_probe.lean: 2324 agreeing pairs, 0 candidates)
supports that THIS form is derivable from fragment-agreement. -/

/-- Layered bisimulation with fallibility escapes: the working form
for PLL. -/
structure LayeredBisimE (A : String → Prop) (M N : ConstraintModel) where
  Z : Nat → M.W → N.W → Prop
  mono : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → Z n w w'
  atoms : ∀ {n : Nat} {w w'}, Z n w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  fall : ∀ {n : Nat} {w w'}, Z n w w' → (w ∈ M.F ↔ w' ∈ N.F)
  iforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v}, M.Ri w v →
    (∃ v', N.Ri w' v' ∧ Z n v v') ∨ v ∈ M.F
  iback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v'}, N.Ri w' v' →
    (∃ v, M.Ri w v ∧ Z n v v') ∨ v' ∈ N.F
  mforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u}, M.Rm w u →
    ∃ u', N.Rm w' u' ∧ (Z n u u' ∨ (u ∈ M.F ∧ u' ∈ N.F))
  mback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u'}, N.Rm w' u' →
    ∃ u, M.Rm w u ∧ (Z n u u' ∨ (u ∈ M.F ∧ u' ∈ N.F))

theorem LayeredBisimE.mono_le (B : LayeredBisimE A M N) :
    ∀ {m n : Nat}, m ≤ n → ∀ {w w'}, B.Z n w w' → B.Z m w w' := by
  intro m n h
  induction h with
  | refl => exact fun h => h
  | step _ ih => exact fun h => ih (B.mono h)

/-- The strong form embeds in the weak one. -/
def LayeredBisim.toE (B : LayeredBisim A M N) : LayeredBisimE A M N where
  Z := B.Z
  mono := B.mono
  atoms := B.atoms
  fall := B.fall
  iforth := by
    intro n w w' h v hv
    exact .inl (B.iforth h hv)
  iback := by
    intro n w w' h v' hv'
    exact .inl (B.iback h hv')
  mforth := by
    intro n w w' h u hu
    obtain ⟨u', hu', hZ⟩ := B.mforth h hu
    exact ⟨u', hu', .inl hZ⟩
  mback := by
    intro n w w' h u' hu'
    obtain ⟨u, hu, hZ⟩ := B.mback h hu'
    exact ⟨u, hu, .inl hZ⟩

/-- **Rank preservation for the weakened form** — every escape
absorbs by `force_of_fallible`: fallible ⊃-targets force the
conclusion outright, fallible ◯-row pairs supply their own
witnesses. -/
theorem force_iff_of_layeredE (B : LayeredBisimE A M N) :
    ∀ {φ : PLLFormula} {n : Nat}, crank φ ≤ n →
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
      have hc' : max (crank φ) (crank ψ) ≤ n := hc
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact and_congr
        (ihφ (le_trans (le_max_left _ _) hc') h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc') h2 hZ)
  | or φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have hc' : max (crank φ) (crank ψ) ≤ n := hc
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      simp only [ConstraintModel.force]
      exact or_congr
        (ihφ (le_trans (le_max_left _ _) hc') h1 hZ)
        (ihψ (le_trans (le_max_right _ _) hc') h2 hZ)
  | ifThen φ ψ ihφ ihψ =>
      intro n hc hA w w' hZ
      have h1 : ∀ a ∈ φ.atoms, A a := fun a ha => hA a (by simp [ha])
      have h2 : ∀ a ∈ ψ.atoms, A a := fun a ha => hA a (by simp [ha])
      have hc' : max (crank φ) (crank ψ) + 1 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcφ : crank φ ≤ m := by
        have h3 := le_max_left (crank φ) (crank ψ); omega
      have hcψ : crank ψ ≤ m := by
        have h3 := le_max_right (crank φ) (crank ψ); omega
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv' hφ'
        rcases B.iback hZ hv' with ⟨v, hv, hZv⟩ | hF
        · exact (ihψ hcψ h2 hZv).mp (hf v hv ((ihφ hcφ h1 hZv).mpr hφ'))
        · exact N.force_of_fallible hF
      · intro hf v hv hφv
        rcases B.iforth hZ hv with ⟨v', hv', hZv⟩ | hF
        · exact (ihψ hcψ h2 hZv).mpr (hf v' hv' ((ihφ hcφ h1 hZv).mp hφv))
        · exact M.force_of_fallible hF
  | somehow φ ihφ =>
      intro n hc hA w w' hZ
      have hc' : crank φ + 2 ≤ n := hc
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have hcφ : crank φ ≤ m := by omega
      simp only [ConstraintModel.force]
      constructor
      · intro hf v' hv'
        rcases B.iback hZ hv' with ⟨v, hv, hZv⟩ | hF
        · obtain ⟨u, hu, hφu⟩ := hf v hv
          obtain ⟨u', hu', hZu | ⟨-, hu'F⟩⟩ := B.mforth hZv hu
          · exact ⟨u', hu', (ihφ hcφ hA hZu).mp hφu⟩
          · exact ⟨u', hu', N.force_of_fallible hu'F⟩
        · exact ⟨v', N.refl_m v', N.force_of_fallible hF⟩
      · intro hf v hv
        rcases B.iforth hZ hv with ⟨v', hv', hZv⟩ | hF
        · obtain ⟨u', hu', hφu'⟩ := hf v' hv'
          obtain ⟨u, hu, hZu | ⟨huF, -⟩⟩ := B.mback hZv hu'
          · exact ⟨u, hu, (ihφ hcφ hA hZu).mpr hφu'⟩
          · exact ⟨u, hu, M.force_of_fallible huF⟩
        · exact ⟨v, M.refl_m v, M.force_of_fallible hF⟩

/-! ## 3″. The m-escape geography (machine-checked from both sides)

The probe (wip/mforth_probe.lean) reports 0 violations of the
NON-fallible forth-m clause across 2324 agreeing pairs, but 82
violations of the fallible-PAIR escape.  Both boundary facts are
theorems below:

* `weak_escape_breaks_force_iff`: with the weak m-escape (no
  obligation at a fallible row-member), rank preservation FAILS — a
  fallible row-member finances ◯⊥ on one side with nothing to match
  it on the other.  So `LayeredBisimE`'s pair escape is the weakest
  form supporting `force_iff_of_layeredE`.
* `pair_escape_not_from_agreement`: the pair escape is NOT derivable
  from fragment-agreement — the fork with one fallible m-branch
  agrees with the lone point on every variable-free formula, but the
  lone point's row has no fallible member.

CONSEQUENCE (the settled design): pillar 2 can only produce the WEAK
form `LayeredBisimW` below; the amalgamation must therefore not
consume the link's m-clauses for its ◯-case, routing instead through
the promise components (`mfal`) of the canonical coordinate — the
reason Fairtlough–Mendler theories carry promises at all.  The
E-form stays as the OUTPUT format (what `wit_pbisim` produces), the
W-form as the INPUT format (what agreement delivers). -/

/-- Layered bisimulation with the WEAK m-escape: no obligation at a
fallible row-member.  This is the form fragment-agreement can
deliver; `force_iff` FAILS for it (`weak_escape_breaks_force_iff`). -/
structure LayeredBisimW (A : String → Prop) (M N : ConstraintModel) where
  Z : Nat → M.W → N.W → Prop
  mono : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → Z n w w'
  atoms : ∀ {n : Nat} {w w'}, Z n w w' → ∀ a, A a → (w ∈ M.V a ↔ w' ∈ N.V a)
  fall : ∀ {n : Nat} {w w'}, Z n w w' → (w ∈ M.F ↔ w' ∈ N.F)
  iforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v}, M.Ri w v →
    (∃ v', N.Ri w' v' ∧ Z n v v') ∨ v ∈ M.F
  iback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {v'}, N.Ri w' v' →
    (∃ v, M.Ri w v ∧ Z n v v') ∨ v' ∈ N.F
  mforth : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u}, M.Rm w u →
    (∃ u', N.Rm w' u' ∧ Z n u u') ∨ u ∈ M.F
  mback : ∀ {n : Nat} {w w'}, Z (n + 1) w w' → ∀ {u'}, N.Rm w' u' →
    (∃ u, M.Rm w u ∧ Z n u u') ∨ u' ∈ N.F

/-- Two-point chain with a fallible top on the FULL constraint
relation (`Rₘ = Rᵢ`): the bottom forces ◯⊥ through the fallible
row-member. -/
def chainFM : ConstraintModel where
  W := Bool
  Ri := fun x y => x = y ∨ (x = false ∧ y = true)
  Rm := fun x y => x = y ∨ (x = false ∧ y = true)
  F := {x | x = true}
  V := fun _ => {x | x = true}
  refl_i := fun _ => .inl rfl
  trans_i := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by decide)
  refl_m := fun _ => .inl rfl
  trans_m := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by decide)
  sub_mi := fun h => h
  hered_F := by
    intro a b h hF
    rcases h with rfl | ⟨-, rfl⟩
    · exact hF
    · rfl
  hered_V := by
    intro x a b h hV
    rcases h with rfl | ⟨-, rfl⟩
    · exact hV
    · rfl
  full_F := fun hF => hF

/-- **The weak m-escape breaks rank preservation**: the constant
relation linking the bottom of `chainFM` with the world of `oneW`
satisfies every `LayeredBisimW` clause, yet ◯⊥ (complexity 2) holds
at the bottom — the fallible row-member supplies every witness — and
fails at the lone point. -/
theorem weak_escape_breaks_force_iff :
    ∃ (B : LayeredBisimW (fun _ => True) chainFM oneW),
      B.Z 2 false () ∧
      chainFM.force false (PLLFormula.falsePLL.somehow) ∧
      ¬ oneW.force () (PLLFormula.falsePLL.somehow) := by
  refine ⟨⟨fun _ w w' => w = false, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    rfl, ?_, ?_⟩
  · exact fun h => h
  · rintro n w w' rfl a -
    constructor
    · intro h
      exact absurd (show false = true from h) (by decide)
    · intro h
      exact h.elim
  · rintro n w w' rfl
    constructor
    · intro h
      exact absurd (show false = true from h) (by decide)
    · intro h
      exact h.elim
  · rintro n w w' rfl v hv
    rcases hv with rfl | ⟨-, rfl⟩
    · exact .inl ⟨(), trivial, rfl⟩
    · exact .inr rfl
  · rintro n w w' rfl v' -
    exact .inl ⟨false, .inl rfl, rfl⟩
  · rintro n w w' rfl u hu
    rcases hu with rfl | ⟨-, rfl⟩
    · exact .inl ⟨(), trivial, rfl⟩
    · exact .inr rfl
  · rintro n w w' rfl u' -
    exact .inl ⟨false, .inl rfl, rfl⟩
  · intro v hv
    rcases hv with rfl | ⟨-, rfl⟩
    · exact ⟨true, .inr ⟨rfl, rfl⟩, rfl⟩
    · exact ⟨true, .inl rfl, rfl⟩
  · intro h
    obtain ⟨u, -, hu⟩ := h () trivial
    exact hu

/-- The fork with one fallible m-branch: bottom `none`, a rigid
non-fallible top `some false`, a fallible top `some true` reached by
`Rₘ` from the bottom. -/
def forkF : ConstraintModel where
  W := Option Bool
  Ri := fun x y => x = y ∨ x = none
  Rm := fun x y => x = y ∨ (x = none ∧ y = some true)
  F := {x | x = some true}
  V := fun _ => {x | x = some true}
  refl_i := fun _ => .inl rfl
  trans_i := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | rfl
    · exact h₂
    · exact .inr rfl
  refl_m := fun _ => .inl rfl
  trans_m := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by decide)
  sub_mi := by
    intro a b h
    rcases h with rfl | ⟨rfl, -⟩
    · exact .inl rfl
    · exact .inr rfl
  hered_F := by
    intro a b h hF
    rcases h with rfl | rfl
    · exact hF
    · exact absurd (show (none : Option Bool) = some true from hF)
        (by decide)
  hered_V := by
    intro x a b h hV
    rcases h with rfl | rfl
    · exact hV
    · exact absurd (show (none : Option Bool) = some true from hV)
        (by decide)
  full_F := fun hF => hF

/-- The rigid top of the fork is indistinguishable from the lone
point — on EVERY formula (both refute every atom). -/
theorem forkF_top_agree :
    ∀ (χ : PLLFormula),
      (forkF.force (some false) χ ↔ oneW.force () χ) := by
  intro χ
  induction χ with
  | prop a =>
      constructor
      · intro h
        exact absurd (show (some false : Option Bool) = some true from h)
          (by decide)
      · intro h
        exact h.elim
  | falsePLL =>
      constructor
      · intro h
        exact absurd (show (some false : Option Bool) = some true from h)
          (by decide)
      · intro h
        exact h.elim
  | and φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      exact or_congr ihφ ihψ
  | ifThen φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      constructor
      · intro h _ _ hφ
        exact ihψ.mp (h (some false) (.inl rfl) (ihφ.mpr hφ))
      · intro h v hv hφ
        rcases hv with rfl | hv
        · exact ihψ.mpr (h () trivial (ihφ.mp hφ))
        · exact absurd (show (some false : Option Bool) = none from hv)
            (by decide)
  | somehow φ ih =>
      simp only [ConstraintModel.force]
      constructor
      · intro h _ _
        obtain ⟨u, hu, hφ⟩ := h (some false) (.inl rfl)
        rcases hu with rfl | ⟨h', -⟩
        · exact ⟨(), trivial, ih.mp hφ⟩
        · exact absurd (show (some false : Option Bool) = none from h')
            (by decide)
      · intro h v hv
        obtain ⟨u0, -, hφ⟩ := h () trivial
        rcases hv with rfl | hv
        · exact ⟨some false, .inl rfl, ih.mpr hφ⟩
        · exact absurd (show (some false : Option Bool) = none from hv)
            (by decide)

/-- **Full agreement of the fork's bottom with the lone point**: the
fallible m-branch is invisible to every formula — its witnesses come
free at the bottom's own row, and every other future self-witnesses. -/
theorem forkF_agree :
    ∀ (χ : PLLFormula),
      (forkF.force none χ ↔ oneW.force () χ) := by
  intro χ
  induction χ with
  | prop a =>
      constructor
      · intro h
        exact absurd (show (none : Option Bool) = some true from h)
          (by decide)
      · intro h
        exact h.elim
  | falsePLL =>
      constructor
      · intro h
        exact absurd (show (none : Option Bool) = some true from h)
          (by decide)
      · intro h
        exact h.elim
  | and φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      exact or_congr ihφ ihψ
  | ifThen φ ψ ihφ ihψ =>
      simp only [ConstraintModel.force]
      constructor
      · intro h _ _ hφ
        exact ihψ.mp (h none (.inl rfl) (ihφ.mpr hφ))
      · intro h v hv hφ
        match v with
        | none => exact ihψ.mpr (h () trivial (ihφ.mp hφ))
        | some false =>
            exact (forkF_top_agree ψ).mpr
              (h () trivial ((forkF_top_agree φ).mp hφ))
        | some true => exact forkF.force_of_fallible rfl
  | somehow φ ih =>
      simp only [ConstraintModel.force]
      constructor
      · intro h _ _
        obtain ⟨u, hu, hφ⟩ := h (some false) (.inr rfl)
        rcases hu with rfl | ⟨h', -⟩
        · exact ⟨(), trivial, (forkF_top_agree φ).mp hφ⟩
        · exact absurd (show (some false : Option Bool) = none from h')
            (by decide)
      · intro h v hv
        obtain ⟨u0, -, hφ⟩ := h () trivial
        match v with
        | none => exact ⟨some true, .inr ⟨rfl, rfl⟩,
            forkF.force_of_fallible rfl⟩
        | some false =>
            exact ⟨some false, .inl rfl, (forkF_top_agree φ).mpr hφ⟩
        | some true => exact ⟨some true, .inl rfl,
            forkF.force_of_fallible rfl⟩

/-- **The pair escape is not derivable from agreement**: the fork's
bottom agrees with the lone point on EVERY formula, yet any
`LayeredBisimE` linking them at level 1 dies on `mforth` at the
fallible m-branch — the lone point's row has no fallible member.
(With `forkF_agree` this also separates logical indistinguishability
from escape-bisimilarity in PLL outright.) -/
theorem pair_escape_not_from_agreement :
    ¬ ∃ B : LayeredBisimE (fun _ => True) forkF oneW, B.Z 1 none () := by
  rintro ⟨B, hZ⟩
  obtain ⟨u', -, hZ' | ⟨-, hF⟩⟩ :=
    B.mforth hZ (show forkF.Rm none (some true) from .inr ⟨rfl, rfl⟩)
  · exact (B.fall hZ').mp rfl
  · exact hF

/- **The repaired pillar 2** lives in `PLLSemUIChar.lean`
(`layered_of_frag_agree_W`): the i-clauses and all pointwise clauses
are PROVED there by the character argument; the sorry-footprint is
exactly the two weak m-clauses (probe-backed). -/

/-! ## 4. The sorried pillars (each a separate target)

The statements below are the PLL forms of the remaining steps of the
Litak–Visser route.  Each is stated so that it can be attacked — or
refuted by the oracle on instances — independently. -/

/- **Fragment finiteness up to interderivability** (their Thm 4.5
analogue): PROVED as `frag_reps_exist'` in `PLLSemUIFrag.lean`
(DNF-over-components construction, sorry-free). -/

/-! ### Pillar 2: their Theorem 4.7 is REFUTED for PLL as stated

Their proof takes Z at level α := agreement at rank α.  For PLL this
CANNOT satisfy the `iforth` zigzag of `LayeredBisim`: adding a
fallible top with a trivial row to a model is conservative — "some
Rᵢ-successor is fallible" is not a hereditary property, so no formula
expresses it — yet the fallible successor demands a fallible partner
through the `fall` clause.  Machine-checked below on the two-point
chain against `oneW`.  (Litak–Visser never meet this: their frames
replace fallible worlds by irreflexive dead ends.)

The redesign boundary this fixes precisely: the ESCAPE form of
`iforth` (partner OR the successor is fallible, as in `DescPack`)
survives the character argument — a NON-fallible successor `v`
refutes its θ⁻ (a fallible one forces everything, breaking `v ⊮ θ⁻`),
so the implication argument still produces a partner exactly when one
is demanded.  The open pillar-2 question is therefore the m-clauses:
which row-zigzag weakening is both agreement-derivable and strong
enough for the two-case budget argument of `wit_pbisim`. -/

/-- Two-point chain with a fallible top and trivial rows: the
conservative extension that defeats the `fall` zigzag. -/
def chainF : ConstraintModel where
  W := Bool
  Ri := fun x y => x = y ∨ (x = false ∧ y = true)
  Rm := fun x y => x = y
  F := {x | x = true}
  V := fun _ => {x | x = true}
  refl_i := fun _ => .inl rfl
  trans_i := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | ⟨rfl, rfl⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨h, -⟩
      · exact .inr ⟨rfl, rfl⟩
      · exact absurd h (by simp)
  refl_m := fun _ => rfl
  trans_m := fun h₁ h₂ => h₁.trans h₂
  sub_mi := fun h => .inl h
  hered_F := by
    intro a b h hF
    rcases h with rfl | ⟨-, rfl⟩
    · exact hF
    · rfl
  hered_V := by
    intro x a b h hV
    rcases h with rfl | ⟨-, rfl⟩
    · exact hV
    · rfl
  full_F := fun hF => hF

/-- **Conservativity of the fallible top** at rank ≤ 1: the bottom of
`chainF` agrees with the world of `oneW` on every variable-free
formula of complexity ≤ 1 (the fallible top forces everything, so it
never blocks an implication; ◯ needs complexity 2). -/
theorem chainF_oneW_agree : ∀ {χ : PLLFormula}, crank χ ≤ 1 →
    (∀ a ∈ χ.atoms, a ∈ (∅ : Finset String)) →
    (chainF.force false χ ↔ oneW.force () χ) := by
  intro χ
  induction χ with
  | prop a =>
      intro _ ha
      exact absurd (ha a (by simp)) (by simp)
  | falsePLL =>
      intro _ _
      constructor
      · intro h
        exact absurd (show false = true from h) (by decide)
      · intro h
        exact h.elim
  | and φ ψ ihφ ihψ =>
      intro hc ha
      have hc' : max (crank φ) (crank ψ) ≤ 1 := hc
      have h1 : ∀ a ∈ φ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      have h2 : ∀ a ∈ ψ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      simp only [ConstraintModel.force]
      exact and_congr
        (ihφ (le_trans (le_max_left _ _) hc') h1)
        (ihψ (le_trans (le_max_right _ _) hc') h2)
  | or φ ψ ihφ ihψ =>
      intro hc ha
      have hc' : max (crank φ) (crank ψ) ≤ 1 := hc
      have h1 : ∀ a ∈ φ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      have h2 : ∀ a ∈ ψ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      simp only [ConstraintModel.force]
      exact or_congr
        (ihφ (le_trans (le_max_left _ _) hc') h1)
        (ihψ (le_trans (le_max_right _ _) hc') h2)
  | ifThen φ ψ ihφ ihψ =>
      intro hc ha
      have hc' : max (crank φ) (crank ψ) + 1 ≤ 1 := hc
      have hcφ : crank φ ≤ 1 := by
        have h1 := le_max_left (crank φ) (crank ψ); omega
      have hcψ : crank ψ ≤ 1 := by
        have h1 := le_max_right (crank φ) (crank ψ); omega
      have h1 : ∀ a ∈ φ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      have h2 : ∀ a ∈ ψ.atoms, a ∈ (∅ : Finset String) :=
        fun a h => ha a (by simp [h])
      simp only [ConstraintModel.force]
      constructor
      · intro hf v _ hφ
        exact (ihψ hcψ h2).mp
          (hf false (.inl rfl) ((ihφ hcφ h1).mpr hφ))
      · intro hf v hv hφ
        cases v with
        | false =>
            exact (ihψ hcψ h2).mpr
              (hf () trivial ((ihφ hcφ h1).mp hφ))
        | true =>
            exact chainF.force_of_fallible rfl
  | somehow φ ih =>
      intro hc _
      have hc' : crank φ + 2 ≤ 1 := hc
      exact absurd hc' (by omega)

/-- **The refutation** (machine-checked): fragment-agreement does NOT
yield a layered bisimulation for PLL — the pillar-2 statement in the
Litak–Visser form is false over constraint models. -/
theorem layered_of_frag_agree_refuted :
    ¬ (∀ (V : Finset String) (n : Nat) (M N : ConstraintModel)
        (w : M.W) (w' : N.W),
      (∀ χ : PLLFormula, crank χ ≤ n → (∀ a ∈ χ.atoms, a ∈ V) →
        (M.force w χ ↔ N.force w' χ)) →
      ∃ B : LayeredBisim (fun a => a ∈ V) M N, B.Z n w w') := by
  intro h
  obtain ⟨B, hZ⟩ := h ∅ 1 chainF oneW false ()
    (fun χ hc ha => chainF_oneW_agree hc ha)
  obtain ⟨v', -, hZ0⟩ :=
    B.iforth hZ (show chainF.Ri false true from .inr ⟨rfl, rfl⟩)
  exact (B.fall hZ0).mp rfl

/-- **THE PLL AMALGAMATION LEMMA** (their Lemma 5.4 / Visser's Lemma
5.1; OPEN — the central open problem of the route, equivalent in
strength to the residues of the box-commutation law).

Given an adequate set X, a model K whose root k₀ is layered-bisimilar
to m₀ ∈ M at level 2·(nu X)+1 protecting everything but p, there is a
p-VARIANT of M (unbounded bisimulation!) whose root agrees with k₀ on
all of X.

Their proof shape to adapt: amalgam worlds = pairs ⟨Δ, m⟩ with Δ an
X-prime theory of the finite pre-Henkin model and m ∈ M, admissible
when a witnessing triple k′ ≼ k, k′ Z_{2d(k′)+1} m′, k Z_{2d(k′)} m
exists (d = Henkin depth of Δ); relations componentwise; atoms from
the union of the coordinates.  PLL additions needed: the fallibility
clauses (F-absorption as in `descGraft_force_iff`), the frame
conditions Rₘ ⊆ Rᵢ and reflexivity of Rₘ on the amalgam, and the
promise components of the canonical theories in the ◯-case (where
their ⊏-maximality trick, which uses irreflexivity/Löb, must be
replaced by idempotence-and-promise reasoning). -/
theorem amalgamation (X : Finset PLLFormula) (hX : SubClosed X)
    (p : String) (K M : ConstraintModel) (k₀ : K.W) (m₀ : M.W)
    (B : LayeredBisim (fun a => a ≠ p) K M)
    (hB : B.Z (2 * nu X + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ X, (N.force n₀ φ ↔ K.force k₀ φ) := by
  sorry

/-! ## 5. What the pillars would buy (the route's exit)

With `frag_reps_exist`, `layered_of_frag_agree` and `amalgamation`
in hand, their Theorem 5.1(2) argument yields, for every formula M
and variable p, that the rank-bounded join

  ∀p.M  :=  ⋁ { D ∈ Frag_{2ν+1}(V∖{p}) | D ⊢ M },   ν := nu (Sub M)

satisfies the full semantic specification `IsSemAll p M (that join)`
— and dually the meet at rank 2ν+2 for ∃p.  The residues
`BoxRowAmalgAll/Ex` of the box-commutation law become instances: the
row hypothesis contradicts the character-underivability
Θ⁺ ⊬ Θ⁻ ∨ ◯φ (the rank-completed form of our proved
`preTripleAll_cons_of_residue`), completeness produces the model K,
characters produce the layered link, and `amalgamation` produces the
p-variant the residue demands. -/

/-! ## Axiom audit (pinned for the PROVED results only) -/

/--
info: 'PLLND.SemUI.force_iff_of_layered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms force_iff_of_layered

/--
info: 'PLLND.SemUI.force_iff_of_bisim_via_layered' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms force_iff_of_bisim_via_layered

/--
info: 'PLLND.SemUI.layered_of_frag_agree_refuted' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms layered_of_frag_agree_refuted

/--
info: 'PLLND.SemUI.weak_escape_breaks_force_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms weak_escape_breaks_force_iff

/--
info: 'PLLND.SemUI.forkF_agree' does not depend on any axioms
-/
#guard_msgs in
#print axioms forkF_agree

/--
info: 'PLLND.SemUI.pair_escape_not_from_agreement' does not depend on any axioms
-/
#guard_msgs in
#print axioms pair_escape_not_from_agreement

end SemUI
end PLLND
