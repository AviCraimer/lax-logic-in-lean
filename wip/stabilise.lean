import wip.witTripleC
import wip.residueGrowth
import LaxLogic.PLLSemUIChar

/-!
# The stabilisation lemma, via the cross-route plan

Branch `ui-confluence`.  The syntactic route's certified fact — the
variable-free fragment closes into finitely many interderivability
classes (the RN(◯,{}) dictionary, 15 classes, connective-closed) —
becomes the semantic stabilisation lemma, and the stabilisation lemma
discharges the residue.  The chain:

1. `RNDict`: the interface for a certified dictionary — finitely many
   variable-free representatives, closed under every connective up to
   `Interd`, with a crank bound.  (Instantiated separately from the
   certified closure tables; every theorem here takes `D : RNDict` as a
   hypothesis, so this file is sorry-free NOW and becomes unconditional
   the moment the instantiation lands.)
2. `dict_collapse` (PROVED): by structural induction with the `Interd`
   congruence calculus, EVERY variable-free formula is interderivable
   with a representative.  This is the step that turns the finite
   closure certificate into a statement about the whole fragment — the
   answer to the recorded worry that "finitely many probes cannot
   settle the fragment": closure under the generating connectives can.
3. `dict_agree_stab` (PROVED): agreement at rank `D.crankBound` is
   agreement at EVERY rank — variable-free agreement STABILISES.  The
   semantic form of "the ladder stabilises"; over models this is what
   the certified r-tables observe.
4. `vfB` (PROVED, modulo the two m-clauses taken as hypotheses): the
   CONSTANT link family `Z n := vfAgree` is a lawful `LayeredBisimE`
   between p-pure models — atoms by purity, `fall` at rank 0, the
   i-clauses from `agree_iforth`/`agree_iback` at alphabet ∅ with the
   character budget `2α+2` absorbed by stabilisation.
5. `vfB_mforthResidue` (PROVED): a constant family satisfies the
   level-collapse hypothesis definitionally, so `MforthResidue` holds
   for `vfB` — THE RESIDUE IS DISCHARGED in the one-variable setting.
6. `restricted_amalgamation_oneVar` (PROVED): the full amalgamation for
   p-pure confluent `K`, at entry rank `D.crankBound` (not
   `2·cl.card+1`!), with no residue hypothesis.  What remains of the
   whole route in this setting is exactly `VfMwit`/`VfMback` — the
   witness-form m-clause and the adversarial m-back, nothing else.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The dictionary interface -/

/-- A **certified variable-free dictionary**: finitely many variable-free
representatives, a crank bound, and connective-closure up to `Interd`
(with certified tables).  The RN(◯,{}) instantiation has 15 classes. -/
structure RNDict where
  n : Nat
  rep : Fin n → PLLFormula
  rep_varFree : ∀ i, (rep i).atoms = ∅
  crankBound : Nat
  rep_crank_le : ∀ i, crank (rep i) ≤ crankBound
  botIdx : Fin n
  bot_interd : Interd PLLFormula.falsePLL (rep botIdx)
  andIdx : Fin n → Fin n → Fin n
  orIdx : Fin n → Fin n → Fin n
  impIdx : Fin n → Fin n → Fin n
  boxIdx : Fin n → Fin n
  and_interd : ∀ i j, Interd ((rep i).and (rep j)) (rep (andIdx i j))
  or_interd : ∀ i j, Interd ((rep i).or (rep j)) (rep (orIdx i j))
  imp_interd : ∀ i j, Interd ((rep i).ifThen (rep j)) (rep (impIdx i j))
  box_interd : ∀ i, Interd (PLLFormula.somehow (rep i)) (rep (boxIdx i))

/-- Interderivable formulas force alike, by sequent soundness. -/
theorem interd_force_iff {φ ψ : PLLFormula} (h : Interd φ ψ)
    (C : ConstraintModel) (w : C.W) : C.force w φ ↔ C.force w ψ := by
  obtain ⟨⟨d₁⟩, ⟨d₂⟩⟩ := h
  constructor
  · intro hf
    exact soundness d₁ C w (fun χ hχ => by
      rcases List.mem_singleton.mp hχ with rfl
      exact hf)
  · intro hf
    exact soundness d₂ C w (fun χ hχ => by
      rcases List.mem_singleton.mp hχ with rfl
      exact hf)

/-! ## 2. Collapse: every variable-free formula is a dictionary class -/

theorem atoms_empty_left {A B : PLLFormula} (h : A.atoms ∪ B.atoms = ∅) :
    A.atoms = ∅ := (Finset.union_eq_empty.mp h).1

theorem atoms_empty_right {A B : PLLFormula} (h : A.atoms ∪ B.atoms = ∅) :
    B.atoms = ∅ := (Finset.union_eq_empty.mp h).2

/-- **The collapse**: by structural induction with the `Interd`
congruence calculus, every variable-free formula is interderivable with
a dictionary representative.  The finite connective-closure certificate
decides the whole fragment. -/
theorem dict_collapse (D : RNDict) :
    ∀ φ : PLLFormula, φ.atoms = ∅ → ∃ i, Interd φ (D.rep i) := by
  intro φ
  induction φ with
  | prop a =>
      intro h
      rw [atoms_prop] at h
      exact absurd h (by simp)
  | falsePLL =>
      intro _
      exact ⟨D.botIdx, D.bot_interd⟩
  | and A B ihA ihB =>
      intro h
      rw [atoms_and] at h
      obtain ⟨i, hi⟩ := ihA (atoms_empty_left h)
      obtain ⟨j, hj⟩ := ihB (atoms_empty_right h)
      exact ⟨D.andIdx i j, (Interd.and_congr hi hj).trans (D.and_interd i j)⟩
  | or A B ihA ihB =>
      intro h
      rw [atoms_or] at h
      obtain ⟨i, hi⟩ := ihA (atoms_empty_left h)
      obtain ⟨j, hj⟩ := ihB (atoms_empty_right h)
      exact ⟨D.orIdx i j, (Interd.or_congr hi hj).trans (D.or_interd i j)⟩
  | ifThen A B ihA ihB =>
      intro h
      rw [atoms_ifThen] at h
      obtain ⟨i, hi⟩ := ihA (atoms_empty_left h)
      obtain ⟨j, hj⟩ := ihB (atoms_empty_right h)
      exact ⟨D.impIdx i j, (Interd.imp_congr hi hj).trans (D.imp_interd i j)⟩
  | somehow A ihA =>
      intro h
      obtain ⟨i, hi⟩ := ihA h
      exact ⟨D.boxIdx i, (Interd.box_congr hi).trans (D.box_interd i)⟩

/-! ## 3. The stabilisation lemma -/

/-- Full variable-free agreement between two worlds. -/
def vfAgree (K M : ConstraintModel) (k : K.W) (m : M.W) : Prop :=
  ∀ ρ : PLLFormula, ρ.atoms = ∅ → (K.force k ρ ↔ M.force m ρ)

/-- **The stabilisation lemma**: variable-free agreement at rank
`D.crankBound` is agreement at EVERY rank.  Any formula collapses to a
representative below the bound, and interderivability preserves
forcing on both sides. -/
theorem dict_agree_stab (D : RNDict) {k : K.W} {m : M.W}
    (h : ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ D.crankBound →
      (K.force k ρ ↔ M.force m ρ)) :
    vfAgree K M k m := by
  intro φ hφ
  obtain ⟨i, hi⟩ := dict_collapse D φ hφ
  exact (interd_force_iff hi K k).trans
    ((h (D.rep i) (D.rep_varFree i) (D.rep_crank_le i)).trans
      (interd_force_iff hi M m).symm)

/-! ## 4. The constant link family -/

/-- A model is **p-pure** when no atom other than `p` is decorated. -/
def PPure (p : String) (C : ConstraintModel) : Prop :=
  ∀ a, a ≠ p → ∀ w : C.W, w ∉ C.V a

/-- The two m-clauses of the constant family — the exact remaining
pillar-2 obligation in the one-variable setting. -/
def VfMforth (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, vfAgree K M k m → ∀ {u : K.W}, K.Rm k u →
    ∃ u', M.Rm m u' ∧ (vfAgree K M u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- The WITNESS form of the constant-link m-forth obligation: only some
row-witness of a given formula needs an answered partner.  Strictly
weaker than `VfMforth` (`vfMwit_of_vfMforth`); this is all the
amalgamation consumes. -/
def VfMwit (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, vfAgree K M k m → ∀ {ψ : PLLFormula},
    (∃ κ, K.Rm k κ ∧ K.force κ ψ) →
      ∃ κ u', K.Rm k κ ∧ K.force κ ψ ∧ M.Rm m u' ∧
        (vfAgree K M κ u' ∨ (κ ∈ K.F ∧ u' ∈ M.F))

theorem vfMwit_of_vfMforth {K M : ConstraintModel} (h : VfMforth K M) :
    VfMwit K M := by
  intro k m hZ ψ hex
  obtain ⟨κ, hkκ, hκψ⟩ := hex
  obtain ⟨u', hmu', hres⟩ := h hZ hkκ
  exact ⟨κ, u', hkκ, hκψ, hmu', hres⟩

def VfMback (K M : ConstraintModel) : Prop :=
  ∀ {k : K.W} {m : M.W}, vfAgree K M k m → ∀ {u' : M.W}, M.Rm m u' →
    ∃ u, K.Rm k u ∧ (vfAgree K M u u' ∨ (u ∈ K.F ∧ u' ∈ M.F))

/-- **The constant link family**: `Z n := vfAgree`, a lawful
`LayeredBisimE` off `p` between p-pure models.  Atoms by purity, `fall`
at rank 0, the i-clauses by the character argument at alphabet ∅ with
its `2α+2` budget absorbed by stabilisation; the m-clauses are the
hypotheses. -/
def vfB (D : RNDict) (hPK : PPure p K) (hPM : PPure p M)
    (hmf : VfMwit K M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := fun _ k m => vfAgree K M k m
  mono := fun h => h
  atoms := by
    intro n k m _ a ha
    exact iff_of_false (hPK a ha k) (hPM a ha m)
  fall := by
    intro n k m hZ
    exact hZ PLLFormula.falsePLL atoms_false
  iforth := by
    intro n k m hZ v hv
    by_cases hvF : v ∈ K.F
    · exact .inr hvF
    · obtain ⟨v', hv', hagr⟩ :=
        agree_iforth (V := (∅ : Finset String)) (α := D.crankBound)
          (fun χ _ hA => hZ χ (Finset.eq_empty_iff_forall_notMem.mpr
            (fun a ha => Finset.notMem_empty a (hA a ha)))) hv hvF
      refine .inl ⟨v', hv', dict_agree_stab D (fun ρ hρ hcr => ?_)⟩
      exact hagr ρ (le_trans hcr (by omega)) (fun a ha => by
        rw [hρ] at ha
        exact ha)
  iback := by
    intro n k m hZ v' hv'
    by_cases hvF : v' ∈ M.F
    · exact .inr hvF
    · obtain ⟨v, hv, hagr⟩ :=
        agree_iback (V := (∅ : Finset String)) (α := D.crankBound)
          (fun χ _ hA => hZ χ (Finset.eq_empty_iff_forall_notMem.mpr
            (fun a ha => Finset.notMem_empty a (hA a ha)))) hv' hvF
      refine .inl ⟨v, hv, dict_agree_stab D (fun ρ hρ hcr => ?_)⟩
      exact hagr ρ (le_trans hcr (by omega)) (fun a ha => by
        rw [hρ] at ha
        exact ha)
  mwit := by
    intro n k m hZ ψ hex
    exact hmf hZ hex

/-- The adversarial side condition, from `VfMback`. -/
theorem vfB_mback (D : RNDict) (hPK : PPure p K) (hPM : PPure p M)
    (hmf : VfMwit K M) (hmb : VfMback K M) :
    (vfB D hPK hPM hmf).MBack := by
  intro n k m hZ u' hu'
  exact hmb hZ hu'

/-! ## 5. The residue is discharged for the constant family -/

/-- A constant family satisfies the level-collapse hypothesis
definitionally: **`MforthResidue` holds for `vfB`.**  The stabilisation
lemma has paid the residue. -/
theorem vfB_mforthResidue (cl : Finset PLLFormula) (D : RNDict)
    (hPK : PPure p K) (hPM : PPure p M)
    (hmf : VfMwit K M) :
    MforthResidue cl (vfB D hPK hPM hmf) :=
  mforthResidue_of_stabilised cl (vfB D hPK hPM hmf) (fun h => h)

/-! ## 6. The one-variable amalgamation, residue-free -/

/-- **The restricted amalgamation** (one-variable setting): for p-pure
mutually confluent `K` and p-pure `M`, from variable-free agreement of
the roots at rank `D.crankBound` — a FIXED finite rank, independent of
the closure — the full p-variant conclusion, with NO residue
hypothesis.  Everything that remains of the route here is
`VfMforth`/`VfMback`: the two m-clauses of pillar 2. -/
theorem restricted_amalgamation_oneVar (cl : Finset PLLFormula)
    (D : RNDict) (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hPK : PPure p K) (hPM : PPure p M)
    (hmf : VfMwit K M) (hmb : VfMback K M)
    (k₀ : K.W) (m₀ : M.W)
    (hagree : ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ D.crankBound →
      (K.force k₀ ρ ↔ M.force m₀ ρ)) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  amalgamation_assembledC cl (vfB D hPK hPM hmf) hcl hadeq hK
    (vfB_mback D hPK hPM hmf hmb)
    (vfB_mforthResidue cl D hPK hPM hmf) k₀ m₀
    (dict_agree_stab D hagree)

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.dict_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dict_collapse

/--
info: 'PLLND.SemUI.dict_agree_stab' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms dict_agree_stab

/--
info: 'PLLND.SemUI.vfB_mforthResidue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms vfB_mforthResidue

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar

end SemUI
end PLLND
