import wip.bandStabilise

/-!
# The m-clauses: the infallible collapse, and the positive half

Branch `ui-confluence`.  Two results locating the m-clause difficulty
exactly at fallibility-grading (Matthew's observation, 2026-07-26: over
infallible models `◯⊥ ≡ ⊥` and RN(◯,{}) collapses to `{⊥, ⊤}`, so no
uniform-interpolation argument there can depend on tower structure).

1. `infallible_amalgamation` (PROVED, UNCONDITIONAL): between p-pure
   INFALLIBLE models the total link is a lawful `LayeredBisimE` — all
   eight clauses, the two m-clauses included, hold trivially — so the
   full one-variable amalgamation drops out with no agreement
   hypothesis at all.  This is the semantic form of the RN(◯,{})
   collapse under `¬◯⊥`: over infallible p-pure models, every
   variable-free formula is pointwise constant, p-blind bisimilarity
   says nothing, and any realisable p-theory rides any base model.  It
   is also a constructive non-vacuity certificate for the whole
   amalgamation tower (`witTripleC` → `stabilise` → `bandStabilise`):
   the machinery applies outright somewhere.

2. `band_mforth_positive` (PROVED): in the general fallible case, the
   POSITIVE half of the banded m-forth clause — an `Rₘ`-move `k ⟶ u`
   is answered by `m ⟶Rₘ u′` with `u′` forcing EVERY variable-free
   formula of crank ≤ α that `u` forces — by the character argument:
   `u` witnesses `◯(charPos u)` at `k` (bare possibility in K), the box
   crosses the link at rank `α + 3 ≤ R`, and bare possibility in M
   produces the witness.  What is NOT delivered is the negative half
   (`u′` may overshoot); that residue is the entire remaining content
   of `BandMforth`/`BandMback`, and by result 1 it is a phenomenon of
   fallible models only.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp
open ConfluentU

variable {p : String} {K M : ConstraintModel}

/-! ## 1. The infallible collapse -/

/-- No fallible worlds. -/
def FFree (C : ConstraintModel) : Prop := ∀ w : C.W, w ∉ C.F

/-- **The total link**: between p-pure infallible models, the constant
total family satisfies every clause of `LayeredBisimE` — the m-clauses
answer every move reflexively.  The m-clause difficulty is a
fallibility phenomenon. -/
def totalB (hPK : PPure p K) (hPM : PPure p M)
    (hFK : FFree K) (hFM : FFree M) :
    LayeredBisimWit (fun a => a ≠ p) K M where
  Z := fun _ _ _ => True
  mono := fun _ => trivial
  atoms := by
    intro n k m _ a ha
    exact iff_of_false (hPK a ha k) (hPM a ha m)
  fall := by
    intro n k m _
    exact iff_of_false (hFK k) (hFM m)
  iforth := by
    intro n k m _ v _
    exact .inl ⟨m, M.refl_i m, trivial⟩
  iback := by
    intro n k m _ v' _
    exact .inl ⟨k, K.refl_i k, trivial⟩
  mwit := by
    intro n k m _ ψ hex
    obtain ⟨κ, hkκ, hκψ⟩ := hex
    exact ⟨κ, m, hkκ, hκψ, M.refl_m m, .inl trivial⟩

/-- The adversarial side condition holds trivially for the total link. -/
theorem totalB_mback (hPK : PPure p K) (hPM : PPure p M)
    (hFK : FFree K) (hFM : FFree M) :
    (totalB hPK hPM hFK hFM).MBack := by
  intro n k m _ u' _
  exact ⟨k, K.refl_m k, .inl trivial⟩

/-- **The unconditional infallible amalgamation**: between p-pure
infallible models (K mutually confluent), the full p-variant conclusion
holds with NO agreement hypothesis — the semantic image of
RN(◯,{}) ≡ {⊥, ⊤} under `¬◯⊥`. -/
theorem infallible_amalgamation (cl : Finset PLLFormula)
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hPK : PPure p K) (hPM : PPure p M)
    (hFK : FFree K) (hFM : FFree M) (k₀ : K.W) (m₀ : M.W) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  amalgamation_assembledC cl (totalB hPK hPM hFK hFM) hcl hadeq hK
    (totalB_mback hPK hPM hFK hFM)
    (mforthResidue_of_stabilised cl (totalB hPK hPM hFK hFM) (fun h => h))
    k₀ m₀ trivial

/-! ## 2. The positive half of the banded m-clause -/

/-- **The m-forth clause, positive half** (general fallible case): over
mutually confluent `K` and `M`, an `Rₘ`-move `k ⟶ u` is answered by
`m ⟶Rₘ u′` preserving every variable-free formula of crank ≤ α that
`u` forces, provided the band floor covers the boxed positive
character (`α + 3 ≤ R`).  The proof: `u` forces its positive character
over the rank-α representatives (`force_charPos`); bare possibility in
`K` puts `◯(charPos u)` at `k`; the band link transfers it; bare
possibility in `M` produces the witness; `force_bigAnd_iff` unpacks it
on representatives, and interderivability carries it to every rank-α
formula.  The NEGATIVE half — that `u′` need not overshoot — is the
open remainder of `BandMforth`. -/
theorem band_mforth_positive {R α : Nat}
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hcr : α + 3 ≤ R)
    {k : K.W} {m : M.W} (hZ : bandAgree R K M k m)
    {u : K.W} (hu : K.Rm k u) :
    ∃ u', M.Rm m u' ∧ ∀ ρ : PLLFormula, ρ.atoms = ∅ → crank ρ ≤ α →
      K.force u ρ → M.force u' ρ := by
  classical
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' (∅ : Finset String) α
  set χ : PLLFormula := charPos K u L with hχ
  have hχatoms : χ.atoms = ∅ := by
    refine Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => ?_)
    exact Finset.notMem_empty a
      (atoms_charPos (fun D hD => (hL D hD).2) a ha)
  have hχcrank : crank χ ≤ α + 1 :=
    crank_charPos_le (fun D hD => (hL D hD).1)
  -- k forces ◯χ: u is the bare-possibility witness
  have hkbox : K.force k (PLLFormula.somehow χ) := by
    rw [force_somehow_iff_of_confluent hK]
    exact ⟨u, hu, force_charPos K u L⟩
  -- the box crosses the band link
  have hmbox : M.force m (PLLFormula.somehow χ) := by
    refine (hZ (PLLFormula.somehow χ) ?_ ?_).mp hkbox
    · show χ.atoms = ∅
      exact hχatoms
    · show crank χ + 2 ≤ R
      omega
  -- bare possibility in M produces the witness
  rw [force_somehow_iff_of_confluent hM] at hmbox
  obtain ⟨u', hmu', hχu'⟩ := hmbox
  refine ⟨u', hmu', fun ρ hρa hρc hρu => ?_⟩
  -- collapse ρ to a representative D forced by u
  obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
    (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
  have hInterd : Interd ρ D := ⟨hd₁, hd₂⟩
  have hDu : K.force u D := (interd_force_iff hInterd K u).mp hρu
  -- D is in the character's conjunction, so u′ forces it
  have hDu' : M.force u' D := by
    have := (force_bigAnd_iff M u' _).mp hχu'
    exact this D (List.mem_filter.mpr ⟨hDL, decide_eq_true hDu⟩)
  exact (interd_force_iff hInterd M u').mpr hDu'

/-! ## 3. The negative half closes under the band: the maximal-type ascent

The witness-form m-clause `BandMwit` is PROVED from the band collapse
plus confluence of both models.  The engine is the ASCENT: if the
M-partner of a ψ-witness's character overshoots, transfer the
overshoot back, and lift the ψ-witness over the returned world by the
confluence square — persistence keeps ψ, and the lifted witness's
type strictly grows.  Types live in a finite list, so the ascent
terminates at a ψ-witness whose type is exactly matched. -/

theorem countP_le_of_imp {l : List PLLFormula}
    {pq qq : PLLFormula → Bool}
    (h : ∀ a ∈ l, pq a = true → qq a = true) :
    l.countP pq ≤ l.countP qq := by
  induction l with
  | nil => simp
  | cons b l ih =>
      have hb := h b (List.mem_cons_self ..)
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      by_cases hpb : pq b = true
      · simp [List.countP_cons, hpb, hb hpb]
        omega
      · by_cases hqb : qq b = true <;>
          simp [List.countP_cons, hpb, hqb] <;> omega

theorem countP_lt_of_witness {l : List PLLFormula}
    {pq qq : PLLFormula → Bool}
    (h : ∀ a ∈ l, pq a = true → qq a = true) {a₀ : PLLFormula}
    (ha₀ : a₀ ∈ l) (hq : qq a₀ = true) (hp : ¬ pq a₀ = true) :
    l.countP pq < l.countP qq := by
  induction l with
  | nil => cases ha₀
  | cons b l ih =>
      have ht := countP_le_of_imp (fun a ha => h a (List.mem_cons_of_mem _ ha))
      rcases List.mem_cons.mp ha₀ with rfl | ha₀'
      · simp [List.countP_cons, hp, hq]
        omega
      · have hlt := ih (fun a ha => h a (List.mem_cons_of_mem _ ha)) ha₀'
        by_cases hpb : pq b = true
        · simp [List.countP_cons, hpb, h b (List.mem_cons_self ..) hpb]
          omega
        · by_cases hqb : qq b = true <;>
            simp [List.countP_cons, hpb, hqb] <;> omega

theorem countP_le_length' {l : List PLLFormula}
    {pq : PLLFormula → Bool} : l.countP pq ≤ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
      by_cases hpb : pq b = true <;> simp [List.countP_cons, hpb] <;> omega

theorem all_of_countP_ge {l : List PLLFormula}
    {pq : PLLFormula → Bool} (h : l.length ≤ l.countP pq) :
    ∀ a ∈ l, pq a = true := by
  induction l with
  | nil => intro a ha; cases ha
  | cons b l ih =>
      intro a ha
      by_cases hpb : pq b = true
      · rcases List.mem_cons.mp ha with rfl | ha'
        · exact hpb
        · refine ih ?_ a ha'
          simp [List.countP_cons, hpb] at h
          omega
      · exfalso
        have := countP_le_length' (l := l) (pq := pq)
        simp [List.countP_cons, hpb] at h
        omega

/-- **One transfer step, forward**: the positive rank-R character of a
K-row world crosses the link (boxed, collapsed by the band) and bare
possibility in M realises it: some M-row world forces everything the
K-row world forces among the representatives. -/
theorem band_row_char_partner {R : Nat} (hR : 1 ≤ R)
    (hband : BandCollapse R (2 * R + 2))
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k : K.W} {m : M.W} (hZ : bandAgree R K M k m)
    {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ R ∧ ∀ a ∈ D.atoms, a ∈ (∅ : Finset String))
    {κ : K.W} (hkκ : K.Rm k κ) :
    ∃ u', M.Rm m u' ∧ ∀ D ∈ L, K.force κ D → M.force u' D := by
  classical
  set χ : PLLFormula := charPos K κ L with hχdef
  have hχa : χ.atoms = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
      Finset.notMem_empty a
        (atoms_charPos (fun D hD => (hL D hD).2) a ha))
  have hχc : crank χ ≤ R + 1 :=
    crank_charPos_le (fun D hD => (hL D hD).1)
  have hkbox : K.force k (PLLFormula.somehow χ) := by
    rw [force_somehow_iff_of_confluent hK]
    exact ⟨κ, hkκ, force_charPos K κ L⟩
  have hmbox : M.force m (PLLFormula.somehow χ) := by
    refine (band_agree_stab hband hZ (PLLFormula.somehow χ) ?_ ?_).mp hkbox
    · show χ.atoms = ∅
      exact hχa
    · show crank χ + 2 ≤ 2 * R + 2
      omega
  rw [force_somehow_iff_of_confluent hM] at hmbox
  obtain ⟨u', hmu', hχu'⟩ := hmbox
  refine ⟨u', hmu', fun D hD hκD => ?_⟩
  exact (force_bigAnd_iff M u' _).mp hχu' D
    (List.mem_filter.mpr ⟨hD, decide_eq_true hκD⟩)

/-- **One transfer step, backward**: symmetrically, an M-row world's
character is realised in K's row. -/
theorem band_row_char_partner_rev {R : Nat} (hR : 1 ≤ R)
    (hband : BandCollapse R (2 * R + 2))
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    {k : K.W} {m : M.W} (hZ : bandAgree R K M k m)
    {L : List PLLFormula}
    (hL : ∀ D ∈ L, crank D ≤ R ∧ ∀ a ∈ D.atoms, a ∈ (∅ : Finset String))
    {u' : M.W} (hmu' : M.Rm m u') :
    ∃ κ', K.Rm k κ' ∧ ∀ D ∈ L, M.force u' D → K.force κ' D := by
  classical
  set χ : PLLFormula := charPos M u' L with hχdef
  have hχa : χ.atoms = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr (fun a ha =>
      Finset.notMem_empty a
        (atoms_charPos (fun D hD => (hL D hD).2) a ha))
  have hχc : crank χ ≤ R + 1 :=
    crank_charPos_le (fun D hD => (hL D hD).1)
  have hmbox : M.force m (PLLFormula.somehow χ) := by
    rw [force_somehow_iff_of_confluent hM]
    exact ⟨u', hmu', force_charPos M u' L⟩
  have hkbox : K.force k (PLLFormula.somehow χ) := by
    refine (band_agree_stab hband hZ (PLLFormula.somehow χ) ?_ ?_).mpr hmbox
    · show χ.atoms = ∅
      exact hχa
    · show crank χ + 2 ≤ 2 * R + 2
      omega
  rw [force_somehow_iff_of_confluent hK] at hkbox
  obtain ⟨κ', hkκ', hχκ'⟩ := hkbox
  refine ⟨κ', hkκ', fun D hD hu'D => ?_⟩
  exact (force_bigAnd_iff K κ' _).mp hχκ' D
    (List.mem_filter.mpr ⟨hD, decide_eq_true hu'D⟩)

/-- **The witness-form m-clause is DISCHARGED under the band** (the
maximal-type ascent): over mutually confluent `K` and `M` with the
band collapse at `(R, 2R+2)`, `BandMwit R K M` holds outright.

The ascent: take any ψ-witness κ in k's row.  Its character crosses to
an M-row partner u′ (forward step).  If u′'s representative type
matches κ's exactly, type-equality is rank-R agreement and we are
done.  Otherwise u′ overshoots at some representative D₀; the backward
step returns a K-row world κ′ covering u′'s type, and the CONFLUENCE
SQUARE over (Rₘ k κ, Rᵢ k κ′) yields y ∈ row(k) above both — y keeps
ψ by persistence along Rᵢ κ y and swallows κ′'s type by persistence
along Rₘ κ′ y, so y is a ψ-witness whose type strictly grew (it gained
D₀).  Types live in the finite representative list, so the deficit
`L.length − count` strictly drops and the ascent terminates in the
matched case.  No fallible escape is ever needed. -/
theorem bandMwit_of_collapse {R : Nat} (hR : 1 ≤ R)
    (hband : BandCollapse R (2 * R + 2))
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M) :
    BandMwit R K M := by
  classical
  intro k m hZ ψ hex
  obtain ⟨L, hL, hrep⟩ := frag_reps_exist' (∅ : Finset String) R
  suffices main : ∀ (n : Nat) (κ : K.W), K.Rm k κ → K.force κ ψ →
      L.length ≤ L.countP (fun D => decide (K.force κ D)) + n →
      ∃ κ' u', K.Rm k κ' ∧ K.force κ' ψ ∧ M.Rm m u' ∧
        (bandAgree R K M κ' u' ∨ (κ' ∈ K.F ∧ u' ∈ M.F)) by
    obtain ⟨κ₀, hkκ₀, hκ₀ψ⟩ := hex
    exact main L.length κ₀ hkκ₀ hκ₀ψ (Nat.le_add_left _ _)
  intro n
  induction n with
  | zero =>
      intro κ hkκ hκψ hcount
      obtain ⟨u', hmu', hpres⟩ :=
        band_row_char_partner hR hband hK hM hZ hL hkκ
      have hall : ∀ D ∈ L, K.force κ D := fun D hD =>
        of_decide_eq_true (all_of_countP_ge (by omega) D hD)
      refine ⟨κ, u', hkκ, hκψ, hmu', .inl fun ρ hρa hρc => ?_⟩
      obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
        (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
      have hI : Interd ρ D := ⟨hd₁, hd₂⟩
      exact iff_of_true
        ((interd_force_iff hI K κ).mpr (hall D hDL))
        ((interd_force_iff hI M u').mpr (hpres D hDL (hall D hDL)))
  | succ n ih =>
      intro κ hkκ hκψ hcount
      obtain ⟨u', hmu', hpres⟩ :=
        band_row_char_partner hR hband hK hM hZ hL hkκ
      by_cases hsub : ∀ D ∈ L, M.force u' D → K.force κ D
      · -- exact type match: rank-R agreement
        refine ⟨κ, u', hkκ, hκψ, hmu', .inl fun ρ hρa hρc => ?_⟩
        obtain ⟨D, hDL, hd₁, hd₂⟩ := hrep ρ hρc
          (fun a ha => by rw [hρa] at ha; exact absurd ha (Finset.notMem_empty a))
        have hI : Interd ρ D := ⟨hd₁, hd₂⟩
        exact ((interd_force_iff hI K κ).trans
          (Iff.intro (hpres D hDL) (hsub D hDL))).trans
            (interd_force_iff hI M u').symm
      · -- overshoot at D₀: ascend
        push_neg at hsub
        obtain ⟨D₀, hD₀L, hD₀u, hD₀κ⟩ := hsub
        obtain ⟨κ', hkκ', hpres'⟩ :=
          band_row_char_partner_rev hR hband hK hM hZ hL hmu'
        obtain ⟨y, hκy, hκ'y⟩ := hK hkκ (K.sub_mi hkκ')
        have hky : K.Rm k y := K.trans_m hkκ' hκ'y
        have hyψ : K.force y ψ := K.force_hered hκy hκψ
        have hchain : ∀ D ∈ L, K.force κ D → K.force y D := fun D hD h =>
          K.force_hered (K.sub_mi hκ'y) (hpres' D hD (hpres D hD h))
        have hyD₀ : K.force y D₀ :=
          K.force_hered (K.sub_mi hκ'y) (hpres' D₀ hD₀L hD₀u)
        have hlt : L.countP (fun D => decide (K.force κ D)) <
            L.countP (fun D => decide (K.force y D)) := by
          refine countP_lt_of_witness
            (fun D hD h => decide_eq_true (hchain D hD (of_decide_eq_true h)))
            hD₀L (decide_eq_true hyD₀) ?_
          simp only [decide_eq_true_eq]
          exact hD₀κ
        exact ih y hky hyψ (by omega)

/-- **The banded one-variable amalgamation, second form**: the
witness-form m-clause is no longer a hypothesis — it is paid by the
ascent.  What remains of the entire route: the band collapse (the
plateau) and the single adversarial clause `BandMback`. -/
theorem restricted_amalgamation_oneVar_band' (cl : Finset PLLFormula)
    (R : Nat) (hR : 1 ≤ R) (hband : BandCollapse R (2 * R + 2))
    (hcl : SubClosed cl) (hadeq : OBoxAdeq cl)
    (hK : MutuallyConfluent K) (hM : MutuallyConfluent M)
    (hPK : PPure p K) (hPM : PPure p M)
    (hmb : BandMback R K M)
    (k₀ : K.W) (m₀ : M.W)
    (hagree : bandAgree R K M k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) :=
  restricted_amalgamation_oneVar_band cl R hband hcl hadeq hK hPK hPM
    (bandMwit_of_collapse hR hband hK hM) hmb k₀ m₀ hagree

/-! ## Axiom audit -/

/--
info: 'PLLND.SemUI.infallible_amalgamation' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms infallible_amalgamation

/--
info: 'PLLND.SemUI.band_mforth_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms band_mforth_positive

/--
info: 'PLLND.SemUI.bandMwit_of_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms bandMwit_of_collapse

/--
info: 'PLLND.SemUI.restricted_amalgamation_oneVar_band'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms restricted_amalgamation_oneVar_band'


end SemUI
end PLLND
