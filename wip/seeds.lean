import wip.connect

/-!
# New seeds: two identities and a fourth family — all PLL

Three candidate constructions investigated; two collapse into known
structure (which is itself news), one is a genuinely new family.

**1. Boxing the s-chain folds it into the c-chain**:

    ◯(s k) ≡ c (k+1)                                (`box_sC`)

Inside the box, the `c k`-disjunct climbs by `chain_step_le` and the
even disjunct enters by the unit; conversely `t(2k+3) ⊢ s k`
(`odd_le_sC`) boxes to `c (k+1) ⊢ ◯s k`.  Consequence: the PLL value
of the previously OPEN table cell `◯q9`:

    ◯q9 ≡ q12   in PLL                              (`boxq9_q12`)

(in PCLL both collapse to `q9` — the harvest's `◯q9 ≡ q9` cell — so
this is a clean PLL/PCLL divergence point: PLL keeps `◯s 1 = c 2`
strictly above `s 1`, PCLL flattens them.)

**2. Chain and gap meet at the anchor rung**:

    c k ∧ g k ≡ t(2k+1)                             (`chain_meet_gap`)

modus ponens one way, unit + weakening the other.  So at every level
the comb closes: the box and the collapse statement are complementary
over the odd rung.  Also `c k ⊢ ◯g k` (`chain_le_bg`), so the boxed
gap sits above BOTH teeth of the comb.

**3. w15 seeds a family with the EVEN-RUNG order type**:

    wC k := g k ∧ t(2k+4)                           (`wC 1 ≡ w15`)

The `wC k` are pairwise distinct, off the image, and ordered exactly
like the even rungs: `wC j ⊢ wC k` iff `j = k` or `j + 2 ≤ k`
(`wC_le`, `wC_strict`, `wC_succ_not_le`) — a "two-step chain" whose
consecutive members are incomparable.  Neither a chain nor an
antichain: a third order type among the families.

**Still open**: the second-order gaps `◯g k ⊃ g k` — on every model
in our edged-lift family they have the same truth set as `g k`, so
separating them (or proving the collapse) needs a new model idea.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## 1. The s-chain's boxes are the c-chain -/

/-- `q7 ≡ rnSub 5` — a classification instance at `¬p ∨ ¬¬p`. -/
theorem q7_rn5 : Interd q7 (rnSub 5) := by
  have h := rn_classification
    (A := (((PLLFormula.prop pv).ifThen .falsePLL)).or
      ((((PLLFormula.prop pv).ifThen .falsePLL)).ifThen .falsePLL))
    (by decide) (by decide)
  have e1 : embed ((((PLLFormula.prop pv).ifThen .falsePLL)).or
      ((((PLLFormula.prop pv).ifThen .falsePLL)).ifThen .falsePLL)) = q7 := by
    decide
  have e2 : cls ((((PLLFormula.prop pv).ifThen .falsePLL)).or
      ((((PLLFormula.prop pv).ifThen .falsePLL)).ifThen .falsePLL))
      = .odd 2 := by decide
  rw [e1, e2] at h
  exact h

/-- **`◯(s k) ≡ c (k+1)`**: boxing the s-chain folds it into the
c-chain, one level up. -/
theorem box_sC (k : Nat) : Interd ((sC k).somehow) (chainF (k + 1)) := by
  constructor
  · -- bind; inside the box each disjunct reaches ◯t(2k+3)
    refine dSomehowElim (Deriv.iden (.head _)) (Deriv.toHead ?_)
    refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · exact Deriv.toHead (chain_step_le k)
    · refine Deriv.toHead ?_
      refine Deriv.cutHead (rungD (eo_le (show k + 1 ≤ k + 1 from le_refl _))) ?_
      exact dSomehowIntro (Deriv.iden (.head _))
  · -- c (k+1) ⊢ ◯s k: box the en-masse arrow t(2k+3) ⊢ s k
    have h := box_mono (odd_le_sC k)
    have e : (2 : Nat) * k + 3 = 2 * (k + 1) + 1 := by omega
    rw [e] at h
    exact h

/-- **The PLL value of the open cell `◯q9`**: `◯q9 ≡ q12` in PLL
(PCLL collapses both to `q9`; this is a PLL/PCLL divergence point). -/
theorem boxq9_q12 : Interd (q9.somehow) q12 := by
  have h1 : Interd (q9.somehow) ((sC 1).somehow) :=
    (Interd.box_congr sC_one_q9).symm
  have h2 : Interd ((sC 1).somehow) (chainF 2) := box_sC 1
  have h3 : Interd (chainF 2) (q7.somehow) := by
    have := Interd.box_congr q7_rn5.symm
    exact this
  exact (h1.trans h2).trans h3

/-! ## 2. The comb closes: c k ∧ g k ≡ t(2k+1) -/

/-- **`c k ∧ g k ≡ t(2k+1)`**: modus ponens down, unit + weakening
up — chain and gap are complementary over the anchor rung. -/
theorem chain_meet_gap (k : Nat) :
    Interd ((chainF k).and (gap k)) (rnSub (2 * k + 1)) := by
  constructor
  · exact Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
      (Deriv.andElim1 (Deriv.iden (.head _)))
  · refine Deriv.andIntro (dSomehowIntro (Deriv.iden (.head _))) ?_
    exact rung_le_gap k

/-- `c k ⊢ ◯g k`: the boxed gap sits above both teeth of the comb. -/
theorem chain_le_bg (k : Nat) : Deriv [chainF k] ((gap k).somehow) :=
  box_mono (rung_le_gap k)

/-! ## 3. The w-family: even-rung order type -/

/-- The w15-family: `wC k := g k ∧ t(2k+4)`; `wC 1 ≡ w15` is
`w15_form`. -/
def wC (k : Nat) : PLLFormula := (gap k).and (rnSub (2 * k + 4))

theorem wC_one_w15 : Interd (wC 1) (q8.and q10) := w15_form

/-- On the plain lift `wC k` wears the truth set of the even rung
`t(2k+4)` (the gap conjunct is forced everywhere). -/
theorem wC_plain_iff (k w : Nat) :
    ladder.cm.force (some w) (wC k) ↔ (w + 1 ≤ k + 1 ∨ w = k + 2) := by
  constructor
  · intro h
    have hE := (h : ladder.cm.force (some w) (gap k) ∧
        ladder.cm.force (some w) (rnSub (2 * k + 4))).2
    have := (sat_rn_even (k + 1) w).mp
      ((ladder.transfer (rn_boxFree _) w).mp (by
        have e : (2 : Nat) * (k + 1) + 2 = 2 * k + 4 := by omega
        rw [e]
        exact hE))
    omega
  · intro hw
    refine ⟨plain_forces_gap k (some w), ?_⟩
    refine (ladder.transfer (rn_boxFree _) w).mpr ?_
    rw [show (2 * k + 4 : Nat) = 2 * (k + 1) + 2 from by omega]
    exact (sat_rn_even (k + 1) w).mpr (by omega)

/-- `wC j ⊢ wC k` for `j + 2 ≤ k` — the two-step ascent, via the even
conjunct alone (it supplies BOTH components at the higher level). -/
theorem wC_le {j k : Nat} (h : j + 2 ≤ k) : Deriv [wC j] (wC k) := by
  refine Deriv.andIntro ?_ ?_
  · -- the gap component, by weakening from the even rung
    refine Deriv.impIntro ?_
    -- ctx [chainF k, wC j] ⊢ rnSub (2k+1)
    have hE : Deriv [chainF k, wC j] (rnSub (2 * j + 4)) :=
      Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))
    refine Deriv.cutHead hE ?_
    have hr := rungD (eo_le (show (j + 1) + 1 ≤ k from by omega))
    rw [show (2 * (j + 1) + 2 : Nat) = 2 * j + 4 from by omega] at hr
    exact hr
  · -- the even component, by the even-rung order
    refine Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) ?_
    have hr := rungD (even_le_even (j + 1) (k + 1) (Or.inr (by omega)))
    rw [show (2 * (j + 1) + 2 : Nat) = 2 * j + 4 from by omega,
        show (2 * (k + 1) + 2 : Nat) = 2 * k + 4 from by omega] at hr
    exact hr

/-- `wC k ⊬ wC j` for `j < k`: refuted at plain-lift world `k+2`. -/
theorem wC_strict {j k : Nat} (h : j < k) : ¬ Deriv [wC k] (wC j) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (k + 2)) (fun ψ hψ => by
    have e : ψ = wC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (wC_plain_iff k (k + 2)).mpr (by omega))
  have := (wC_plain_iff j (k + 2)).mp hs
  omega

/-- `wC j ⊬ wC (j+1)`: consecutive members are incomparable (with
`wC_strict` this gives the even-rung order type). -/
theorem wC_succ_not_le (j : Nat) : ¬ Deriv [wC j] (wC (j + 1)) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (j + 2)) (fun ψ hψ => by
    have e : ψ = wC j := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (wC_plain_iff j (j + 2)).mpr (by omega))
  have := (wC_plain_iff (j + 1) (j + 2)).mp hs
  omega

/-- `wC k` matches no rung (PLL): plain agreement forces the even rung
`2k+4`, and the edged lift kills that (the gap conjunct fails at the
edge world where the even rung holds). -/
theorem wC_not_rung {k : Nat} (hk : 1 ≤ k) (n : Nat) :
    ¬ Interd (rnSub n) (wC k) := by
  rintro ⟨h1, h2⟩
  have hpt : ∀ w : Nat, ladder.sat (rn n) w ↔ (w + 1 ≤ k + 1 ∨ w = k + 2) := by
    intro w
    constructor
    · intro hw
      obtain ⟨d⟩ := h1
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (ladder.transfer (rn_boxFree n) w).mpr hw
        | tail _ h => cases h)
      exact (wC_plain_iff k w).mp hf
    · intro hw
      obtain ⟨d⟩ := h2
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (wC_plain_iff k w).mpr hw
        | tail _ h => cases h)
      exact (ladder.transfer (rn_boxFree n) w).mp hf
  have hI : Interd (rnSub n) (rnSub (2 * (k + 1) + 2)) := by
    constructor
    · exact (rnSub_deriv_iff n (2 * (k + 1) + 2)).mpr
        (fun w hw => (sat_rn_even (k + 1) w).mpr ((hpt w).mp hw))
    · exact (rnSub_deriv_iff (2 * (k + 1) + 2) n).mpr
        (fun w hw => (hpt w).mpr ((sat_rn_even (k + 1) w).mp hw))
  have hn : n = 2 * (k + 1) + 2 := by
    by_contra hne
    exact rn_pairwise_pll hne hI
  subst hn
  -- refute rung(2k+4) ⊢ wC k on the edged lift at the edge world k+2
  obtain ⟨d⟩ := h1
  have hs := soundness d (cmE (k - 1)) (some ((k - 1) + 3)) (fun ψ hψ => by
    have e : ψ = rnSub (2 * (k + 1) + 2) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    refine (cmE_transfer (k - 1) (rn_boxFree _) _).mpr ?_
    exact (sat_rn_even (k + 1) _).mpr (by omega))
  exact gap_fails (k - 1) k (by omega) (by omega)
    (hs : (cmE (k - 1)).force (some ((k - 1) + 3)) (gap k) ∧
      (cmE (k - 1)).force (some ((k - 1) + 3)) (rnSub (2 * k + 4))).1

/-- `wC k` is not `⊤` (PLL). -/
theorem wC_not_top (k : Nat) : ¬ Interd q1 (wC k) := by
  rintro ⟨h1, -⟩
  have h0 : Deriv [] (wC k) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  obtain ⟨d⟩ := h0
  have hs := soundness d ladder.cm (some (k + 1)) (fun ψ hψ => by cases hψ)
  have := (wC_plain_iff k (k + 1)).mp hs
  omega

/-- **`wC k ∉ im h`** (PLL, `k ≥ 1`). -/
theorem wC_off_image {k : Nat} (hk : 1 ≤ k) : ¬ InImage (wC k) :=
  not_inImage_of_offRungs (wC_not_rung hk) (wC_not_top k)

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.box_sC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms box_sC

/-- info: 'PLLND.RNEmbed.boxq9_q12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms boxq9_q12

/-- info: 'PLLND.RNEmbed.chain_meet_gap' does not depend on any axioms -/
#guard_msgs in
#print axioms chain_meet_gap

/-- info: 'PLLND.RNEmbed.wC_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wC_off_image

/-- info: 'PLLND.RNEmbed.wC_succ_not_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wC_succ_not_le

end RNEmbed
end PLLND
