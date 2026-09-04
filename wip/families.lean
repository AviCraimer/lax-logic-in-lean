import wip.laxNeg
import wip.gapWidth

/-!
# The families seeded by q9, q13, q14 — and the gap antichain is new

**Everything in this file is PLL** (`Deriv`/`Interd` = `LaxND`
derivability); no `DerivU`/`InterdU` (PCLL) appears.  The refutations
are by `soundness` on constraint models, which refutes PLL.

## Part 1 — the gap antichain coincides with nothing known

`gap_not_q9`, `gap_not_q13`, `gap_not_q14`, `gap_not_w15`: for every
`k` (≥ 2 where the statement needs it), `gap k` is interderivable with
none of the four dictionary classes not already covered
(`gap_not_rung`, `gap_not_top`, `gap_not_chain`, and
`gap_incomparable` at `gap 1 ≡ q8` cover all the others).  Method: on
the plain abyss lift `gap k` is forced at EVERY world
(`plain_forces_gap`), so it cannot match any class that fails
somewhere there — and `q9`, `q14`, `w15` all fail at world 3 or 2.
`q13 = ◯q8` is forced everywhere on the plain lift, so it needs the
order argument instead: `q8 ⊢ ◯q8` is the unit, so `gap k ≡ q13`
would give `gap 1 ⊢ gap k`, against `gap_incomparable`.

## Part 2 — the probes: q9, q13, q14 each seed an infinite family

New canonical forms (`sC 1 ≡ q9`, `rC 1 ≡ q14`, `(gap 1).somehow ≡ q13`):

    sC k := chainF k ∨ rnSub (2k+2)          (q9-family)
    rC k := rnSub (2k+4) ⊃ chainF k          (q14-family)
    bg k := (gap k).somehow                  (q13-family)

* **q9 seeds a strict CHAIN**: `sC j ⊢ sC k` for `j ≤ k` (`sC_le`),
  strict at every step (`sC_strict`), every member off the image
  (`sC_off_image`) and no chain class (`sC_not_chain` — the plain
  truth sets of `sC k` and `chainF (k+1)` agree, so this needs the
  edged lift).
* **q14 seeds an ANTICHAIN**: the `rC k` are pairwise ⊬-incomparable
  for ALL `j ≠ k ≥ 1` (`rC_incomparable` — stronger than the gaps,
  no `k ≥ 2` restriction), and off the image (`rC_off_image`).
* **q13 seeds an ANTICHAIN**: the boxed gaps `(gap k).somehow` are
  pairwise incomparable for `j ≠ k ≥ 2` (`bg_incomparable`), off the
  image and off the chain (`bg_off_image`, `bg_not_chain`).

Model bookkeeping, all on the ONE edged-lift family `cmE m`: `gap k`
fails in `cmE m` exactly at the worlds whose cone contains the edge
world `m+3`, when `k` is in the window `{m+1, m+2}` — so `bg k` fails
exactly ABOVE the edge world (`[m+5,∞)`), which is what makes the
boxed family separable at world `m+5`.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-! ## The new canonical forms and their dictionary bridges -/

/-- The q9-family: `sC k := chainF k ∨ rnSub (2k+2)`. -/
def sC (k : Nat) : PLLFormula := (chainF k).or (rnSub (2 * k + 2))

/-- The q14-family: `rC k := rnSub (2k+4) ⊃ chainF k`. -/
def rC (k : Nat) : PLLFormula := (rnSub (2 * k + 4)).ifThen (chainF k)

/-- `sC 1 ≡ q9` (PLL). -/
theorem sC_one_q9 : Interd (sC 1) q9 :=
  Interd.or_congr chainF_one_q5 q6_rn4.symm

/-- `rC 1 ≡ q14` (PLL). -/
theorem rC_one_q14 : Interd (rC 1) q14 :=
  Interd.imp_congr q10_rn6.symm chainF_one_q5

/-- `(gap 1).somehow ≡ q13` (PLL) — `q13` IS `◯q8` syntactically. -/
theorem bg_one_q13 : Interd ((gap 1).somehow) q13 :=
  Interd.box_congr gap_one_q8

/-- `w15 ≡ gap 1 ∧ rnSub 6` (PLL) — `w15` IS `q8 ∧ q10` syntactically. -/
theorem w15_form : Interd ((gap 1).and (rnSub 6)) (q8.and q10) :=
  Interd.and_congr gap_one_q8 q10_rn6.symm

/-! ## Part 1: the gap antichain is new

The reusable step: nothing that fails at some plain-lift world can be
interderivable with any `gap k`. -/

theorem not_interd_gap_of_unforced {X : PLLFormula} (w : Nat)
    (hw : ¬ ladder.cm.force (some w) X) (k : Nat) :
    ¬ Interd (gap k) X := by
  rintro ⟨h1, -⟩
  obtain ⟨d⟩ := h1
  refine hw (soundness d ladder.cm (some w) (fun ψ hψ => ?_))
  have e : ψ = gap k := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  exact plain_forces_gap k (some w)

/-! World-level facts on the plain abyss lift (`T(q3) = {1}`,
`T(q5) = {0,1}`, `T(q6) = {0,2}`, `T(q10) = {0,1,3}`). -/

theorem l3_not_q3 : ¬ ladder.cm.force (some 3) q3 := by
  intro h
  have h' : ∀ v : Option Nat, ladder.cm.Ri (some 3) v →
      ladder.cm.force v q2 → ladder.cm.force v q0 := h
  have h0 := h' (some 0) (Or.inr (by omega))
    ((Skel.force_oBot ladder 0).mpr rfl)
  exact absurd (h0 : (some 0 : Option Nat) = none) (Option.some_ne_none 0)

theorem l1_q3 : ladder.cm.force (some 1) q3 := by
  show ∀ v : Option Nat, ladder.cm.Ri (some 1) v →
    ladder.cm.force v q2 → ladder.cm.force v q0
  intro v hv h2
  cases v with
  | none => exact ladder.cm.force_of_fallible rfl
  | some y =>
      have hy : y = 1 := by
        rcases (hv : y = 1 ∨ y + 2 ≤ 1) with rfl | h <;> omega
      subst hy
      have := (Skel.force_oBot ladder 1).mp h2
      exact absurd (ladder_U.mp this) (by omega)

theorem l3_not_q5 : ¬ ladder.cm.force (some 3) q5 := by
  intro h
  rcases (Skel.box_force ladder q3 3).mp h 3 (Or.inl rfl) with hU | hf
  · exact absurd (ladder_U.mp hU) (by omega)
  · exact l3_not_q3 hf

theorem l3_not_q6 : ¬ ladder.cm.force (some 3) q6 := by
  intro h
  have h' : ∀ v : Option Nat, ladder.cm.Ri (some 3) v →
      ladder.cm.force v q3 → ladder.cm.force v q0 := h
  have h0 := h' (some 1) (Or.inr (by omega)) l1_q3
  exact absurd (h0 : (some 1 : Option Nat) = none) (Option.some_ne_none 1)

theorem l3_q10 : ladder.cm.force (some 3) q10 := by
  obtain ⟨d⟩ := q10_rn6.2
  refine soundness d ladder.cm (some 3) (fun ψ hψ => ?_)
  have e : ψ = rnSub 6 := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  refine (ladder.transfer (rn_boxFree 6) 3).mpr ?_
  show ladder.sat (rn (2 * 2 + 2)) 3
  exact (sat_rn_even 2 3).mpr (by omega)

theorem l3_not_q14 : ¬ ladder.cm.force (some 3) q14 := by
  intro h
  have h' : ∀ v : Option Nat, ladder.cm.Ri (some 3) v →
      ladder.cm.force v q10 → ladder.cm.force v q5 := h
  exact l3_not_q5 (h' (some 3) (Or.inl rfl) l3_q10)

theorem l2_not_q10 : ¬ ladder.cm.force (some 2) q10 := by
  intro h
  obtain ⟨d⟩ := q10_rn6.1
  have hf := soundness d ladder.cm (some 2) (fun ψ hψ => by
    have e : ψ = q10 := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact h)
  have hs := (ladder.transfer (rn_boxFree 6) 2).mp hf
  have := (sat_rn_even 2 2).mp hs
  omega

/-- **`gap k ≢ q9` for every `k`** (PLL): `q9` fails at plain-lift
world 3, `gap k` never fails. -/
theorem gap_not_q9 (k : Nat) : ¬ Interd (gap k) q9 :=
  not_interd_gap_of_unforced 3
    (fun h => by
      rcases (h : ladder.cm.force (some 3) q5 ∨ ladder.cm.force (some 3) q6)
        with h5 | h6
      · exact l3_not_q5 h5
      · exact l3_not_q6 h6) k

/-- **`gap k ≢ q14` for every `k`** (PLL). -/
theorem gap_not_q14 (k : Nat) : ¬ Interd (gap k) q14 :=
  not_interd_gap_of_unforced 3 l3_not_q14 k

/-- **`gap k ≢ w15 = q8 ∧ q10` for every `k`** (PLL). -/
theorem gap_not_w15 (k : Nat) : ¬ Interd (gap k) (q8.and q10) :=
  not_interd_gap_of_unforced 2
    (fun h => l2_not_q10
      (h : ladder.cm.force (some 2) q8 ∧ ladder.cm.force (some 2) q10).2) k

/-- **`gap k ≢ q13` for `k ≥ 2`** (PLL): `q13 = ◯q8` is forced
everywhere on the plain lift, so instead: `q8 ⊢ ◯q8` is the unit, so
an identification would give `gap 1 ⊢ gap k`, against the antichain. -/
theorem gap_not_q13 {k : Nat} (hk : 2 ≤ k) : ¬ Interd (gap k) q13 := by
  intro hI
  refine gap_incomparable hk (show (1 : Nat) ≠ k from by omega) ?_
  refine Deriv.cutHead (Deriv.cutHead gap_one_q8.1 ?_) hI.2
  exact dSomehowIntro (Deriv.iden (.head _))

/-! ## Part 2a: the q9-chain -/

/-- The plain-lift truth set of `sC k` is `[0, k+1]` — the same as
rung `2k+3`'s, which is why the edged lift is needed below. -/
theorem sC_plain_iff (k w : Nat) :
    ladder.cm.force (some w) (sC k) ↔ w ≤ k + 1 := by
  constructor
  · intro h
    rcases (h : ladder.cm.force (some w) (chainF k) ∨
        ladder.cm.force (some w) (rnSub (2 * k + 2))) with hc | he
    · have := (chainF_force_iff k w).mp hc
      omega
    · have := (sat_rn_even k w).mp ((ladder.transfer (rn_boxFree _) w).mp he)
      omega
  · intro hw
    rcases Nat.lt_or_ge w (k + 1) with hlt | hge
    · exact Or.inl ((chainF_force_iff k w).mpr (by omega))
    · refine Or.inr ((ladder.transfer (rn_boxFree _) w).mpr
        ((sat_rn_even k w).mpr (by omega)))

/-- `sC` ascends (PLL). -/
theorem sC_le {j k : Nat} (h : j ≤ k) : Deriv [sC j] (sC k) := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact Deriv.iden (.head _)
  · refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · exact Deriv.toHead (Deriv.orIntro1 (chain_up (Nat.le_of_lt hlt)))
    · refine Deriv.toHead (Deriv.orIntro1 ?_)
      refine Deriv.cutHead (rungD (eo_le (show j + 1 ≤ k from hlt))) ?_
      exact dSomehowIntro (Deriv.iden (.head _))

/-- `sC` is STRICT at every step (PLL): refuted at plain-lift world
`j+2`. -/
theorem sC_strict {j k : Nat} (h : j < k) : ¬ Deriv [sC k] (sC j) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (j + 2)) (fun ψ hψ => by
    have e : ψ = sC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (sC_plain_iff k (j + 2)).mpr (by omega))
  have := (sC_plain_iff j (j + 2)).mp hs
  omega

/-- The `sC k` are pairwise distinct classes (PLL). -/
theorem sC_pairwise {j k : Nat} (h : j < k) : ¬ Interd (sC j) (sC k) :=
  fun hI => sC_strict h hI.2

/-- `sC k` matches no rung (PLL): pointwise agreement on the plain
lift would force rung `2k+3`, which the edged lift then refutes at
world `k+2`. -/
theorem sC_not_rung {k : Nat} (hk : 1 ≤ k) (n : Nat) :
    ¬ Interd (rnSub n) (sC k) := by
  rintro ⟨h1, h2⟩
  have hpt : ∀ w, ladder.sat (rn n) w ↔ w ≤ k + 1 := by
    intro w
    constructor
    · intro hw
      obtain ⟨d⟩ := h1
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (ladder.transfer (rn_boxFree n) w).mpr hw
        | tail _ h => cases h)
      exact (sC_plain_iff k w).mp hf
    · intro hw
      obtain ⟨d⟩ := h2
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (sC_plain_iff k w).mpr hw
        | tail _ h => cases h)
      exact (ladder.transfer (rn_boxFree n) w).mp hf
  have hI : Interd (rnSub n) (rnSub (2 * (k + 1) + 1)) := by
    constructor
    · exact (rnSub_deriv_iff n (2 * (k + 1) + 1)).mpr
        (fun w hw => (sat_rn_odd (k + 1) w).mpr ((hpt w).mp hw))
    · exact (rnSub_deriv_iff (2 * (k + 1) + 1) n).mpr
        (fun w hw => (hpt w).mpr ((sat_rn_odd (k + 1) w).mp hw))
  have hn : n = 2 * (k + 1) + 1 := by
    by_contra hne
    exact rn_pairwise_pll hne hI
  subst hn
  -- refute `sC k ⊢ rung (2k+3)` on the edged lift at world k+2
  obtain ⟨d⟩ := h2
  have hs := soundness d (cmE (k - 1)) (some (k + 2)) (fun ψ hψ => by
    have e : ψ = sC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    refine Or.inl ((cmE_chainF (k - 1) k (k + 2)).mpr (Or.inr ⟨by omega, by omega⟩)))
  have := (sat_rn_odd (k + 1) (k + 2)).mp
    ((cmE_transfer (k - 1) (rn_boxFree _) (k + 2)).mp hs)
  omega

/-- `sC k` is not `⊤` (PLL). -/
theorem sC_not_top (k : Nat) : ¬ Interd q1 (sC k) := by
  rintro ⟨h1, -⟩
  have h0 : Deriv [] (sC k) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  obtain ⟨d⟩ := h0
  have hs := soundness d ladder.cm (some (k + 2)) (fun ψ hψ => by cases hψ)
  have := (sC_plain_iff k (k + 2)).mp hs
  omega

/-- **`sC k ∉ im h`** (PLL, `k ≥ 1`). -/
theorem sC_off_image {k : Nat} (hk : 1 ≤ k) : ¬ InImage (sC k) :=
  not_inImage_of_offRungs (sC_not_rung hk) (sC_not_top k)

/-- `sC k` is no chain class either (PLL) — the delicate case is
`chainF (k+1)`, whose plain truth set agrees; the edge separates. -/
theorem sC_not_chain {k : Nat} (hk : 1 ≤ k) (i : Nat) :
    ¬ Interd (chainF i) (sC k) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_trichotomy i (k + 1) with hlt | heq | hgt
  · -- i ≤ k: sC k forced at i+1, chainF i not
    obtain ⟨d⟩ := h2
    have hs := soundness d ladder.cm (some (i + 1)) (fun ψ hψ => by
      have e : ψ = sC k := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e
      exact (sC_plain_iff k (i + 1)).mpr (by omega))
    have := (chainF_force_iff i (i + 1)).mp hs
    omega
  · -- i = k+1: same plain truth sets; separate on cmE k at world k+3
    subst heq
    obtain ⟨d⟩ := h1
    have hs := soundness d (cmE k) (some (k + 3)) (fun ψ hψ => by
      have e : ψ = chainF (k + 1) := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e
      exact (cmE_chainF k (k + 1) (k + 3)).mpr (Or.inr ⟨rfl, by omega⟩))
    rcases (hs : (cmE k).force (some (k + 3)) (chainF k) ∨
        (cmE k).force (some (k + 3)) (rnSub (2 * k + 2))) with hc | he
    · rcases (cmE_chainF k k (k + 3)).mp hc with h' | ⟨-, h'⟩ <;> omega
    · have := (sat_rn_even k (k + 3)).mp
        ((cmE_transfer k (rn_boxFree _) (k + 3)).mp he)
      omega
  · -- i ≥ k+2: chainF i forced at k+2, sC k not
    obtain ⟨d⟩ := h1
    have hs := soundness d ladder.cm (some (k + 2)) (fun ψ hψ => by
      have e : ψ = chainF i := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e
      exact (chainF_force_iff i (k + 2)).mpr (by omega))
    have := (sC_plain_iff k (k + 2)).mp hs
    omega

/-! ## Part 2b: the q14-antichain -/

/-- The plain-lift truth set of `rC k` is `[0,k+1] ∪ {k+3}` — the
same as rung `2k+6`'s. -/
theorem rC_plain_iff (k w : Nat) :
    ladder.cm.force (some w) (rC k) ↔ (w ≤ k + 1 ∨ w = k + 3) := by
  constructor
  · intro h
    have h' : ∀ v : Option Nat, ladder.cm.Ri (some w) v →
        ladder.cm.force v (rnSub (2 * k + 4)) →
        ladder.cm.force v (chainF k) := h
    by_contra hw
    have hle : ladder.le w (k + 2) := by
      have h2 : k + 2 = w ∨ k + 2 + 2 ≤ w := by omega
      exact h2
    have hE : ladder.cm.force (some (k + 2)) (rnSub (2 * k + 4)) := by
      refine (ladder.transfer (rn_boxFree _) (k + 2)).mpr ?_
      show ladder.sat (rn (2 * (k + 1) + 2)) (k + 2)
      exact (sat_rn_even (k + 1) (k + 2)).mpr (by omega)
    have := (chainF_force_iff k (k + 2)).mp (h' (some (k + 2)) hle hE)
    omega
  · intro hw
    show ∀ v : Option Nat, ladder.cm.Ri (some w) v →
      ladder.cm.force v (rnSub (2 * k + 4)) → ladder.cm.force v (chainF k)
    intro v hv hE
    cases v with
    | none => exact ladder.cm.force_of_fallible rfl
    | some y =>
        have hy : y ≤ k ∨ y = k + 2 := by
          have := (sat_rn_even (k + 1) y).mp
            ((ladder.transfer (rn_boxFree _) y).mp
              (by
                have e : (2 : Nat) * (k + 1) + 2 = 2 * k + 4 := by omega
                rw [e]
                exact hE))
          omega
        have hcone : y = w ∨ y + 2 ≤ w := hv
        have hcone' : (y : Nat) = w ∨ (y : Nat) + 2 ≤ w := hcone
        refine (chainF_force_iff k y).mpr ?_
        omega

/-- In its own edged lift `cmE (k−1)`, `rC k` is forced at EVERY
world — the edge supplies exactly the missing point `k+2`. -/
theorem rC_forced_own {k : Nat} (hk : 1 ≤ k) (x : Nat) :
    (cmE (k - 1)).force (some x) (rC k) := by
  show ∀ v : Option Nat, (cmE (k - 1)).Ri (some x) v →
    (cmE (k - 1)).force v (rnSub (2 * k + 4)) →
    (cmE (k - 1)).force v (chainF k)
  intro v hv hE
  cases v with
  | none => exact (cmE (k - 1)).force_of_fallible rfl
  | some y =>
      have hy : y ≤ k ∨ y = k + 2 := by
        have := (sat_rn_even (k + 1) y).mp
          ((cmE_transfer (k - 1) (rn_boxFree _) y).mp
            (by
              have e : (2 : Nat) * (k + 1) + 2 = 2 * k + 4 := by omega
              rw [e]
              exact hE))
        omega
      rcases hy with hy | rfl
      · exact (cmE_chainF (k - 1) k y).mpr (Or.inl hy)
      · exact (cmE_chainF (k - 1) k (k + 2)).mpr (Or.inr ⟨by omega, by omega⟩)

/-- In any OTHER edged lift (`k+2` not the edge world), `rC k` fails
at world `k+2`. -/
theorem rC_fails (m k : Nat) (hne : k + 2 ≠ m + 3) :
    ¬ (cmE m).force (some (k + 2)) (rC k) := by
  intro h
  have h' : ∀ v : Option Nat, (cmE m).Ri (some (k + 2)) v →
      (cmE m).force v (rnSub (2 * k + 4)) →
      (cmE m).force v (chainF k) := h
  have hE : (cmE m).force (some (k + 2)) (rnSub (2 * k + 4)) := by
    refine (cmE_transfer m (rn_boxFree _) (k + 2)).mpr ?_
    show ladder.sat (rn (2 * (k + 1) + 2)) (k + 2)
    exact (sat_rn_even (k + 1) (k + 2)).mpr (by omega)
  have hc := (cmE_chainF m k (k + 2)).mp (h' (some (k + 2)) (Or.inl rfl) hE)
  rcases hc with h' | ⟨h', -⟩
  · omega
  · exact hne h'

/-- **The q14-family is an antichain** (PLL): for ALL `j ≠ k ≥ 1`,
`rC j ⊬ rC k` — no `k ≥ 2` restriction, unlike the gaps. -/
theorem rC_incomparable {j k : Nat} (hj : 1 ≤ j) (hk : 1 ≤ k)
    (hne : j ≠ k) : ¬ Deriv [rC j] (rC k) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (j - 1)) (some (k + 2)) (fun ψ hψ => by
    have e : ψ = rC j := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact rC_forced_own hj (k + 2))
  exact rC_fails (j - 1) k (by omega) hs

theorem rC_pairwise {j k : Nat} (hj : 1 ≤ j) (hk : 1 ≤ k) (hne : j ≠ k) :
    ¬ Interd (rC j) (rC k) :=
  fun hI => rC_incomparable hj hk hne hI.1

/-- `rC k` matches no rung (PLL): plain agreement forces rung `2k+6`,
then `cmE (k−1)` refutes at world `k+4`. -/
theorem rC_not_rung {k : Nat} (hk : 1 ≤ k) (n : Nat) :
    ¬ Interd (rnSub n) (rC k) := by
  rintro ⟨h1, h2⟩
  have hpt : ∀ w : Nat, ladder.sat (rn n) w ↔ (w ≤ k + 1 ∨ w = k + 3) := by
    intro w
    constructor
    · intro hw
      obtain ⟨d⟩ := h1
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (ladder.transfer (rn_boxFree n) w).mpr hw
        | tail _ h => cases h)
      exact (rC_plain_iff k w).mp hf
    · intro hw
      obtain ⟨d⟩ := h2
      have hf := soundness d ladder.cm (some w) (fun ψ hψ => by
        cases hψ with
        | head => exact (rC_plain_iff k w).mpr hw
        | tail _ h => cases h)
      exact (ladder.transfer (rn_boxFree n) w).mp hf
  have hI : Interd (rnSub n) (rnSub (2 * (k + 2) + 2)) := by
    constructor
    · exact (rnSub_deriv_iff n (2 * (k + 2) + 2)).mpr
        (fun w hw => (sat_rn_even (k + 2) w).mpr (by
          have := (hpt w).mp hw
          omega))
    · exact (rnSub_deriv_iff (2 * (k + 2) + 2) n).mpr
        (fun w hw => (hpt w).mpr (by
          have := (sat_rn_even (k + 2) w).mp hw
          omega))
  have hn : n = 2 * (k + 2) + 2 := by
    by_contra hne
    exact rn_pairwise_pll hne hI
  subst hn
  obtain ⟨d⟩ := h2
  have hs := soundness d (cmE (k - 1)) (some (k + 4)) (fun ψ hψ => by
    have e : ψ = rC k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact rC_forced_own hk (k + 4))
  have := (sat_rn_even (k + 2) (k + 4)).mp
    ((cmE_transfer (k - 1) (rn_boxFree _) (k + 4)).mp hs)
  omega

/-- `rC k` is not `⊤` (PLL). -/
theorem rC_not_top (k : Nat) : ¬ Interd q1 (rC k) := by
  rintro ⟨h1, -⟩
  have h0 : Deriv [] (rC k) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  obtain ⟨d⟩ := h0
  have hs := soundness d ladder.cm (some (k + 2)) (fun ψ hψ => by cases hψ)
  have := (rC_plain_iff k (k + 2)).mp hs
  omega

/-- **`rC k ∉ im h`** (PLL, `k ≥ 1`). -/
theorem rC_off_image {k : Nat} (hk : 1 ≤ k) : ¬ InImage (rC k) :=
  not_inImage_of_offRungs (rC_not_rung hk) (rC_not_top k)

/-! ## Part 2c: the q13-antichain (boxed gaps) -/

/-- Where `gap k` fails in `cmE m` (for `k` in the window): at the
edge world and everything above it. -/
theorem gap_fails_above (m k x : Nat) (hk1 : m + 1 ≤ k) (hk2 : k ≤ m + 2)
    (hx : x = m + 3 ∨ m + 5 ≤ x) :
    ¬ (cmE m).force (some x) (gap k) := by
  intro h
  have h' : ∀ v : Option Nat, (cmE m).Ri (some x) v →
      (cmE m).force v (chainF k) → (cmE m).force v (rnSub (2 * k + 1)) := h
  have hle : ladder.le x (m + 3) := by
    have h2 : m + 3 = x ∨ m + 3 + 2 ≤ x := by omega
    exact h2
  have hf := h' (some (m + 3)) hle
    ((cmE_chainF m k (m + 3)).mpr (Or.inr ⟨rfl, hk1⟩))
  have := (sat_rn_odd k (m + 3)).mp
    ((cmE_transfer m (rn_boxFree _) (m + 3)).mp hf)
  omega

/-- **The q13-family is an antichain** (PLL): the boxed gaps
`(gap k).somehow` are pairwise ⊬-incomparable for `j ≠ k`, `k ≥ 2` —
separated at world `m+5`, just above the edge. -/
theorem bg_incomparable {j k : Nat} (hk : 2 ≤ k) (hne : j ≠ k) :
    ¬ Deriv [(gap j).somehow] ((gap k).somehow) := by
  rintro ⟨d⟩
  have key : ∀ m : Nat, m + 1 ≤ k → k ≤ m + 2 → j ≠ m + 1 → j ≠ m + 2 →
      False := by
    intro m h1 h2 h3 h4
    have hs := soundness d (cmE m) (some (m + 5)) (fun ψ hψ => by
      have e : ψ = (gap j).somehow := by
        cases hψ with
        | head => rfl
        | tail _ h => cases h
      subst e
      refine (cmE_box_force m (gap j) (m + 5)).mpr (fun y hy => ?_)
      exact Or.inr (Or.inr (gap_forced m j h3 h4 y)))
    rcases (cmE_box_force m (gap k) (m + 5)).mp hs (m + 5) (Or.inl rfl)
      with h0 | h3' | hf
    · omega
    · omega
    · exact gap_fails_above m k (m + 5) h1 h2 (Or.inr (by omega)) hf
  by_cases hcase : j = k + 1
  · exact key (k - 2) (by omega) (by omega) (by omega) (by omega)
  · exact key (k - 1) (by omega) (by omega) (by omega) (by omega)

theorem bg_pairwise {j k : Nat} (hj : 2 ≤ j) (hk : 2 ≤ k) (hne : j ≠ k) :
    ¬ Interd ((gap j).somehow) ((gap k).somehow) :=
  fun hI => bg_incomparable hk hne hI.1

/-- The boxed gaps are forced everywhere on the plain lift. -/
theorem plain_forces_bg (k : Nat) (v : Option Nat) :
    ladder.cm.force v ((gap k).somehow) := by
  cases v with
  | none => exact ladder.cm.force_of_fallible rfl
  | some x =>
      refine (Skel.box_force ladder (gap k) x).mpr (fun y hy => ?_)
      exact Or.inr (plain_forces_gap k (some y))

/-- `(gap k).somehow` matches no rung (PLL). -/
theorem bg_not_rung (k n : Nat) : ¬ Interd (rnSub n) ((gap k).somehow) := by
  rintro ⟨-, h2⟩
  obtain ⟨d⟩ := h2
  have hs := soundness d ladder.cm (some (n + 1)) (fun ψ hψ => by
    have e : ψ = (gap k).somehow := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact plain_forces_bg k (some (n + 1)))
  have hb := rungMem_bound
    ((sat_rung n (n + 1)).mp ((ladder.transfer (rn_boxFree n) (n + 1)).mp hs))
  omega

/-- `(gap k).somehow` is no chain class (PLL). -/
theorem bg_not_chain (k i : Nat) : ¬ Interd (chainF i) ((gap k).somehow) := by
  rintro ⟨-, h2⟩
  obtain ⟨d⟩ := h2
  have hs := soundness d ladder.cm (some (i + 1)) (fun ψ hψ => by
    have e : ψ = (gap k).somehow := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact plain_forces_bg k (some (i + 1)))
  have := (chainF_force_iff i (i + 1)).mp hs
  omega

/-- `(gap k).somehow` is not `⊤` for `k ≥ 2` (PLL): `⊢ ◯(gap k)`
reflects to `⊢ gap k`, against `box_not_fix`. -/
theorem bg_not_top {k : Nat} (hk : 2 ≤ k) :
    ¬ Interd q1 ((gap k).somehow) := by
  rintro ⟨h1, -⟩
  have hthm : Deriv [] ((gap k).somehow) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  have hg : Deriv [] (gap k) := box_reflects_thm hthm
  have hd : Deriv [chainF k] (rnSub (2 * k + 1)) :=
    Deriv.impElim (wkHead _ hg) (Deriv.iden (.head _))
  have hb := box_not_fix (k - 2)
  rw [show k - 2 + 2 = k from by omega] at hb
  exact hb hd

/-- **`(gap k).somehow ∉ im h`** (PLL, `k ≥ 2`). -/
theorem bg_off_image {k : Nat} (hk : 2 ≤ k) : ¬ InImage ((gap k).somehow) :=
  not_inImage_of_offRungs (fun n => bg_not_rung k n) (bg_not_top hk)

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.gap_not_q9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_not_q9

/-- info: 'PLLND.RNEmbed.gap_not_q13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_not_q13

/-- info: 'PLLND.RNEmbed.sC_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sC_off_image

/-- info: 'PLLND.RNEmbed.rC_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rC_incomparable

/-- info: 'PLLND.RNEmbed.bg_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bg_incomparable

end RNEmbed
end PLLND
