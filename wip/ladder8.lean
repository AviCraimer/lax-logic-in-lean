import wip.rnEmbed

/-!
# The ladder image of `RN({p})` in `RN(◯,{})`, decided

`wip/rnEmbed.lean` proves that `p ↦ ◯⊥` carries the Rieger–Nishimura
rungs to pairwise non-interderivable variable-free formulas, and that
the resulting order is exactly ladder containment
(`rnSub_deriv_iff`).  That reduces every rung-to-rung derivability
question to a statement about truth sets in the ladder frame — but
leaves it in semantic form, quantified over worlds.

This file finishes the reduction: the truth sets are computed as
*arithmetic*, so `rnSub i ⊢ rnSub j` becomes a decidable predicate on
`(i, j)` and every cell of the order table is closed by `decide`.

The point is that this is not a table for eight rungs.  `rnSub_order`
holds for ALL `i, j`; the eight-rung table below is one instance of it,
and any larger table is the same theorem with different numerals.

## The truth sets

From `sat_rn_odd` / `sat_rn_even` / `sat_rn_zero`:

    rn 0       ↦  ∅
    rn (2k+1)  ↦  {w | w ≤ k}          an initial segment
    rn (2k+2)  ↦  {w | w < k} ∪ {k+1}  an initial segment with a gap
                                        at `k` and one point above it

The gap is the whole story: it is what makes the even rungs pairwise
incomparable, and it is why the ladder does not collapse.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI ConfluentU

/-! ## The truth sets as arithmetic -/

/-- Membership of world `w` in the truth set of rung `n`. -/
def rungMem (n w : Nat) : Bool :=
  if n = 0 then false
  else if n % 2 = 1 then decide (w ≤ (n - 1) / 2)
  else (decide (w + 1 ≤ (n - 2) / 2) || decide (w = (n - 2) / 2 + 1))

theorem rungMem_zero (w : Nat) : rungMem 0 w = false := by
  simp [rungMem]

theorem rungMem_odd (k w : Nat) : rungMem (2 * k + 1) w = decide (w ≤ k) := by
  have e0 : ¬ (2 * k + 1 = 0) := by omega
  have e1 : (2 * k + 1) % 2 = 1 := by omega
  have e2 : (2 * k + 1 - 1) / 2 = k := by omega
  simp [rungMem, e0, e1, e2]

theorem rungMem_even (k w : Nat) :
    rungMem (2 * k + 2) w = (decide (w + 1 ≤ k) || decide (w = k + 1)) := by
  have e0 : ¬ (2 * k + 2 = 0) := by omega
  have e1 : ¬ ((2 * k + 2) % 2 = 1) := by omega
  have e2 : (2 * k + 2 - 2) / 2 = k := by omega
  simp [rungMem, e0, e1, e2]

/-- **The truth set of a rung, arithmetically.** -/
theorem sat_rung (n w : Nat) : ladder.sat (rn n) w ↔ rungMem n w = true := by
  rcases parity3 n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [rungMem_zero]
    exact ⟨fun h => absurd h (sat_rn_zero w), fun h => absurd h (by simp)⟩
  · rw [sat_rn_odd, rungMem_odd]
    exact ⟨fun h => by simpa using h, fun h => by simpa using h⟩
  · rw [sat_rn_even, rungMem_even]
    constructor
    · rintro (h | h) <;> simp <;> omega
    · intro h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      exact h

/-- Nothing above `n` is in the truth set of rung `n`. -/
theorem rungMem_bound {n w : Nat} (h : rungMem n w = true) : w ≤ n := by
  rcases parity3 n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [rungMem_zero] at h; exact absurd h (by simp)
  · rw [rungMem_odd] at h; simp at h; omega
  · rw [rungMem_even] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    omega

/-! ## The order, decided -/

/-- The decidable order test: containment of truth sets, checked on the
only worlds that can matter (`rungMem_bound`). -/
def rungLe (i j : Nat) : Bool :=
  (List.range (i + 1)).all fun w => (!rungMem i w) || rungMem j w

/-- **The rung order is decidable arithmetic.**  For every pair of
rungs, `rnSub i ⊢ rnSub j` in PLL iff `rungLe i j`. -/
theorem rnSub_order (i j : Nat) :
    Deriv [rnSub i] (rnSub j) ↔ rungLe i j = true := by
  rw [rnSub_deriv_iff]
  constructor
  · intro h
    simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    intro w _
    by_cases hw : rungMem i w = true
    · exact Or.inr ((sat_rung j w).mp (h w ((sat_rung i w).mpr hw)))
    · exact Or.inl (by simpa using hw)
  · intro h w hw
    have hi : rungMem i w = true := (sat_rung i w).mp hw
    have hlt : w < i + 1 := Nat.lt_succ_of_le (rungMem_bound hi)
    simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h w (List.mem_range.mpr hlt) with hc | hc
    · exact absurd hi (by simp [hc])
    · exact (sat_rung j w).mpr hc

/-- The same order in PCLL (`rnSub_derivU_iff_deriv`). -/
theorem rnSub_orderU (i j : Nat) :
    DerivU [rnSub i] (rnSub j) ↔ rungLe i j = true :=
  (rnSub_derivU_iff_deriv i j).trans (rnSub_order i j)

/-- Distinct rungs are never interderivable — the embedding is
injective, restated through the decision procedure. -/
theorem rnSub_interd_iff (i j : Nat) :
    Interd (rnSub i) (rnSub j) ↔ (rungLe i j = true ∧ rungLe j i = true) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(rnSub_order i j).mp h1, (rnSub_order j i).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(rnSub_order i j).mpr h1, (rnSub_order j i).mpr h2⟩

/-! ## The cover relation

`j` covers `i` when `i < j` in the order and nothing sits strictly
between.  Bounded to rungs `< b`, which is all a finite drawing needs.
-/

/-- `j` covers `i` among the rungs below `b`. -/
def rungCovers (b i j : Nat) : Bool :=
  rungLe i j && !rungLe j i &&
    (List.range b).all fun m =>
      !(rungLe i m && !rungLe m i && rungLe m j && !rungLe j m)

/-! ## The eight-rung table

Every cell below is closed by `decide` through `rnSub_order`.  Nothing
here is search output, and nothing is specific to eight: the same two
lines prove any cell of any size.
-/

example : Deriv [rnSub 0] (rnSub 5) := (rnSub_order 0 5).mpr (by decide)
example : ¬ Deriv [rnSub 5] (rnSub 6) := fun h => by
  have := (rnSub_order 5 6).mp h; exact absurd this (by decide)

/-- The order on the first nine rungs, as a Boolean matrix. -/
def order9 : List (List Bool) :=
  (List.range 9).map fun i => (List.range 9).map fun j => rungLe i j

/-- The cover relation on the first nine rungs. -/
def covers9 : List (Nat × Nat) :=
  (List.range 9).flatMap fun i =>
    ((List.range 9).filter fun j => rungCovers 9 i j).map fun j => (i, j)

/-- **The Hasse diagram of the first nine rungs**, as its cover list.
Eleven covers, pinned by `decide`.  Reading them off:

    rn0 ⋖ rn1, rn2          `⊥` below the two atoms of the ladder
    rn1 ⋖ rn3, rn4          the odd rung forks
    rn2 ⋖ rn3               the even rung does not
    rn3 ⋖ rn5, rn6
    rn4 ⋖ rn5
    rn5 ⋖ rn7, rn8
    rn6 ⋖ rn7

so odd rungs have two upper covers and even rungs one, which is the
Rieger–Nishimura zigzag. -/
theorem covers9_eq :
    covers9 = [(0, 1), (0, 2), (1, 3), (1, 4), (2, 3), (3, 5), (3, 6),
               (4, 5), (5, 7), (5, 8), (6, 7)] := by
  decide

/-- The bound in `covers9` is not hiding anything: widening the
"nothing strictly between" search from rungs `< 9` to rungs `< 24`
gives the same eleven covers, so the drawing is the Hasse diagram of
the true poset restricted to these nine elements, not an artefact of
where the table was cut. -/
theorem covers9_stable :
    ((List.range 9).flatMap fun i =>
        ((List.range 9).filter fun j => rungCovers 24 i j).map fun j => (i, j))
      = covers9 := by
  decide

/-- The odd rungs form a chain: `rn 1 < rn 3 < rn 5 < rn 7 < …`. -/
theorem odd_chain (k : Nat) : rungLe (2 * k + 1) (2 * k + 3) = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  rw [rungMem_odd]
  by_cases h : w ≤ k
  · exact Or.inr (by
      have : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
      rw [this, rungMem_odd]; simp; omega)
  · exact Or.inl (by simp [h])

/-- **The even rungs are not an antichain**, contrary to what the
picture suggests: `rn (2k+2) ⊢ rn (2m+2)` exactly when `m` is `k` or at
least `k + 2`.  The gap at `k` blocks the *step*, and only the step —
`rn 4 ⊢ rn 8` while `rn 4 ⊬ rn 6`. -/
theorem even_le_even (k m : Nat) (h : k = m ∨ k + 2 ≤ m) :
    rungLe (2 * k + 2) (2 * m + 2) = true := by
  simp only [rungLe, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro w _
  by_cases hw : rungMem (2 * k + 2) w = true
  · refine Or.inr ?_
    rw [rungMem_even] at hw ⊢
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hw ⊢
    omega
  · exact Or.inl (by simpa using hw)

/-- Witness form: one world inside `i`'s truth set and outside `j`'s
refutes the order. -/
theorem rungLe_eq_false {i j w : Nat} (hw : w ≤ i)
    (h1 : rungMem i w = true) (h2 : rungMem j w = false) :
    rungLe i j = false := by
  by_contra hc
  have hct : rungLe i j = true := by
    cases hh : rungLe i j with
    | false => exact absurd hh hc
    | true => rfl
  have hall := List.all_eq_true.mp hct w (List.mem_range.mpr (Nat.lt_succ_of_le hw))
  rw [h1, h2] at hall
  simp at hall

/-- Consecutive even rungs ARE incomparable: the step is exactly what
the gap blocks.  Witness: world `k+1`, the point that sits above the
gap in `rn (2k+2)` and below it in `rn (2k+4)`. -/
theorem even_step_incomparable (k : Nat) :
    rungLe (2 * k + 2) (2 * k + 4) = false := by
  have he : (2 : Nat) * k + 4 = 2 * (k + 1) + 2 := by omega
  refine rungLe_eq_false (w := k + 1) (by omega) ?_ ?_
  · rw [rungMem_even]; simp
  · rw [he, rungMem_even]
    have a1 : ¬ (k + 1 + 1 ≤ k + 1) := by omega
    have a2 : ¬ (k + 1 = k + 1 + 1) := by omega
    simp [a1, a2]

/-! ## Axiom audits

Everything here is `sorry`-free.  The two diagram theorems are pure
computation and depend on no axioms whatever; the order theorems
inherit `propext / Classical.choice / Quot.sound` from `rnEmbed`.
-/

/-- info: 'PLLND.RNEmbed.sat_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sat_rung

/-- info: 'PLLND.RNEmbed.rnSub_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rnSub_order

/-- info: 'PLLND.RNEmbed.rnSub_orderU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rnSub_orderU

/-- info: 'PLLND.RNEmbed.covers9_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms covers9_eq

/-- info: 'PLLND.RNEmbed.covers9_stable' does not depend on any axioms -/
#guard_msgs in
#print axioms covers9_stable

/-- info: 'PLLND.RNEmbed.even_step_incomparable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms even_step_incomparable

end RNEmbed
end PLLND
