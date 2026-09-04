import wip.rnClassify

/-!
# RN(◯,{}) has UNBOUNDED WIDTH

The question "does RN(◯,{}) have bounded width?" is answered: **no**.
The witness family generalises the dictionary class
`q8 = ◯¬◯⊥ ⊃ (◯⊥ ∨ ¬◯⊥)` level by level:

    gap k := ◯(rnSub (2k+1)) ⊃ rnSub (2k+1)      "◯ collapses at level k"

(`gap 1 ≡ q8`, proved below).  The `gap k` for `k ≥ 2` are **pairwise
⊬-incomparable** — an antichain indexed by ℕ — so no finite bound on
antichains exists.

The proof needs ONE new semantic computation and no new models.  On the
edged lift `cmE m` (the abyss-lifted ladder with the single extra
`Rₘ`-edge `(m+3) ⇝ 0`, from `wip/chainOff.lean`):

    T(chainF k) = [0,k] ∪ { m+3  if m+1 ≤ k }        (`cmE_chainF`)

while the rungs keep their plain truth sets (`cmE_transfer`).  Hence
`gap k` fails somewhere in `cmE m` **exactly when** `k ∈ {m+1, m+2}`
(the levels whose collapse the edge fakes), and holds at every world
otherwise.  For `j ≠ k` (`k ≥ 2`) choose the edge level

    m := k−2  if j = k+1,   m := k−1  otherwise

so `gap k` fails at world `m+3` while `gap j` is forced everywhere;
soundness refutes `gap j ⊢ gap k`.

Squaring with the classification: each `gap k` (`k ≥ 2`) is a genuinely
NEW class — off im h (`gap_off_image`, via `image_classification`), and
distinct from every chain class too (`gap_not_chain`) — because on the
PLAIN abyss lift `chainF k` and `rnSub (2k+1)` wear the same truth set,
so `gap k` is forced at every world there, and nothing of bounded truth
set can match it.  So the dictionary's snapshot sits inside an algebra
with an infinite chain (the boxed odd rungs) AND an infinite antichain
(their collapse statements), both families starting at dictionary
classes (`q5`/`q12`/`◯q11`, and `q8`).
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- `gap k`: the box collapses at level `k`.  `gap 1 ≡ q8`. -/
def gap (k : Nat) : PLLFormula := (chainF k).ifThen (rnSub (2 * k + 1))

/-- How `◯` evaluates on the edged lift: a cone point is the abyss
escape `0`, the edge world `m+3` (which escapes through the edge), or
must force the body itself. -/
theorem cmE_box_force (m : Nat) (N : PLLFormula) (x : Nat) :
    (cmE m).force (some x) N.somehow ↔
      ∀ y : Nat, ladder.le x y → (y = 0 ∨ y = m + 3 ∨ (cmE m).force (some y) N) := by
  constructor
  · intro h y hy
    obtain ⟨u, hu, hf⟩ := h (some y) hy
    cases u with
    | none =>
        rcases (hu : y = 0 ∨ y = m + 3) with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
    | some z =>
        rcases (hu : y = z ∨ (y = m + 3 ∧ z = 0)) with rfl | ⟨rfl, -⟩
        · exact Or.inr (Or.inr hf)
        · exact Or.inr (Or.inl rfl)
  · intro h v hv
    cases v with
    | none => exact ⟨none, trivial, (cmE m).force_of_fallible rfl⟩
    | some y =>
        rcases h y hv with rfl | rfl | hf
        · exact ⟨none, Or.inl rfl, (cmE m).force_of_fallible rfl⟩
        · exact ⟨none, Or.inr rfl, (cmE m).force_of_fallible rfl⟩
        · exact ⟨some y, Or.inl rfl, hf⟩

/-- **The truth set of the chain on the edged lift**:
`T(chainF k) = [0,k]`, plus the edge world `m+3` exactly when the edge
reaches low enough (`m+1 ≤ k`). -/
theorem cmE_chainF (m k x : Nat) :
    (cmE m).force (some x) (chainF k) ↔ (x ≤ k ∨ (x = m + 3 ∧ m + 1 ≤ k)) := by
  show (cmE m).force (some x) ((rnSub (2 * k + 1)).somehow) ↔ _
  rw [cmE_box_force]
  constructor
  · intro h
    rcases h x (Or.inl rfl) with rfl | rfl | hf
    · exact Or.inl (Nat.zero_le k)
    · by_cases hmk : m + 3 ≤ k
      · exact Or.inl hmk
      · refine Or.inr ⟨rfl, ?_⟩
        rcases h (m + 1) (Or.inr (by omega)) with h0 | h3 | hf
        · omega
        · omega
        · have := (sat_rn_odd k (m + 1)).mp
            ((cmE_transfer m (rn_boxFree _) _).mp hf)
          omega
    · exact Or.inl ((sat_rn_odd k x).mp ((cmE_transfer m (rn_boxFree _) _).mp hf))
  · intro h y hy
    rcases h with hx | ⟨rfl, hmk⟩
    · refine Or.inr (Or.inr ((cmE_transfer m (rn_boxFree _) _).mpr
        ((sat_rn_odd k y).mpr ?_)))
      rcases (hy : y = x ∨ y + 2 ≤ x) with rfl | h2 <;> omega
    · rcases (hy : y = m + 3 ∨ y + 2 ≤ m + 3) with rfl | h2
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((cmE_transfer m (rn_boxFree _) _).mpr
          ((sat_rn_odd k y).mpr (by omega))))

/-- If `j` avoids the edge's window `{m+1, m+2}`, `gap j` is forced at
EVERY world of `cmE m`. -/
theorem gap_forced (m j : Nat) (h1 : j ≠ m + 1) (h2 : j ≠ m + 2) (x : Nat) :
    (cmE m).force (some x) (gap j) := by
  show ∀ v, (cmE m).Ri (some x) v →
    (cmE m).force v (chainF j) → (cmE m).force v (rnSub (2 * j + 1))
  intro v hv hcf
  cases v with
  | none => exact (cmE m).force_of_fallible rfl
  | some y =>
      refine (cmE_transfer m (rn_boxFree _) _).mpr ((sat_rn_odd j y).mpr ?_)
      rcases (cmE_chainF m j y).mp hcf with hy | ⟨rfl, hmj⟩
      · exact hy
      · omega

/-- If `k` sits IN the window, `gap k` fails at the edge world `m+3`. -/
theorem gap_fails (m k : Nat) (hk1 : m + 1 ≤ k) (hk2 : k ≤ m + 2) :
    ¬ (cmE m).force (some (m + 3)) (gap k) := by
  intro h
  have h' : ∀ v, (cmE m).Ri (some (m + 3)) v →
      (cmE m).force v (chainF k) → (cmE m).force v (rnSub (2 * k + 1)) := h
  have hf := h' (some (m + 3)) (Or.inl rfl)
    ((cmE_chainF m k (m + 3)).mpr (Or.inr ⟨rfl, hk1⟩))
  have := (sat_rn_odd k (m + 3)).mp ((cmE_transfer m (rn_boxFree _) _).mp hf)
  omega

/-- **Pairwise incomparability**: for `k ≥ 2` and any `j ≠ k`,
`gap j ⊬ gap k` — the edge level is chosen per pair. -/
theorem gap_incomparable {j k : Nat} (hk : 2 ≤ k) (hne : j ≠ k) :
    ¬ Deriv [gap j] (gap k) := by
  rintro ⟨d⟩
  have key : ∀ m : Nat, m + 1 ≤ k → k ≤ m + 2 → j ≠ m + 1 → j ≠ m + 2 → False :=
    fun m h1 h2 h3 h4 =>
      gap_fails m k h1 h2 (soundness d (cmE m) (some (m + 3)) (fun ψ hψ => by
        have e : ψ = gap j := by
          cases hψ with
          | head => rfl
          | tail _ h => cases h
        subst e
        exact gap_forced m j h3 h4 (m + 3)))
  by_cases hcase : j = k + 1
  · exact key (k - 2) (by omega) (by omega) (by omega) (by omega)
  · exact key (k - 1) (by omega) (by omega) (by omega) (by omega)

/-- **RN(◯,{}) has infinite width**: an ℕ-indexed antichain. -/
theorem width_infinite (i j : Nat) (h : i ≠ j) :
    ¬ Interd (gap (i + 2)) (gap (j + 2)) := fun hI =>
  gap_incomparable (by omega) (by omega) hI.2

/-! ## The antichain is genuinely new: off the image, off the chain -/

/-- On the PLAIN abyss lift, `chainF k` and `rnSub (2k+1)` wear the
same truth set, so `gap k` is forced at every world. -/
theorem plain_forces_gap (k : Nat) (v : Option Nat) :
    ladder.cm.force v (gap k) := by
  cases v with
  | none => exact ladder.cm.force_of_fallible rfl
  | some x =>
      show ∀ u, ladder.cm.Ri (some x) u →
        ladder.cm.force u (chainF k) → ladder.cm.force u (rnSub (2 * k + 1))
      intro u hu hcf
      cases u with
      | none => exact ladder.cm.force_of_fallible rfl
      | some y =>
          exact (ladder.transfer (rn_boxFree _) y).mpr
            ((sat_rn_odd k y).mpr ((chainF_force_iff k y).mp hcf))

/-- `gap k` is interderivable with NO rung: it is forced everywhere on
the plain lift, and rungs have bounded truth sets. -/
theorem gap_not_rung (k n : Nat) : ¬ Interd (rnSub n) (gap k) := by
  rintro ⟨-, h2⟩
  obtain ⟨d⟩ := h2
  have hs := soundness d ladder.cm (some (n + 1)) (fun ψ hψ => by
    have e : ψ = gap k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact plain_forces_gap k (some (n + 1)))
  have hb := rungMem_bound
    ((sat_rung n (n + 1)).mp ((ladder.transfer (rn_boxFree n) (n + 1)).mp hs))
  omega

/-- `gap k` is no chain class either — same argument, since
`T(chainF i) = [0, i]` is bounded on the plain lift. -/
theorem gap_not_chain (k i : Nat) : ¬ Interd (chainF i) (gap k) := by
  rintro ⟨-, h2⟩
  obtain ⟨d⟩ := h2
  have hs := soundness d ladder.cm (some (i + 1)) (fun ψ hψ => by
    have e : ψ = gap k := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact plain_forces_gap k (some (i + 1)))
  have := (chainF_force_iff i (i + 1)).mp hs
  omega

/-- `gap k` is not `⊤` for `k ≥ 2`: a proof of it would collapse the
unit at level `k`, against `box_not_fix`. -/
theorem gap_not_top {k : Nat} (hk : 2 ≤ k) : ¬ Interd q1 (gap k) := by
  rintro ⟨h1, -⟩
  have hthm : Deriv [] (gap k) :=
    Deriv.cutHead (Deriv.impIntro (Deriv.iden (.head _))) h1
  have hd : Deriv [chainF k] (rnSub (2 * k + 1)) :=
    Deriv.impElim (wkHead _ hthm) (Deriv.iden (.head _))
  have hb := box_not_fix (k - 2)
  rw [show k - 2 + 2 = k from by omega] at hb
  exact hb hd

/-- **Every `gap k` (`k ≥ 2`) is off the image of `h`** — by the
mechanised classification. -/
theorem gap_off_image {k : Nat} (hk : 2 ≤ k) : ¬ InImage (gap k) :=
  not_inImage_of_offRungs (fun n => gap_not_rung k n) (gap_not_top hk)

/-! ## The family starts at the dictionary: `gap 1 ≡ q8` -/

/-- `chainF 1 ≡ q5`: `◯(rung 3) ≡ ◯(rung 2)` — the box absorbs the
`◯⊥`-disjunct. -/
theorem chainF_one_q5 : Interd (chainF 1) q5 := by
  constructor
  · refine dSomehowElim (Deriv.iden (.head _)) (Deriv.toHead ?_)
    have e : rnSub (2 * 1 + 1) = (rnSub 1).or (rnSub 2) := rnSub_odd_eq 0
    rw [e]
    refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · have e1 : rnSub 1 = q2 := by decide
      rw [e1]
      exact Deriv.toHead (dSomehowElim (Deriv.iden (.head _))
        (Deriv.falsoElim _ (Deriv.iden (.head _))))
    · have e2 : rnSub 2 = q3 := by decide
      rw [e2]
      exact Deriv.toHead (dSomehowIntro (Deriv.iden (.head _)))
  · show Deriv [q3.somehow] (chainF 1)
    have e2 : q3 = rnSub 2 := by decide
    rw [e2]
    exact box_mono (rungD (show rungLe 2 3 = true from by decide))

/-- **`gap 1 ≡ q8`**: the antichain generalises the dictionary class
`q8` level by level. -/
theorem gap_one_q8 : Interd (gap 1) q8 := by
  show Interd ((chainF 1).ifThen (rnSub (2 * 1 + 1))) q8
  have e : rnSub (2 * 1 + 1) = q4 := by decide
  rw [e]
  exact Interd.imp_congr chainF_one_q5 (Interd.refl q4)

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.width_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms width_infinite

/-- info: 'PLLND.RNEmbed.gap_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_off_image

/-- info: 'PLLND.RNEmbed.gap_not_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_not_chain

/-- info: 'PLLND.RNEmbed.gap_one_q8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_one_q8

end RNEmbed
end PLLND
