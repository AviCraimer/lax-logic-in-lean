import wip.boxq11

/-!
# The ◯-chain is strictly increasing at EVERY step

Implementation of `docs/chain-strictness.md`.  `chainF k` is the boxed
odd rung `◯(rnSub (2k+1))`; the theorems are

* `chain_step_le`     : `chainF k ⊢ chainF (k+1)`
* `chain_step_strict` : `chainF (k+1) ⊬ chainF k`
* `chain_up`          : `j ≤ k → chainF j ⊢ chainF k`
* `chain_lt_strict`   : `j < k → chainF k ⊬ chainF j`
* `chain_pairwise`    : `j ≠ k → ¬ Interd (chainF j) (chainF k)`

The negative halves are NOT `decide` on concrete models: they evaluate
ONE infinite constraint model — the abyss lift of the ladder skeleton —
through two general lemmas (`Skel.box_force`, composing with
`Skel.transfer`), and land by `PLLKripke.soundness`.  The instance data
is arithmetic on rung truth sets, uniform in `k`.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- **How `◯` evaluates on any abyss lift**: at a skeleton world the
only `Rₘ`-moves are staying put or (from `U`) jumping to the fallible
top, so `◯N` holds iff every extension is in `U` or forces `N`. -/
theorem Skel.box_force (S : Skel) (N : PLLFormula) (x : S.W) :
    S.cm.force (some x) N.somehow ↔
      ∀ y, S.le x y → (y ∈ S.U ∨ S.cm.force (some y) N) := by
  constructor
  · intro h y hy
    obtain ⟨u, hm, hf⟩ := h (some y) hy
    cases u with
    | none => exact Or.inl hm
    | some z =>
        have hz : y = z := hm
        subst hz
        exact Or.inr hf
  · intro h v hv
    cases v with
    | none => exact ⟨none, trivial, S.cm.force_of_fallible rfl⟩
    | some y =>
        rcases h y hv with hU | hf
        · exact ⟨none, hU, S.cm.force_of_fallible rfl⟩
        · exact ⟨some y, rfl, hf⟩

/-- The lifted-ladder specialisation, through the transfer: a boxed
substituted rung is forced at `some x` iff every cone point is the
`U`-world `0` or lies in the rung's truth set. -/
theorem ladder_box_rn (m : Nat) (x : Nat) :
    ladder.cm.force (some x) ((rnSub m).somehow) ↔
      ∀ y : Nat, ladder.le x y → (y = 0 ∨ ladder.sat (rn m) y) := by
  rw [Skel.box_force]
  exact forall_congr' fun y => imp_congr Iff.rfl
    (or_congr ladder_U (ladder.transfer (rn_boxFree m) y))

/-- The boxed odd rung: `chainF k = ◯(rnSub (2k+1))`;
`chainF 1 ≡ q5`, `chainF 2 ≡ q12`, `chainF 3 = ◯q11`. -/
def chainF (k : Nat) : PLLFormula := (rnSub (2 * k + 1)).somehow

/-- `◯` is monotone. -/
theorem box_mono {A B : PLLFormula} (h : Deriv [A] B) :
    Deriv [A.somehow] B.somehow :=
  dSomehowElim (Deriv.iden (.head _)) (dSomehowIntro (Deriv.toHead h))

/-- **The increasing half**: `chainF k ⊢ chainF (k+1)`, from the odd
rungs' chain (`odd_chain`, pure arithmetic) through `rnSub_order` and
◯-monotonicity. -/
theorem chain_step_le (k : Nat) : Deriv [chainF k] (chainF (k + 1)) := by
  have e : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  show Deriv [(rnSub (2 * k + 1)).somehow] ((rnSub (2 * (k + 1) + 1)).somehow)
  rw [e]
  exact box_mono ((rnSub_order (2 * k + 1) (2 * k + 3)).mpr (odd_chain k))

/-- **The strict half, at every `k`**: `chainF (k+1) ⊬ chainF k`.
Refuted on the lifted ladder at world `k+1`: its cone is
`{k+1} ∪ [0, k−1]`, contained in `T(2k+3) = [0, k+1]` (hypothesis
forced) but with the point `k+1` outside `T(2k+1) = [0, k]`
(conclusion not forced); `soundness` does the rest. -/
theorem chain_step_strict (k : Nat) :
    ¬ Deriv [chainF (k + 1)] (chainF k) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (k + 1)) ?_
  · -- the conclusion is not forced at k+1
    have h := (ladder_box_rn (2 * k + 1) (k + 1)).mp hs (k + 1) (Or.inl rfl)
    rcases h with h0 | hsat
    · omega
    · rw [sat_rn_odd k (k + 1)] at hsat
      omega
  · -- the hypothesis is forced at k+1
    intro ψ hψ
    have e : ψ = chainF (k + 1) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    show ladder.cm.force (some (k + 1)) ((rnSub (2 * (k + 1) + 1)).somehow)
    have e2 : 2 * (k + 1) + 1 = 2 * (k + 1) + 1 := rfl
    rw [ladder_box_rn]
    intro y hy
    refine Or.inr ?_
    rw [sat_rn_odd (k + 1) y]
    rcases (ladder_le.mp hy) with h | h <;> omega

/-- `chainF` ascends: `j ≤ k → chainF j ⊢ chainF k`. -/
theorem chain_up {j k : Nat} (h : j ≤ k) : Deriv [chainF j] (chainF k) := by
  induction k with
  | zero =>
      have : j = 0 := by omega
      subst this
      exact Deriv.iden (.head _)
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Deriv.cutHead (ih (by omega)) (chain_step_le k)
      · have : j = k + 1 := by omega
        subst this
        exact Deriv.iden (.head _)

/-- **Strictness, pairwise**: `j < k → chainF k ⊬ chainF j`.  A
violation would compose with `chain_up` into a violation of the single
step at `j`. -/
theorem chain_lt_strict {j k : Nat} (h : j < k) :
    ¬ Deriv [chainF k] (chainF j) := fun d =>
  chain_step_strict j (Deriv.cutHead (chain_up (show j + 1 ≤ k from h)) d)

/-- **The boxed odd rungs are pairwise non-interderivable**: an
infinite strictly ascending chain of distinct classes in RN(◯,{}). -/
theorem chain_pairwise {j k : Nat} (h : j ≠ k) :
    ¬ Interd (chainF j) (chainF k) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_ge j k with hlt | hge
  · exact chain_lt_strict hlt h2
  · exact chain_lt_strict (by omega : k < j) h1

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.chain_step_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_step_strict

/-- info: 'PLLND.RNEmbed.chain_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_pairwise

end RNEmbed
end PLLND
