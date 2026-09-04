import wip.gap2

/-!
# Testing the hypothesis: RN(◯,{})'s structure as a SEMANTIC obstruction to UI

**The bridge.**  A uniform post-interpolant `∃p.φ` of a one-variable
formula must be VARIABLE-FREE — an element of RN(◯,{}) — and must be
the LEAST variable-free consequence of `φ`.  The variable-free
consequences of any `φ` form a filter (up-closed, ∧-closed), so
`∃p.φ` exists iff that filter is principal.  Dually `∀p.φ` is the
GREATEST variable-free antecedent; the antecedents form an ideal
(down-closed, ∨-closed).  So the semantic shape of a UI failure is:

  * a consequence filter containing an infinite STRICTLY DESCENDING
    meet-chain with no floor inside the filter, or
  * an antecedent ideal containing an infinite STRICTLY ASCENDING
    join-chain with no ceiling inside the ideal

— exactly the Ghilardi–Zawadowski mechanism for the failure of UI in
S4-like logics.  **This file proves that RN(◯,{}) supplies both
engines**, and reduces the hypothesis to one concrete witness
question.

Proved here (all PLL):

1. `t3_below_gap`: the whole gap antichain has the common floor `t3`
   — so the antichain ALONE does not obstruct (RN(◯,{}) is a lattice
   and the finite meets exist as formulas); the obstruction must come
   from non-stabilising meet-chains, which is exactly what happens:
2. `Gmeet_strict` / `Gmeet_desc_strict`: the partial meets
   `g 1 ∧ … ∧ g (n+1)` DESCEND STRICTLY FOREVER — incidentally the
   first infinite strictly descending chain proved in RN(◯,{}).
3. `no_post_interp_schema` / `no_pre_interp_schema`: the reduction
   theorems.  For the ∃-side: any `φ` entailing every `g k`, none of
   whose variable-free consequences entails every `g k`, has NO
   uniform post-interpolant.  For the ∀-side, dually with the c-chain
   (`chainF k`) and antecedents.
4. `chain_cofinal_not_rung` and the earlier family lemmas: no KNOWN
   class except `⊤` bounds the c-chain from above — supporting (but
   not proving) that the ∀-side hypothesis is satisfiable.

**Verdict of the test so far**: the hypothesis is structurally
CONFIRMED — the infinite antichain generates the non-stabilising
descending meet-chain that a UI failure needs, and the chain generates
the ascending side.  What remains to produce an actual counterexample
to UI is ONE witness: a one-variable `φ` entailed by every `chainF k`
(resp. entailing every `gap k`) with no variable-free formula between
the family and `φ`.  Whether such `φ` exists is precisely where the
syntactic UI hunt got stuck from the other side; if NO such witness
exists, uniform interpolants survive this attack — that alternative is
also recorded honestly in the schemas' hypotheses.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## Variable-freeness of the substituted rungs and the families -/

theorem rnP_sub_atomFree :
    ∀ k, atomFree (embed (rnP k).1) = true ∧ atomFree (embed (rnP k).2) = true := by
  intro k
  induction k with
  | zero => exact ⟨by decide, by decide⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show (atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2)) = true
        rw [h1, h2]
        rfl
      · show ((atomFree (embed (rnP k).1) && atomFree (embed (rnP k).2)) &&
            atomFree (embed (rnP k).1)) = true
        rw [h1, h2]
        rfl

theorem rnSub_atomFree (n : Nat) : atomFree (rnSub n) = true := by
  match n with
  | 0 => rfl
  | m + 1 =>
      show atomFree (embed (if m % 2 = 0 then (rnP (m / 2)).1
        else (rnP (m / 2)).2)) = true
      split
      · exact (rnP_sub_atomFree _).1
      · exact (rnP_sub_atomFree _).2

theorem chainF_atomFree (k : Nat) : atomFree (chainF k) = true := by
  show atomFree (rnSub (2 * k + 1)) = true
  exact rnSub_atomFree _

theorem gap_atomFree (k : Nat) : atomFree (gap k) = true := by
  show (atomFree (chainF k) && atomFree (rnSub (2 * k + 1))) = true
  rw [chainF_atomFree, rnSub_atomFree]
  rfl

/-! ## 1. The antichain has a common floor -/

/-- **`t3 ⊢ g k` for every `k ≥ 1`**: the whole gap antichain sits
above `t3` — the antichain alone cannot obstruct meets. -/
theorem t3_below_gap {k : Nat} (hk : 1 ≤ k) : Deriv [rnSub 3] (gap k) :=
  Deriv.cutHead (rungD (oo_le hk)) (rung_le_gap k)

/-! ## 2. The partial meets descend strictly forever -/

/-- `Gmeet n = g 1 ∧ g 2 ∧ … ∧ g (n+1)`. -/
def Gmeet : Nat → PLLFormula
  | 0 => gap 1
  | n + 1 => (Gmeet n).and (gap (n + 2))

theorem Gmeet_le (n : Nat) : Deriv [Gmeet (n + 1)] (Gmeet n) :=
  Deriv.andElim1 (Deriv.iden (.head _))

/-- In `cmE m` with the window above all its levels, `Gmeet n` is
forced everywhere. -/
theorem Gmeet_forced {m : Nat} :
    ∀ {n : Nat}, n + 1 ≤ m → ∀ x : Nat, (cmE m).force (some x) (Gmeet n) := by
  intro n
  induction n with
  | zero =>
      intro h x
      exact gap_forced m 1 (by omega) (by omega) x
  | succ n ih =>
      intro h x
      exact ⟨ih (by omega) x, gap_forced m (n + 2) (by omega) (by omega) x⟩

/-- **The partial meets never reach the next gap**:
`g 1 ∧ … ∧ g (n+1) ⊬ g (n+2)`. -/
theorem Gmeet_strict (n : Nat) : ¬ Deriv [Gmeet n] (gap (n + 2)) := by
  rintro ⟨d⟩
  have hs := soundness d (cmE (n + 1)) (some ((n + 1) + 3)) (fun ψ hψ => by
    have e : ψ = Gmeet n := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact Gmeet_forced (le_refl _) ((n + 1) + 3))
  exact gap_fails (n + 1) (n + 2) (by omega) (by omega) hs

/-- **RN(◯,{}) contains an infinite strictly DESCENDING chain**:
`Gmeet 0 > Gmeet 1 > Gmeet 2 > …`. -/
theorem Gmeet_desc_strict (n : Nat) : ¬ Deriv [Gmeet n] (Gmeet (n + 1)) :=
  fun h => Gmeet_strict n
    (Deriv.cutHead h (Deriv.andElim2 (Deriv.iden (.head _))))

/-! ## 3. Uniform interpolants over the variable-free fragment, and
the obstruction schemas -/

/-- `ψ` is a uniform post-interpolant (`∃`-side) of `φ` over the
variable-free fragment: variable-free, a consequence, and the least
such. -/
def IsPostInterp (φ ψ : PLLFormula) : Prop :=
  atomFree ψ = true ∧ Deriv [φ] ψ ∧
    ∀ χ, atomFree χ = true → Deriv [φ] χ → Deriv [ψ] χ

/-- `ψ` is a uniform pre-interpolant (`∀`-side) of `φ`: variable-free,
an antecedent, and the greatest such. -/
def IsPreInterp (φ ψ : PLLFormula) : Prop :=
  atomFree ψ = true ∧ Deriv [ψ] φ ∧
    ∀ χ, atomFree χ = true → Deriv [χ] φ → Deriv [χ] ψ

/-- **Obstruction schema, `∃`-side**: if `φ` entails every gap but
none of its variable-free consequences does, then `φ` has no uniform
post-interpolant. -/
theorem no_post_interp_schema {φ : PLLFormula}
    (hg : ∀ k, 1 ≤ k → Deriv [φ] (gap k))
    (hL : ∀ χ, atomFree χ = true → (∀ k, 1 ≤ k → Deriv [χ] (gap k)) →
      ¬ Deriv [φ] χ) :
    ¬ ∃ ψ, IsPostInterp φ ψ := by
  rintro ⟨ψ, hψa, hφψ, hmin⟩
  exact hL ψ hψa (fun k hk => hmin (gap k) (gap_atomFree k) (hg k hk)) hφψ

/-- **Obstruction schema, `∀`-side**: if every `chainF k` entails `φ`
but no variable-free formula above the whole chain does, then `φ` has
no uniform pre-interpolant. -/
theorem no_pre_interp_schema {φ : PLLFormula}
    (hc : ∀ k, Deriv [chainF k] φ)
    (hU : ∀ χ, atomFree χ = true → (∀ k, Deriv [chainF k] χ) →
      ¬ Deriv [χ] φ) :
    ¬ ∃ ψ, IsPreInterp φ ψ := by
  rintro ⟨ψ, hψa, hψφ, hmax⟩
  exact hU ψ hψa (fun k => hmax (chainF k) (chainF_atomFree k) (hc k)) hψφ

/-! ## 4. No known class but `⊤` bounds the c-chain -/

/-- The c-chain is cofinal over the rungs: `chainF (n+1) ⊬ t n` for
every `n` — no rung bounds the chain. -/
theorem chain_cofinal_not_rung (n : Nat) :
    ¬ Deriv [chainF (n + 1)] (rnSub n) := by
  rintro ⟨d⟩
  have hs := soundness d ladder.cm (some (n + 1)) (fun ψ hψ => by
    have e : ψ = chainF (n + 1) := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact (chainF_force_iff (n + 1) (n + 1)).mpr (le_refl _))
  have hb := rungMem_bound
    ((sat_rung n (n + 1)).mp ((ladder.transfer (rn_boxFree n) (n + 1)).mp hs))
  omega

/-! ## Axiom audits — sorry-free, all PLL -/

/-- info: 'PLLND.RNEmbed.t3_below_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms t3_below_gap

/-- info: 'PLLND.RNEmbed.Gmeet_desc_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Gmeet_desc_strict

/-- info: 'PLLND.RNEmbed.no_post_interp_schema' does not depend on any axioms -/
#guard_msgs in
#print axioms no_post_interp_schema

/-- info: 'PLLND.RNEmbed.no_pre_interp_schema' does not depend on any axioms -/
#guard_msgs in
#print axioms no_pre_interp_schema

/-- info: 'PLLND.RNEmbed.chain_cofinal_not_rung' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms chain_cofinal_not_rung

end RNEmbed
end PLLND
