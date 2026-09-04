import LaxLogic.PLLSemUIFrag

/-!
# The chain criteria: refutation instruments for the two quantifiers

`PROGRESS-POLAR.md` §5: `∃p φ` is the least element of the filter of `p`-free
consequences of `φ`; `∀p φ` the greatest element of the ideal of `p`-free
formulas entailing `φ`.  Each fails exactly when a strictly monotone chain of
`p`-free formulas escapes — descending and coinitial for `∃p`, ascending and
cofinal for `∀p`.

(In fact monotonicity of the chain is NOT needed — the proofs consume only the
per-step strictness and the trapping, so the hypotheses ask for less than the
prose above.  Found by the unused-variable linter.)

This file proves the two criteria, **generic in the chain and in the class of
"`p`-free" formulas** (any predicate `P`), so that a future witness `φ` plus a
chain instantly refutes the corresponding quantifier.  Both are five-line
lattice arguments; their value is that they turn each hunt into exactly two
checkable obligations.

**Scope, stated plainly (Matthew's point, 2026-08-08 evening).**  These
criteria are REFUTATION-ONLY.  For the positive direction they are useless:
proving that *no* chain escapes, for *every* `φ`, is not a route.  The
positive route is the second-order candidate method — see
`LaxLogic/PLLCandLeast.lean`, built alongside this file.
-/

namespace PLLND
open SemUI
namespace UIChains

/-- **The `∃p` refutation criterion.**  If a strictly descending chain `D` of
`P`-formulas lies above `φ` and is coinitial among `φ`'s `P`-consequences,
then `φ` has no least `P`-consequence — no post-interpolant. -/
theorem no_least_consequence (P : PLLFormula → Prop) (D : Nat → PLLFormula)
    (hP : ∀ n, P (D n))
    (hstrict : ∀ n, ¬ Deriv [D n] (D (n + 1)))
    (φ : PLLFormula)
    (hbelow : ∀ n, Deriv [φ] (D n))
    (htrap : ∀ ψ, P ψ → Deriv [φ] ψ → ∃ n, Deriv [D n] ψ) :
    ¬ ∃ χ, P χ ∧ Deriv [φ] χ ∧
        (∀ ψ, P ψ → Deriv [φ] ψ → Deriv [χ] ψ) := by
  rintro ⟨χ, hχP, hχc, hleast⟩
  obtain ⟨n, hn⟩ := htrap χ hχP hχc
  have h₁ : Deriv [χ] (D (n + 1)) := hleast (D (n + 1)) (hP _) (hbelow _)
  exact hstrict n (Deriv.cutHead hn h₁)

/-- **The `∀p` refutation criterion.**  If a strictly ascending chain `A` of
`P`-formulas lies below `φ` and is cofinal among the `P`-formulas entailing
`φ`, then `φ` has no greatest `P`-antecedent — no pre-interpolant. -/
theorem no_greatest_antecedent (P : PLLFormula → Prop) (A : Nat → PLLFormula)
    (hP : ∀ n, P (A n))
    (hstrict : ∀ n, ¬ Deriv [A (n + 1)] (A n))
    (φ : PLLFormula)
    (habove : ∀ n, Deriv [A n] φ)
    (htrap : ∀ ψ, P ψ → Deriv [ψ] φ → ∃ n, Deriv [ψ] (A n)) :
    ¬ ∃ χ, P χ ∧ Deriv [χ] φ ∧
        (∀ ψ, P ψ → Deriv [ψ] φ → Deriv [ψ] χ) := by
  rintro ⟨χ, hχP, hχa, hgreatest⟩
  obtain ⟨n, hn⟩ := htrap χ hχP hχa
  have h₁ : Deriv [A (n + 1)] χ := hgreatest (A (n + 1)) (hP _) (habove _)
  exact hstrict n (Deriv.cutHead h₁ hn)

end UIChains
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.UIChains.no_least_consequence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.UIChains.no_least_consequence

/-- info: 'PLLND.UIChains.no_greatest_antecedent' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.UIChains.no_greatest_antecedent
