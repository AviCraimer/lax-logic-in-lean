import wip.rnEmbed
import wip.rnDict

/-!
# What the two-generator question actually is

Stated properly, following Matthew's framing: a substitution `p ↦ A` is
always a homomorphism from the free one-generated Heyting algebra (the
Rieger–Nishimura lattice) into the Lindenbaum algebra of PLL, because
substitution commutes with the connectives.  Nothing has to be proved
about that.  What matters is **injectivity**, and for `A = ◯⊥` that is
exactly `rnEmbed.rn_pairwise_pll`:

    theorem rn_pairwise_pll {i j : Nat} (h : i ≠ j) :
        ¬ Interd (rnSub i) (rnSub j)

So the two-generator question is the same question one dimension up:
let `τ` send `p ↦ ◯⊥` and `q ↦ ◯¬◯⊥`, giving a homomorphism from the
free TWO-generated Heyting algebra into PLL's Lindenbaum algebra.  Is
`τ` injective?

**No** — and `W` below is the witness.  It is a two-variable formula
that `τ` sends to `⊤` while `W` itself is not even classically valid
(put `p := ⊤`, `q := ⊥`, and `W` becomes `⊤ ⊃ ⊥`).  So `τ` identifies
two distinct elements of the free algebra, `[W]` and `[⊤]`.

That is the correct statement of what the last probe found.  It is NOT
an axiom scheme: `(p ∨ ¬p) ⊃ q` with `p`, `q` arbitrary would entail
`p ⊃ q` for all `p, q` and collapse everything.  It is a single formula
that happens to become valid under this one interpretation.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- Second generator: `◯¬◯⊥`. -/
def oNotOBot : PLLFormula := (oBot.ifThen falsePLL).somehow

/-- The witness, under `τ`: `(◯⊥ ∨ ¬◯⊥) ⊃ ◯¬◯⊥`.  Its preimage in the
free two-generated Heyting algebra is `(p ∨ ¬p) ⊃ q`. -/
def tauW : PLLFormula :=
  (oBot.or (oBot.ifThen falsePLL)).ifThen oNotOBot

/-- **`τ` is not injective.**  `τ(W) = ⊤`, though `W` is not valid.

Both disjuncts reach `◯¬◯⊥`: from `◯⊥` because `◯⊥ ⊢ ◯X` for every `X`
(open it, then ex falso), and from `¬◯⊥` by the unit of the monad. -/
theorem tauW_derivable : Deriv [] tauW := by
  refine Deriv.impIntro (Deriv.orElim (Deriv.iden (.head _)) ?_ ?_)
  · -- ◯⊥ ⊢ ◯¬◯⊥
    exact dSomehowElim (Deriv.iden (.head _))
      (Deriv.falsoElim _ (Deriv.iden (.head _)))
  · -- ¬◯⊥ ⊢ ◯¬◯⊥
    exact dSomehowIntro (Deriv.iden (.head _))

/-- The property that FAILS, written out: injectivity of `τ` on the free
two-generated Heyting algebra would say that interderivability of two
substituted two-variable formulas forces their IPC-equivalence.
`tauW_derivable` refutes it, taking `X := (p ∨ ¬p) ⊃ q` and `Y := ⊤`. -/
def TauInjective (τ : String → PLLFormula) : Prop :=
  ∀ X Y : PLLFormula,
    Interd (substP "p" (τ "p") (substP "q" (τ "q") X))
           (substP "p" (τ "p") (substP "q" (τ "q") Y)) →
    Interd X Y

/-- info: 'PLLND.RNEmbed.tauW_derivable' does not depend on any axioms -/
#guard_msgs in
#print axioms tauW_derivable

end RNEmbed
end PLLND
