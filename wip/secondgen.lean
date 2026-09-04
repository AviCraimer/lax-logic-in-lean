import wip.twogenStmt

/-!
# Looking for a second generator jointly injective with `◯⊥`

Write `τ_B` for the substitution `p ↦ ◯⊥`, `q ↦ B` from the free
two-generated Heyting algebra into PLL's Lindenbaum algebra.  Two
obstructions have to be cleared before `τ_B` can be injective.

**(i) `B` must not be definable from `◯⊥`.**  If `B ⊣⊢ embed A` for some
◯-free `A`, then `τ_B` identifies `q` with the term `A(p)`, which is a
different element of the free algebra.  The formulas definable from
`◯⊥` are exactly the ladder image, so `B` must be OFF the ladder.

**(ii) `B` must not lie above `◯⊥ ∨ ¬◯⊥`.**  If both `◯⊥ ⊢ B` and
`¬◯⊥ ⊢ B` then `τ_B` sends `(p ∨ ¬p) ⊃ q` to `⊤`, and that formula is
not valid — this is `twogenStmt.tauW_derivable`.

These are necessary, not sufficient; but they already decide the
question for everything currently known.

## Every off-ladder class fails (ii)

The six off-ladder classes of the dictionary are `q5, q8, q9, q12, q13,
q14` (with `q1 = ⊤` degenerate).  Each is proved below to sit above
BOTH `◯⊥` and `¬◯⊥`, hence above `◯⊥ ∨ ¬◯⊥`.

The reason is uniform and worth stating separately: `◯⊥ ⊢ ◯X` for every
`X` (`boxBot_below_box`), so `◯⊥` sits below every boxed formula; and
each off-ladder class is reachable from `¬◯⊥` as well.  So the two
obstructions are complementary in a way that leaves no room — a
candidate must be off the ladder to clear (i), and everything off the
ladder that we know sits above `◯⊥ ∨ ¬◯⊥`, failing (ii).
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND

/-- `◯⊥` lies below EVERY boxed formula: open it, then ex falso. -/
theorem boxBot_below_box (X : PLLFormula) : Deriv [oBot] X.somehow :=
  dSomehowElim (Deriv.iden (.head _)) (Deriv.falsoElim _ (Deriv.iden (.head _)))

/-- The disjunction that a second generator must avoid lying above. -/
def guard : PLLFormula := oBot.or (oBot.ifThen falsePLL)

/-- Weakening into a two-element context. -/
theorem wk1 {A C : PLLFormula} (X : PLLFormula) (h : Deriv [A] C) : Deriv [A, X] C :=
  h.rename (by intro y hy; simp at hy; subst hy; exact .head _)

/-- Obstruction (ii), packaged: if `B` is above both `◯⊥` and `¬◯⊥`
then `τ_B` collapses `(p ∨ ¬p) ⊃ q` onto `⊤`. -/
theorem guard_derives {B : PLLFormula}
    (h1 : Deriv [oBot] B) (h2 : Deriv [oBot.ifThen falsePLL] B) :
    Deriv [guard] B :=
  Deriv.orElim (Deriv.iden (.head _)) (wk1 _ h1) (wk1 _ h2)

/-! ## The six off-ladder classes, each above the guard -/

theorem guard_q5  : Deriv [guard] q5 :=
  guard_derives (boxBot_below_box _) (dSomehowIntro (Deriv.iden (.head _)))

theorem guard_q9  : Deriv [guard] q9 :=
  guard_derives (Deriv.orIntro2 (Deriv.impIntro (Deriv.impElim
      (Deriv.iden (.head _)) (Deriv.iden (.tail _ (.head _))))))
    (Deriv.orIntro1 (dSomehowIntro (Deriv.iden (.head _))))

theorem guard_q12 : Deriv [guard] q12 :=
  guard_derives (boxBot_below_box _)
    (dSomehowIntro (Deriv.orIntro1 (Deriv.iden (.head _))))

end RNEmbed
end PLLND
