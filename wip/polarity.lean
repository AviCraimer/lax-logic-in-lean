import LaxLogic.PLLSearchCmd

/-!
# `◯`-right is not invertible in the SINGLE-judgment presentation

`docs/lax-logic-interpolation-handoff.md` proposes recasting the
contraction-usage metric as a **polarity-phase** measure in a focused,
polarised calculus, and assigns `◯` negative (asynchronous) polarity on the
strength of its intro rule being invertible.

The Twelf `lax-logic` development agrees: in its target it declares
`circ : prop pos → prop neg`, so `◯` is negative there, taking a positive
proposition to a negative one — the shape of an up-shift.  Its rules are

    Γ ⊢ P lax                     Γ, ◯P, P ⊢ A lax
    ─────────── circR             ───────────────── circL
    Γ ⊢ ◯P true                   Γ, ◯P ⊢ A lax

This file records the one fact that makes those rules *necessary* rather than
stylistic, and it is a fact about OUR calculus, which has a single judgment.

## The fact

Negativity is invertibility of the right rule.  In the two-judgment
Pfenning–Davies setting `circR` **is** invertible, because its premise is the
`lax` judgment on `P`, not the `true` judgment: `◯P true` and `P lax` are
interderivable by construction.  In a single-judgment calculus there is no
`lax` judgment to fall back to, and the corresponding statement would have to
be

    Γ ⊢ ◯A   ⟹   Γ ⊢ A

which is **false**.  So the invertibility that licenses the negative
assignment is bought by the second judgment, and cannot be read off our `SC` /
`LaxND` presentation.  Painting polarities onto the existing calculus will not
work; the two-judgment structure has to be adopted first.  That is exactly
step 1 of the handoff's programme, and this is why it is not optional.

## Why this is the good news

The restriction the handoff calls "the real monster" — that the `◯`-left rule
fires only when the goal is itself `◯`-shaped — reappears in the target as
`circL`'s succedent being `A lax`.  A condition on the *shape of the
succedent formula*, which entangles antecedent with consequent, has become a
condition on *which judgment we are in*, which is precisely what a focusing
phase tracks.  That is the mechanism by which polarisation could dissolve the
entanglement, and it is worth stating as the thing to aim at.

Note also that `circL` **retains** `◯P` in its premise, exactly as our `G4c`
retention repairs do (`docs/calculus-map.md`, the three retention rules).  The
"contraction by the back door" the handoff worries about is already present,
and already tamed, in the target calculus.
-/

open PLLFormula PLLND PLLND.Search

namespace Polarity

def p : PLLFormula := prop "p"

/-! ## `◯`-right is not invertible here -/

/-- `◯p ⊬ p`.  With `◯p ⊢ ◯p` by identity, this says the rule
`Γ ⊢ ◯A ⟹ Γ ⊢ A` is unavailable, so `◯R` is not invertible in a calculus
whose only judgment is `true`.  (Contrast the EMPTY context, where reflection
DOES hold — `⊢ ◯A → ⊢ A`, `wip/boxTop.lean`.  Non-invertibility is a statement
about open sequents.) -/
theorem box_right_not_invertible : ¬ Nonempty (LaxND [p.somehow] p) :=
  FinCM.not_provable_of_check
    (M := ⟨2, [(0,1)], [(0,1)], [], [(1,"p")]⟩) (w := 0) (by decide)

/-! ## `◯`-left inversion, by contrast, is unconditional here

From `◯A` on the left one may always pass to `A` on the left, for ANY
succedent — not only a `◯`-shaped one.  So the goal-restriction in `SC`'s
`laxL` is a restriction on the *rule*, not a semantic necessity: the
inference it licenses is available anyway, through the unit.  This is what
makes the `lax`-judgment reformulation faithful. -/

/-- The unit `A ⊢ ◯A`. -/
theorem unit (A : PLLFormula) : Nonempty (LaxND [A] A.somehow) :=
  ⟨.laxIntro (.iden (by simp))⟩

/-- `◯`-left inversion, unrestricted in the succedent. -/
theorem box_left_invertible {Γ : List PLLFormula} {A C : PLLFormula}
    (h : Nonempty (LaxND (A.somehow :: Γ) C)) : Nonempty (LaxND (A :: Γ) C) := by
  obtain ⟨d⟩ := h
  obtain ⟨u⟩ := unit A
  refine ⟨LaxND.impElim (φ := A.somehow) ?_ ?_⟩
  · exact (LaxND.impIntro d).rename (fun θ hθ => List.mem_cons_of_mem _ hθ)
  · exact u.rename (fun θ hθ => by simp at hθ; simp [hθ])

end Polarity

/-! ### Axiom audit -/

/-- info: 'Polarity.box_right_not_invertible' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Polarity.box_right_not_invertible

/-- info: 'Polarity.box_left_invertible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Polarity.box_left_invertible
