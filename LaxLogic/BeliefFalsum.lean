import LaxLogic.PLLFrames

/-!
# The believer may believe the absurd: `◯⊥` is consistent and non-trivial

This mechanises handover §3b-4, the PLL-side of the belief-vs-knowledge contrast.
Reading `◯M` as "M is believed", `◯⊥` reads "the absurd is believed".  In PLL:

* `◯⊥` is **consistent** — `¬◯⊥` is not a theorem (`belief_no_D`).  PLL has no
  doxastic `D` axiom `¬◯⊥`: a believer *may* believe the absurd.
* `◯⊥` is **not valid** — `◯⊥` is not a theorem (`belief_bot_not_provable`), so
  `◯⊥ ≠ ⊤`: believing the absurd is not forced either.
* Hence `◯⊥` is a genuine intermediate element `⊥ ≠ ◯⊥ ≠ ⊤` (indeed the free
  generator of the closed fragment; see `wip/lax_infinite.lean`).
* **Credulous collapse at the `◯`-level** — `◯⊥ ⊢ ◯M` for every `M`
  (`belief_credulous`): a believer who believes the absurd believes everything.
  Yet `◯⊥` does not make everything *true* — `⊥` stays unprovable — so the
  inconsistency is quarantined inside `◯`.

Contrast Artemov–Protopopescu's intuitionistic *knowledge* IEL, which *does*
prove `¬K⊥` (intuitionistic factivity `KA → ¬¬A`); see
`docs/iel-justification-lit.md`.  Provability is `Nonempty (LaxND [] ·)`;
non-provability is by soundness against a constraint countermodel.
-/

open PLLFormula PLLND

namespace BeliefLax

/-- **No consistency axiom (`D`).**  `¬◯⊥` is not a theorem of PLL: a believer
may believe the absurd.  (F&M's fallible countermodel, `PLLFrames`.) -/
theorem belief_no_D : ¬ Nonempty (LaxND [] (notPLL (somehow falsePLL))) :=
  not_provable_not_somehow_false

/-- **`◯⊥` is not valid**, so `◯⊥ ≠ ⊤`: believing the absurd is not forced.
Soundness against an `F = ∅` constraint model, where `◯⊥` fails at the root. -/
theorem belief_bot_not_provable : ¬ Nonempty (LaxND [] (somehow falsePLL)) := by
  rintro ⟨p⟩
  exact absurd (soundness_valid p modelOrSplit .r) (by decide)

/-- **Credulous collapse at the `◯`-level.**  `◯⊥ ⊢ ◯M` for every `M`: believing
the absurd entails believing anything (`◯`-monotonicity applied to ex falso). -/
def belief_credulous (M : PLLFormula) : LaxND [somehow falsePLL] (somehow M) :=
  .laxElim (.iden (List.mem_cons_self ..))
    (.laxIntro (.falsoElim M (.iden (List.mem_cons_self ..))))

/-- The internal form of credulous collapse: `⊢ ◯⊥ ⊃ ◯M`. -/
def belief_credulous_imp (M : PLLFormula) :
    LaxND [] ((somehow falsePLL).ifThen (somehow M)) :=
  .impIntro (belief_credulous M)

end BeliefLax

#print axioms BeliefLax.belief_no_D
#print axioms BeliefLax.belief_bot_not_provable
#print axioms BeliefLax.belief_credulous
#print axioms BeliefLax.belief_credulous_imp
