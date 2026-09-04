import wip.atomForce
import LaxLogic.PLLSearchPin

/-!
# The fresh-antecedent goal branch, closed without the ∃-ascent

PROGRESS §93 addendum lists two open branches at target budget `1`.  The second
is the descent's goal-side clause for `C = C₁ ⊃ C₂` with `C₁ ∉ Γ`.  It is not
budget-gated, so both components sit at the incoming budget:

    source   E@2(C₁::Γ)  ⇢  A@2(C₁::Γ, C₂)
    target   E@1(C₁::Γ)  ⇢  A@1(C₁::Γ, C₂)

The obvious route introduces the target's guard and fires the source, which needs
`E@2(C₁::Γ)` from `E@1(C₁::Γ)` and the ambient at the *ungrown* context — the
∃-ascent, refuted at budget `1` by `not_ambGuardAscent`.  That is why this branch
has been open since July.

**But the branch does not have to go that way.**  `wip/sealprobe10.lean` finds a
**9-node** derivation of the whole target at `C = r ⊃ s`, reaching the target's own
goal clause in 8 — while the ascent instance the obvious route would need is
itself undecided by the same search.  So at least at these configurations the
branch closes with no ascent at all.

This file pins those two instances.  What it does *not* do is give the general
lemma: at `C = r ⊃ z`, where the goal's consequent is unrelated to the γ-clause,
the same cell is undecided (`wip/sealprobe11.lean` pushes it further), and the two
non-goal target disjuncts are *refuted* there.  So the route found here uses the
link between `C₂` and the γ-clause's consequent, and the general question is open.

Still, it changes the shape of the open problem: the second residual branch is
**not** known to depend on the refuted ascent, and the search says it sometimes
does not.
-/

open PLLFormula PLLND

namespace PLLND
namespace FreshAnt

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }

def G1 : List PLLFormula := [gam "r" "s"]

def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }

def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]


/-! ### The deciding cell: consequent unrelated to the context

At `C = r ⊃ z` the goal's consequent occurs nowhere in the context, and
`wip/sealprobe10.lean` shows every target disjunct **other** than the goal clause
is *refuted* there.  So the goal clause is the only candidate, which makes this the
cell that decides whether a general lemma can exist.  `wip/sealprobe11.lean` proves
it at `findBudget` 200 000, 2 000 000 and `none` (exhaustive) — 56 nodes — while
the ∃-ascent instance the natural route would need is still undecided at 200 000.

`goalClause0` is that goal clause, `E@1(r::Γ) ⇢ A@1(r::Γ, z)`. -/

/-- The target's goal clause for `r ⊃ z` at `Γ`. -/
def goalClause0 : PLLFormula :=
  (itpAoth "p" S1 3 1 G1 ((prop "r").ifThen (prop "z"))).getD 0 falsePLL

/-- The fresh-antecedent goal branch at target budget `1`, pinned by `#pinsrc` (9 nodes).  It uses **no** existential ascent. -/
theorem fresh_ant_S1 :
    G4c [itpE "p" S1 4 2 G1, (itpE "p" S1 3 2 ((prop "r") :: G1)).ifThen (itpA "p" S1 3 2 ((prop "r") :: G1) (prop "s"))]
      (orAll (itpAoth "p" S1 3 1 G1 ((prop "r").ifThen (prop "s")))) :=
  (((.orR1 (.impR (.orR1 (.andL (.head _) (.andL (.tail _ (.head _)) (.impLOr (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.andL (.head _) (.init (.head _))))))))))) :
    G4cTm [itpE "p" S1 4 2 G1, (itpE "p" S1 3 2 ((prop "r") :: G1)).ifThen (itpA "p" S1 3 2 ((prop "r") :: G1) (prop "s"))]
      (orAll (itpAoth "p" S1 3 1 G1 ((prop "r").ifThen (prop "s"))))).toG4c

/-- The fresh-antecedent goal branch at target budget `1`, pinned by `#pinsrc` (9 nodes).  It uses **no** existential ascent. -/
theorem fresh_ant_S2 :
    G4c [itpE "p" S2 4 2 G2, (itpE "p" S2 3 2 ((prop "r") :: G2)).ifThen (itpA "p" S2 3 2 ((prop "r") :: G2) (prop "s"))]
      (orAll (itpAoth "p" S2 3 1 G2 ((prop "r").ifThen (prop "s")))) :=
  (((.orR1 (.impR (.orR1 (.andL (.head _) (.andL (.tail _ (.head _)) (.impLOr (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.andL (.head _) (.init (.head _))))))))))) :
    G4cTm [itpE "p" S2 4 2 G2, (itpE "p" S2 3 2 ((prop "r") :: G2)).ifThen (itpA "p" S2 3 2 ((prop "r") :: G2) (prop "s"))]
      (orAll (itpAoth "p" S2 3 1 G2 ((prop "r").ifThen (prop "s"))))).toG4c

/-- The fresh-antecedent goal branch reaching the target's own goal clause, at the cell whose consequent is unrelated to the context.  Pinned by `#pinsrc` (56 nodes).  Uses **no** existential ascent. -/
theorem fresh_ant_unrelated_goalclause :
    G4c [itpE "p" S1 4 2 G1, (itpE "p" S1 3 2 ((prop "r") :: G1)).ifThen (itpA "p" S1 3 2 ((prop "r") :: G1) (prop "z"))]
      (goalClause0) :=
  (((.impR (.orR1 (.andL (.head _) (.andL (.tail _ (.head _)) (.impLOr (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.andL (.head _) (.andL (.tail _ (.head _)) (.andL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) (.andL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.impLOr (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impLOr (.tail _ (.tail _ (.head _))) (.impLAnd (.head _) (.impLOr (.head _) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))) (.impLOr (.head _) (.impLOr (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impLAnd (.head _) (.andL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))) (.impLAnd (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))))))))))))))) (.impLProp (.head _) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.init (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))))))))))) (.andR (.init (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))))))))) (.impR (.botL (.head _)))))) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.init (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))))))))))))) (.andR (.init (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))))))))))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.init (.head _)) (.orL (.head _) (.andL (.head _) (.orL (.tail _ (.head _)) (.init (.head _)) (.botL (.head _)))) (.orL (.head _) (.andL (.head _) (.orL (.tail _ (.head _)) (.init (.head _)) (.botL (.head _)))) (.botL (.head _))))))))))))))))))))))))))))))))) :
    G4cTm [itpE "p" S1 4 2 G1, (itpE "p" S1 3 2 ((prop "r") :: G1)).ifThen (itpA "p" S1 3 2 ((prop "r") :: G1) (prop "z"))]
      (goalClause0)).toG4c


/-- **The whole target follows**, since the goal clause is its first disjunct. -/
theorem fresh_ant_unrelated_S1 :
    G4c [itpE "p" S1 4 2 G1,
         (itpE "p" S1 3 2 ((prop "r") :: G1)).ifThen
           (itpA "p" S1 3 2 ((prop "r") :: G1) (prop "z"))]
      (orAll (itpAoth "p" S1 3 1 G1 ((prop "r").ifThen (prop "z")))) := by
  refine G4c.orAll_intro (φ := goalClause0) ?_ fresh_ant_unrelated_goalclause
  show goalClause0 ∈ itpAoth "p" S1 3 1 G1 ((prop "r").ifThen (prop "z"))
  decide

end FreshAnt
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.FreshAnt.fresh_ant_S1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FreshAnt.fresh_ant_S1

/-- info: 'PLLND.FreshAnt.fresh_ant_S2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.FreshAnt.fresh_ant_S2

/--
info: 'PLLND.FreshAnt.fresh_ant_unrelated_S1' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.FreshAnt.fresh_ant_unrelated_S1
