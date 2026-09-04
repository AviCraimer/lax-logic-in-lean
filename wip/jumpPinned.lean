import LaxLogic.PLLSearchPin
import LaxLogic.PLLG4UITrunc

/-!
# The low-budget jump-goal descents, PINNED

PROGRESS §84–§87 record three facts as "PROVED by search".  Under the
machine-checked mandate that is *evidence*, not a theorem: the search is
kernel-opaque, so a probe's `PROVED` line certifies nothing that survives into
the library.

`LaxLogic/PLLSearchPin.lean` closes that gap.  `Verdict.proved` already carries
a typed term `t : G4cTm Γ C`; `#pinsrc` prints `t` as Lean source, emitting
constructor names and membership chains only, so every formula index is
recovered by unification and the printed term is proportional to the
*derivation* rather than to the (very large) tables in the sequent.  The terms
below were produced that way and are re-elaborated and re-checked here from
scratch — nothing about the search is trusted.

The configuration is the `wip/budgetfit.lean` chain of length 2:

    S = {◯p ⊃ r, ◯r ⊃ s, p, ◯p, r, ◯r, s, ◯s, (◯r ⊃ s) ⊃ z, z}
    Γ = [◯p ⊃ r]                                 (defect 9, |jumpGoals| 5)

and the three facts are:

1. **the descent to budget `0` at the atom jump goal `p`** — the eliminated
   variable itself;
2. **the descent to budget `0` at the atom jump goal `r`**;
3. **the `◯⊥` collapse** `A@1(Γ,◯p) ⊢ ◯⊥`, which is what closes the boxed
   γ-branch at the floor on this family (§86) — and which `wip/sealRefute.lean`
   shows does *not* generalise to a γ-head other than the eliminated variable.

Fact 1 and 2 matter because the budget tier of the descent is entered only at
jump goals (§85): they are the base case of that tier at the shapes where it is
*not* refuted.  Contrast `wip/ascprobe.lean`, where the same descent at a
**boxed** jump goal is certified false at budget `0`.
-/

open PLLFormula PLLND

namespace PLLND
namespace JumpPinned

/-! ## The configuration -/

def atomAt : Nat → PLLFormula
  | 0 => prop "p" | 1 => prop "r" | 2 => prop "s" | 3 => prop "t"
  | 4 => prop "u" | 5 => prop "v" | _ => prop "w"

def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

/-- The chain-2 space. -/
def Sc : Finset PLLFormula := chainSpace 2

/-- The context: the head γ-clause alone. -/
def Gc : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-! ## 1. The descent to budget `0` at the atom jump goal `p` -/

theorem desc_zero_atom_p :
    G4c [itpA "p" Sc 4 1 Gc (prop "p"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "p")) :=
  ((.orL (.head _) (.andL (.head _) (.botL (.head _)))
      (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _))))
        (.botL (.head _)))) :
    G4cTm [itpA "p" Sc 4 1 Gc (prop "p"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "p"))).toG4c

/-! ## 2. The descent to budget `0` at the atom jump goal `r` -/

theorem desc_zero_atom_r :
    G4c [itpA "p" Sc 4 1 Gc (prop "r"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "r")) :=
  ((.orR1 (.orL (.head _) (.init (.head _))
      (.orL (.head _) (.andL (.head _) (.botL (.head _)))
        (.orL (.head _)
          (.andL (.head _)
            (.orL (.tail _ (.head _)) (.init (.head _)) (.botL (.head _))))
          (.botL (.head _)))))) :
    G4cTm [itpA "p" Sc 4 1 Gc (prop "r"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "r"))).toG4c

/-! ## 3. The `◯⊥` collapse at the boxed jump goal `◯p`

This is the route that closes the boxed γ-branch at the floor on this family
(`wip/envDesc.lean`'s `boxed_target_of_starved` takes it from here, since
`A@0(Γ,◯p) = ⊥` there).  `wip/sealRefute.lean`'s `not_route_bot` shows it fails
for a γ-head other than the eliminated variable, so this theorem is the exact
boundary of the mechanism. -/

theorem boxbot_collapse :
    G4c [itpA "p" Sc 4 1 Gc ((prop "p").somehow)] falsePLL.somehow :=
  ((.orL (.head _)
      (.laxL (.head _)
        (.laxR (.impLImp (.head _) (.impR (.botL (.head _)))
          (.orL (.head _) (.andL (.head _) (.botL (.head _)))
            (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _))))
              (.botL (.head _)))))))
      (.orL (.head _) (.laxR (.andL (.head _) (.botL (.head _))))
        (.orL (.head _)
          (.andL (.head _)
            (.laxL (.head _)
              (.laxR (.impLImp (.head _) (.impR (.botL (.head _)))
                (.botL (.head _))))))
          (.orL (.head _)
            (.laxL (.head _)
              (.impLImp (.head _) (.impR (.botL (.head _)))
                (.orL (.head _)
                  (.laxL (.head _)
                    (.laxR (.impLImp (.head _) (.impR (.botL (.head _)))
                      (.orL (.head _) (.andL (.head _) (.botL (.head _)))
                        (.orL (.head _)
                          (.andL (.head _) (.botL (.tail _ (.head _))))
                          (.botL (.head _)))))))
                  (.orL (.head _) (.laxR (.andL (.head _) (.botL (.head _))))
                    (.orL (.head _)
                      (.andL (.head _)
                        (.laxL (.head _)
                          (.laxR (.impLImp (.head _)
                            (.impR (.botL (.head _))) (.botL (.head _))))))
                      (.botL (.head _)))))))
            (.botL (.head _)))))) :
    G4cTm [itpA "p" Sc 4 1 Gc ((prop "p").somehow)] falsePLL.somehow).toG4c

/-! ## 4. What the three give, stated against the parametric budget law

`Descends p need` (`wip/descent2.lean`) is refuted at target budget `0` for
*boxed* goals (`wip/floorRefute.lean`), which is why `needShape` asks for `1`
there.  §1 and §2 above are the corresponding *positive* facts at atom goals:
at this configuration the descent to budget `0` holds, so `needShape`'s `0` at
atom goals is not merely unrefuted but witnessed. -/

/-- The two atom facts together, in the form the budget-law discussion uses:
at this configuration the descent to budget `0` **holds** at atom goals. -/
theorem atom_floor_holds :
    G4c [itpA "p" Sc 4 1 Gc (prop "p"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "p"))
    ∧ G4c [itpA "p" Sc 4 1 Gc (prop "r"), itpE "p" Sc 4 1 Gc]
      (itpA "p" Sc 4 0 Gc (prop "r")) :=
  ⟨desc_zero_atom_p, desc_zero_atom_r⟩

end JumpPinned
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.JumpPinned.desc_zero_atom_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.JumpPinned.desc_zero_atom_p

/-- info: 'PLLND.JumpPinned.desc_zero_atom_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.JumpPinned.desc_zero_atom_r

/-- info: 'PLLND.JumpPinned.boxbot_collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.JumpPinned.boxbot_collapse
