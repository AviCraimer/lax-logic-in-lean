import LaxLogic.PLLSearchPin
import LaxLogic.PLLG4UITrunc

/-!
# Two more facts pinned: the `⊃`-jump-goal floor, and a floor interface instance

Generated with `#pinsrc` (`LaxLogic/PLLSearchPin.lean`) and re-checked here
from scratch.  Both were previously only probe output.

**1. `desc_zero_imp_jump`** — the descent to budget `0` at a `⊃`-shaped jump
goal, on the smallest `⊃⊃`-gated configuration:

    S = piece-closure of {(p⊃r)⊃s},  Γ = [(p⊃r)⊃s, r⊃s],  g = p⊃r.

The `B⊃D` guard material `r⊃s` is in the context, so the gated jump clause
actually reaches its gate (`wip/ascprobe.lean`'s `gateLive` test).  With
`wip/jumpPinned.lean`'s two atom facts this settles the *positive* side of the
budget tier's base case at both non-boxed jump-goal shapes: the descent to
budget `0` holds at atom goals **and** at `⊃`-shaped jump goals.  The boxed
shape is where it is certified false.

**2. `gammaPairFloorA_instance`** — the plain γ-pair branch obligation at target
budget `1`, with the defect tier's contribution pre-applied:

    E@2(Γ), A@1(Γ,p), A@1(r::Γ,z)  ⊢  ⋁ itpAoth p S fl 1 Γ z

on the chain-2 configuration.  This is `GammaPairFloorA`, one of the four
interfaces `wip/cascadeBox.lean` reduces to, at one instance.  It is worth
pinning because it is the **control** for `wip/sealRefute.lean`: the plain
branch goes through where the boxed one has no uniform route, so the
distinction between the two is not an artefact of how hard the search was
pushed.

Both terms are large (349 and 104 nodes) and were generated to a file rather
than transcribed, so no step of the pipeline was manual.
-/

open PLLFormula PLLND

namespace PLLND
namespace PinnedFacts

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

def chainPiecesII (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i =>
    ((atomAt (2 * i)).ifThen (atomAt (2 * i + 1))).ifThen (atomAt (2 * i + 2)))

def chainListII (n : Nat) : List PLLFormula :=
  (chainPiecesII n ++ (List.range (2 * n + 1)).map atomAt
    ++ (List.range (2 * n + 1)).map (fun i => (atomAt i).ifThen (atomAt (i + 1)))
    ++ [prop "z"]).dedup

def chainSpaceII (n : Nat) : Finset PLLFormula := (chainListII n).toFinset

/-- The smallest `⊃⊃`-gated space. -/
def SII : Finset PLLFormula := chainSpaceII 1

/-- Its context, with the `B ⊃ D` guard material present. -/
def GII : List PLLFormula := [((prop "p").ifThen (prop "r")).ifThen (prop "s"),
                              (prop "r").ifThen (prop "s")]

/-- The chain-2 space. -/
def Sc : Finset PLLFormula := chainSpace 2

def Gc : List PLLFormula := [((prop "p").somehow).ifThen (prop "r")]

/-- Pinned by `#pinsrc` (349 nodes). -/
theorem desc_zero_imp_jump :
    G4c [itpA "p" SII 4 1 GII ((prop "p").ifThen (prop "r")), itpE "p" SII 4 1 GII]
      (itpA "p" SII 4 0 GII ((prop "p").ifThen (prop "r"))) :=
  (((.orR1 (.impR (.orR1 (.andL (.head _) (.orL (.tail _ (.tail _ (.tail _ (.head _)))) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLAnd (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.andR (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))) (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.andR (.andL (.tail _ (.head _)) (.init (.head _))) (.impR (.botL (.head _)))))) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))) (.impR (.botL (.head _))))) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.tail _ (.tail _ (.tail _ (.head _)))) (.andL (.head _) (.init (.head _))))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.init (.head _)) (.orL (.head _) (.andL (.head _) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))))))) (.orL (.head _) (.andL (.head _) (.init (.head _))) (.botL (.head _)))))))))) (.orL (.head _) (.andL (.head _) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.andR (.impLAnd (.head _) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.tail _ (.tail _ (.tail _ (.head _)))) (.andL (.head _) (.init (.head _))))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))) (.andL (.head _) (.init (.head _))))))) (.orL (.head _) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.andL (.head _) (.init (.head _)))) (.botL (.head _))))))) (.impR (.botL (.head _)))) (.botL (.head _)))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.andR (.impLAnd (.head _) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.andL (.head _) (.init (.head _))))))) (.impR (.botL (.head _)))) (.botL (.head _)))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.impLAnd (.head _) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.andL (.head _) (.init (.head _))))) (.botL (.head _)))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))) (.impLAnd (.head _) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.andL (.head _) (.init (.head _))))) (.botL (.head _)))))) (.orL (.head _) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))) (.impLAnd (.head _) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.andL (.head _) (.init (.head _))))) (.botL (.head _))) (.botL (.head _))))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.impLAnd (.head _) (.impLImp (.head _) (.impR (.andR (.impLAnd (.tail _ (.head _)) (.impLImp (.tail _ (.tail _ (.tail _ (.head _)))) (.impR (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))) (.andR (.impLAnd (.head _) (.impLImp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impR (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))) (.head _) (.andR (.andL (.head _) (.init (.head _))) (.impR (.botL (.head _)))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))) (.andL (.head _) (.init (.head _))))))) (.impR (.botL (.head _)))) (.botL (.head _)))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))) (.impLAnd (.head _) (.impLProp (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))) (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))) (.andL (.head _) (.init (.head _))))) (.botL (.head _)))))) (.impR (.botL (.head _))))) (.impLImp (.head _) (.impR (.botL (.head _))) (.orL (.head _) (.init (.head _)) (.orL (.head _) (.andL (.head _) (.init (.head _))) (.botL (.head _))))))) (.orL (.head _) (.andL (.head _) (.init (.head _))) (.botL (.head _)))))))) (.orL (.head _) (.andL (.head _) (.init (.head _))) (.botL (.head _)))))))))) :
    G4cTm [itpA "p" SII 4 1 GII ((prop "p").ifThen (prop "r")), itpE "p" SII 4 1 GII]
      (itpA "p" SII 4 0 GII ((prop "p").ifThen (prop "r")))).toG4c

/-- Pinned by `#pinsrc` (104 nodes). -/
theorem gammaPairFloorA_instance :
    G4c [itpE "p" Sc 5 2 Gc, itpA "p" Sc 4 1 Gc (prop "p"), itpA "p" Sc 4 1 ((prop "r") :: Gc) (prop "z")]
      (orAll (itpAoth "p" Sc 4 1 Gc (prop "z"))) :=
  (((.orR1 (.andL (.head _) (.impLOr (.head _) (.impLAnd (.head _) (.impLOr (.tail _ (.tail _ (.head _))) (.impLAnd (.head _) (.andL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))) (.impLLax (.head _) (.impR (.orR1 (.laxR (.impR (.orR1 (.andR (.andL (.tail _ (.head _)) (.andL (.tail _ (.head _)) (.impLLax (.head _) (.impLLax (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.orR1 (.laxR (.impR (.orR1 (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))) (.andR (.andL (.head _) (.botL (.head _))) (.andL (.head _) (.botL (.head _)))) (.andR (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))))) (.impR (.andL (.tail _ (.head _)) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.andL (.head _) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))))))) (.andL (.head _) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))) (.andL (.head _) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))) (.andL (.tail _ (.head _)) (.andL (.tail _ (.head _)) (.impLLax (.head _) (.impLLax (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))) (.impR (.orR1 (.laxR (.impR (.orR1 (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))) (.andR (.andL (.head _) (.botL (.head _))) (.andL (.head _) (.botL (.head _)))) (.andR (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))))) (.impR (.andL (.tail _ (.head _)) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))))))))))))))) (.andL (.head _) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _))))))) (.andL (.head _) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))))))))) (.andL (.head _) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))))))))) (.andL (.head _) (.orL (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))))))))) (.andL (.head _) (.botL (.head _))) (.orL (.head _) (.andL (.head _) (.botL (.tail _ (.head _)))) (.botL (.head _)))))))))))))) :
    G4cTm [itpE "p" Sc 5 2 Gc, itpA "p" Sc 4 1 Gc (prop "p"), itpA "p" Sc 4 1 ((prop "r") :: Gc) (prop "z")]
      (orAll (itpAoth "p" Sc 4 1 Gc (prop "z")))).toG4c


end PinnedFacts
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.PinnedFacts.desc_zero_imp_jump' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.PinnedFacts.desc_zero_imp_jump

/--
info: 'PLLND.PinnedFacts.gammaPairFloorA_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.PinnedFacts.gammaPairFloorA_instance
