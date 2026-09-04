import LaxLogic.PLLG4Dec
import LaxLogic.PLLSemUI

/-! Baseline for wip/oracle2.lean: the PLAIN one-sided oracle on the
known-chaotic failing cases, at the fuels the probes used.  Expected to
grind (that is the point); run timeboxed and killed from outside. -/

open PLLFormula PLLND PLLND.SemUI

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def peirceF : PLLFormula := (gB.ifThen pV).ifThen pV

def searchAt (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def cases : List (String × List PLLFormula × PLLFormula) :=
  [ ("U1  ¬¬◯⊥ ⊢ ◯⊥ @500", [nF (nF gB)], gB)
  , ("U2  allCand(peirce) ⊢ peirce @400", [allCand "p" peirceF], peirceF)
  , ("U4  ◯(◯p⊃p) ⊢ ◯⊥ @400", [((pV.somehow).ifThen pV).somehow], gB)
  ]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== plain one-sided baseline =="
  for (name, Γ, C) in cases do
    let fuel := if name.endsWith "@500" then 500 else 400
    let t0 ← IO.monoMsNow
    let v := searchAt fuel Γ C
    let t1 ← IO.monoMsNow
    pl s!"{name}: {v}  ({t1 - t0} ms)"
  pl "== done =="
