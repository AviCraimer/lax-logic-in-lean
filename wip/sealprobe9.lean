import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# The boxed goal, with a `◯χ` in the context

At a **boxed** goal the universal table has one environment clause family that
exists at no other goal shape: for each `◯χ ∈ Γ` with `χ ∈ S ∖ Γ`,

    ◯( E@b(χ::Γ) ⇢ A@b(χ::Γ, C) )        (`itpAenv`, the `.somehow χ` row)

The configurations probed so far (`wip/sealprobe7.lean`) have **no** `◯χ` in the
context, so that family was empty and the route table's boxed row had only the
goal clause and the γ-disjuncts to aim at — all three unreachable.

This probe adds a `◯w` to the context, so the extra family is live, and asks the
same question: which target disjunct can each case of the analysis reach?  If the
new family is reachable, that is the missing route and it is available exactly
when the context has a boxed member — a condition on `Γ`, decidable, and the sort
of thing a case split can be built on.

Run: `lake build sealprobe9 && .lake/build/bin/sealprobe9`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe9

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

/-- The γ-clause, plus a boxed context member `◯w` (piece-closed: `w ∈ S`). -/
def Sb : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    (prop "w").somehow, prop "w", prop "z" }

/-- The context has both the γ-clause and the boxed member. -/
def Gb : List PLLFormula := [gam "r" "s", (prop "w").somehow]

/-- Control: the same space without the boxed member in the context. -/
def Gb0 : List PLLFormula := [gam "r" "s"]

def cfg (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }

def tag (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) : String :=
  match settleWhy cf hyps goal with
  | .proved t => s!"PROVED({t.size})"
  | .refuted _ _ _ => "REFUTED"
  | .unknown _ => "~"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== boxed goal with a ◯χ in the context =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  let C := (prop "s").somehow
  for (gnm, Γ) in [("Γ = [◯r⊃s, ◯w]  (boxed member LIVE)", Gb),
                   ("Γ = [◯r⊃s]        (control)", Gb0)] do
    let F := 3
    let fl := 3
    let amb := itpE "p" Sb (fl + 1) 2 Γ
    let box := (((itpE "p" Sb F 1 Γ).ifThen
      (itpA "p" Sb F 1 Γ A.somehow)).somehow)
    let tgts := itpAoth "p" Sb fl 1 Γ C
    let cs := itpAfull "p" Sb F 1 (B :: Γ) C
    pl s!"{gnm}: {cs.length} case(s), {tgts.length} target disjunct(s), \
weights {tgts.map PLLFormula.weight}"
    let whole ← IO.lazyPure (fun _ =>
      tag (cfg 20000) [amb, box, itpA "p" Sb (F + 1) 1 (B :: Γ) C] (orAll tgts))
    let _ ← IO.lazyPure (fun _ => whole.length)
    pl s!"   whole obligation: {whole}"
    let mut i := 0
    for ψ in cs do
      let mut hits : List String := []
      let mut j := 0
      for χ in tgts do
        let t ← IO.lazyPure (fun _ => tag (cfg 20000) [ψ, amb, box] χ)
        let _ ← IO.lazyPure (fun _ => t.length)
        if t.startsWith "PROVED" then hits := hits ++ [s!"{j}:{t}"]
        j := j + 1
      let hitStr := if hits.isEmpty then "NOTHING" else String.intercalate ", " hits
      pl s!"   case {i} (weight {ψ.weight}) reaches: {hitStr}"
      i := i + 1
  pl ""
  pl "== done =="

end SealProbe9

def main : IO Unit := SealProbe9.main
