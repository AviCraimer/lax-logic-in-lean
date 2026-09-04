import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# Case-splitting on the second component

`wip/sealRefute.lean` refutes all three *uniform* routes to the boxed
γ-disjunct at target budget `1`, so the branch needs a case analysis.  The
question left open in PROGRESS §87 was what the cases are.

There is a candidate the July survey did not consider, because it looked at the
source's *first* component and at the target's disjuncts.  The branch's **third
hypothesis is itself a disjunction**:

    A@1(B::Γ, C)  =  orAll (itpAoth p S F 1 (B::Γ) C)

so `orAll_elim` on it *is* a case analysis, available for free, with one case
per disjunct of the grown-context table.  And the two refuting models of §87
are consistent with this: in each of them the route that succeeds is determined
by which disjunct of the second component holds.

This file tests the mechanism directly.  For each disjunct `ψ` of
`itpAoth p S F 1 (B::Γ) C` it asks the oracle for

    E@2(Γ) ,  ◯( E@1(Γ) ⇢ A@1(Γ, ◯A) ) ,  ψ   ⊢   ⋁ itpAoth p S fl 1 Γ C

— the branch obligation with the second hypothesis *replaced by one of its
disjuncts*.  If every case comes out `PROVED`, the mechanism works and the
branch is provable by `orAll_elim` plus one route per case; a `REFUTED!` in any
case kills it outright, and is a refutation of the whole obligation too (since
that disjunct implies the second hypothesis).

Output is deliberately terse — one line per disjunct.

Run: `lake build sealprobe6 && .lake/build/bin/sealprobe6`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe6

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

/-- One live γ-clause. -/
def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

/-- Two live γ-clauses, so `s :: Γ` still has one. -/
def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }
def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

def cfg (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }

def tag (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) : String :=
  match settleWhy cf hyps goal with
  | .proved _ => "PROVED"
  | .refuted _ _ _ => "REFUTED!"
  | .unknown (.budgetExhausted k) => s!"~{k}"
  | .unknown (.closureTooBig _ _) => "~closure"
  | .unknown .allStagesMissed => "~allStages"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== case-splitting the boxed γ-branch on its second component =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  let C := prop "z"
  for (snm, S, Γ) in [("S1 (one live γ-clause)", S1, G1),
                      ("S2 (two live γ-clauses)", S2, G2)] do
    for f in [3, 4] do
      let F := f
      let fl := f
      let amb := itpE "p" S (fl + 1) 2 Γ
      let box := (((itpE "p" S F 1 Γ).ifThen
        (itpA "p" S F 1 Γ A.somehow)).somehow)
      let goal := orAll (itpAoth "p" S fl 1 Γ C)
      let cases := itpAoth "p" S F 1 (B :: Γ) C
      pl s!"{snm}  fuel {f}: second component has {cases.length} disjunct(s), \
goal weight {goal.weight}"
      -- the whole obligation, for reference
      let whole := tag (cfg 40000) [amb, box, itpA "p" S F 1 (B :: Γ) C] goal
      pl s!"   whole obligation                : {whole}"
      -- and one line per disjunct
      let mut i := 0
      for ψ in cases do
        let t ← IO.lazyPure (fun _ => tag (cfg 40000) [amb, box, ψ] goal)
        let _ ← IO.lazyPure (fun _ => t.length)
        pl s!"   case {i} (weight {ψ.weight}) : {t}"
        i := i + 1
  pl ""
  pl "== done =="

end SealProbe6

def main : IO Unit := SealProbe6.main
