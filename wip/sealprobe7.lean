import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# The floor branch at a BOXED goal: which route does each case take?

`wip/atomForce.lean` closes the floor branches at an **atom** goal, uniformly in
the configuration, and explains why atoms are special: `prop q` is a disjunct of
the target table at *every* context, so a fact proved at the grown context lands
where it is needed.  Every other goal shape's goal clause mentions the context.

So the residue is the floor branch at the other two jump-goal shapes, `◯A` and
`A ⊃ B`.  This probe takes the boxed one.  For each disjunct `ψ` of the second
component it asks, for **each** disjunct `χ` of the target table, whether

    ψ, E@2(Γ), ◯(E@1(Γ) ⇢ A@1(Γ,◯A))  ⊢  χ

so the output is a route table: which target disjunct each case can reach.  A row
with no `PROVED` is a case with no known route and is where the work is; a row
with one tells us the mechanism to prove in general.

Output is one line per (case, target-disjunct) pair that comes out `PROVED`,
plus a summary line per case, to keep it readable.

Run: `lake build sealprobe7 && .lake/build/bin/sealprobe7`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe7

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }
def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

def cfg (bud : Nat) : Config := { findBudget := some bud, emitClosureCap := 0 }

def tag (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) : String :=
  match settleWhy cf hyps goal with
  | .proved t => s!"PROVED({t.size})"
  | .refuted _ _ _ => "REFUTED"
  | .unknown (.budgetExhausted _) => "~"
  | .unknown _ => "~"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the floor branch at a boxed goal: route table =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  for (snm, S, Γ) in [("S1", S1, G1), ("S2", S2, G2)] do
    for (cnm, C) in [("◯s", (prop "s").somehow),
                     ("r ⊃ s", (prop "r").ifThen (prop "s"))] do
      let F := 3
      let fl := 3
      let amb := itpE "p" S (fl + 1) 2 Γ
      let box := (((itpE "p" S F 1 Γ).ifThen
        (itpA "p" S F 1 Γ A.somehow)).somehow)
      let tgts := itpAoth "p" S fl 1 Γ C
      let cs := itpAfull "p" S F 1 (B :: Γ) C
      pl s!"{snm}, C = {cnm}: {cs.length} case(s), {tgts.length} target \
disjunct(s) of weights {tgts.map PLLFormula.weight}"
      let whole ← IO.lazyPure (fun _ =>
        tag (cfg 20000) [amb, box, itpA "p" S (F + 1) 1 (B :: Γ) C]
          (orAll tgts))
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

end SealProbe7

def main : IO Unit := SealProbe7.main
