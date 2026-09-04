import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# The boxed floor branch, at a search budget that can actually find it

Every boxed-goal cell in `wip/sealprobe7.lean` and `wip/sealprobe9.lean` was run
at `findBudget` 20 000.  PROGRESS §95 then found that the *fresh-antecedent*
branch needs **200 000** nodes to turn up a 56-node derivation — the proof is
short, the search space is wide.  So the boxed row's "no case reaches any target
disjunct" may say nothing except that the budget was ten times too small.

This probe re-runs the boxed cells at 200 000 and 2 000 000, per case and per
target disjunct, at both configurations.  Verdicts only — no terms — so the output
stays small.

Run: `lake build sealprobe12 && .lake/build/bin/sealprobe12`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe12

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

def S2 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s",
    gam "u" "v", (prop "u").somehow, prop "u", prop "v", prop "z" }
def G2 : List PLLFormula := [gam "r" "s", gam "u" "v"]

def tag (bud : Nat) (hyps : List PLLFormula) (goal : PLLFormula) : String :=
  match settleWhy { findBudget := some bud, emitClosureCap := 0 } hyps goal with
  | .proved t => s!"PROVED({t.size})"
  | .refuted _ _ _ => "REFUTED"
  | .unknown _ => "~"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the boxed floor branch at 200k and 2M =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  let C := (prop "s").somehow
  for (snm, S, Γ) in [("S1", S1, G1), ("S2", S2, G2)] do
    let F := 3
    let fl := 3
    let amb := itpE "p" S (fl + 1) 2 Γ
    let box := (((itpE "p" S F 1 Γ).ifThen
      (itpA "p" S F 1 Γ A.somehow)).somehow)
    let snd := itpA "p" S (F + 1) 1 (B :: Γ) C
    let tgts := itpAoth "p" S fl 1 Γ C
    let cs := itpAfull "p" S F 1 (B :: Γ) C
    pl s!"{snm}, C = ◯s: {cs.length} case(s), {tgts.length} target disjunct(s)"
    for bud in [200000, 2000000] do
      let w ← IO.lazyPure (fun _ => tag bud [amb, box, snd] (orAll tgts))
      let _ ← IO.lazyPure (fun _ => w.length)
      pl s!"   whole obligation [{bud}]: {w}"
      -- the goal clause alone, from the whole second component
      let g0 ← IO.lazyPure (fun _ =>
        tag bud [amb, box, snd] (tgts.getD 0 falsePLL))
      let _ ← IO.lazyPure (fun _ => g0.length)
      pl s!"   ⊢ goal clause    [{bud}]: {g0}"
      let mut i := 0
      for ψ in cs do
        let mut hits : List String := []
        let mut j := 0
        for χ in tgts do
          let t ← IO.lazyPure (fun _ => tag bud [ψ, amb, box] χ)
          let _ ← IO.lazyPure (fun _ => t.length)
          if t.startsWith "PROVED" then hits := hits ++ [s!"{j}"]
          j := j + 1
        let hitStr := if hits.isEmpty then "NOTHING" else String.intercalate "," hits
        pl s!"   case {i} [{bud}] reaches: {hitStr}"
        i := i + 1
  pl ""
  pl "== done =="

end SealProbe12

def main : IO Unit := SealProbe12.main
