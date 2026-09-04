import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin

/-!
# The boxed floor branch at the goal the descent actually reaches

A correction to the earlier boxed-goal probes.  The budget tier of the descent is
entered only at **jump goals** (PROGRESS §85), and for a space whose γ-clause is
`◯A ⊃ B` the jump goals are `A` and `◯A` — **not** `◯B`.  Every earlier boxed-goal
probe used `C = ◯s`, i.e. `◯B`, which is not a jump goal of that space at all.
§97's closure is therefore at a configuration the descent does not reach.

This probe uses `C = ◯r`, the actual boxed jump goal of
`S = {◯r ⊃ s, ◯r, r, s, z}`, and reports the whole obligation and every target
disjunct, with and without the grown ambient `E@2(s::Γ)` supplied as a hint (it is
*derivable* from the ambient and the boxed component by `EnvDesc.grownAmb_of_box`,
so adding it cannot change derivability — only what the searcher can find).

Run: `lake build sealprobe13 && .lake/build/bin/sealprobe13`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe13

def gam (a b : String) : PLLFormula := ((prop a).somehow).ifThen (prop b)

def S1 : Finset PLLFormula :=
  { gam "r" "s", (prop "r").somehow, prop "r", prop "s", prop "z" }
def G1 : List PLLFormula := [gam "r" "s"]

def tag (bud : Nat) (hyps : List PLLFormula) (g : PLLFormula) : String :=
  match settleWhy { findBudget := some bud, emitClosureCap := 0 } hyps g with
  | .proved t => s!"PROVED({t.size})"
  | .refuted _ _ _ => "REFUTED"
  | .unknown _ => "~"

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== boxed floor branch at C = ◯r, the actual boxed jump goal =="
  pl ""
  let A := prop "r"
  let B := prop "s"
  for (cnm, C) in [("◯r  (the jump goal)", (prop "r").somehow),
                   ("r   (the atom jump goal, covered by atomForce)", prop "r")] do
    let amb := itpE "p" S1 4 2 G1
    let box := ((itpE "p" S1 3 1 G1).ifThen
      (itpA "p" S1 3 1 G1 A.somehow)).somehow
    let snd := itpA "p" S1 4 1 (B :: G1) C
    let grown := itpE "p" S1 3 2 (B :: G1)
    let tgts := itpAoth "p" S1 3 1 G1 C
    pl s!"C = {cnm}: {tgts.length} target disjunct(s), weights \
{tgts.map PLLFormula.weight}"
    for bud in [20000, 200000] do
      let w1 ← IO.lazyPure (fun _ => tag bud [amb, box, snd] (orAll tgts))
      let _ ← IO.lazyPure (fun _ => w1.length)
      pl s!"   whole, no hint   [{bud}]: {w1}"
      let w2 ← IO.lazyPure (fun _ => tag bud [amb, box, snd, grown] (orAll tgts))
      let _ ← IO.lazyPure (fun _ => w2.length)
      pl s!"   whole, +grownAmb [{bud}]: {w2}"
      let mut j := 0
      for χ in tgts do
        let d ← IO.lazyPure (fun _ => tag bud [amb, box, snd, grown] χ)
        let _ ← IO.lazyPure (fun _ => d.length)
        pl s!"   disjunct {j} (weight {χ.weight}) +grownAmb [{bud}]: {d}"
        j := j + 1
  pl ""
  pl "== done =="

end SealProbe13

def main : IO Unit := SealProbe13.main
