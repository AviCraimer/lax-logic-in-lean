import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed

/-!
# Scout for the one-variable ∃-side witness sweep

Measures (a) the sizes of the objects in play (`rnSub n`, `gap k`) and
(b) the wall-clock cost of a two-sided `settleWhy` on the queries the
sweep will issue, so the sweep's budget and size bound can be chosen
from data rather than guessed.

NOTE on imports: `wip.gapWidth` / `wip.witness` cannot be imported by an
executable root — their closure contains `wip.rnc_probe`, which declares a
root-level `main`.  So `gap`, `chainF`, `wC` are re-declared here, *verbatim*
(`chainF k := (rnSub (2k+1)).somehow`, `gap k := (chainF k) ⊃ rnSub (2k+1)`,
`wC k := gap k ∧ rnSub (2k+4)`); they are definitionally the repo's.

Run: `scripts/probe 300 wscout`.
-/

open PLLFormula PLLND PLLND.Search PLLND.RNEmbed

namespace WScout

def chainF (k : Nat) : PLLFormula := (rnSub (2 * k + 1)).somehow
def gap (k : Nat) : PLLFormula := (chainF k).ifThen (rnSub (2 * k + 1))
def wC (k : Nat) : PLLFormula := (gap k).and (rnSub (2 * k + 4))

def sz : PLLFormula → Nat
  | .prop _ => 1
  | .falsePLL => 1
  | .and a b => 1 + sz a + sz b
  | .or a b => 1 + sz a + sz b
  | .ifThen a b => 1 + sz a + sz b
  | .somehow a => 1 + sz a

def cfg (b : Nat) : Config := { findBudget := some b, emitClosureCap := 0 }

def verd (b : Nat) (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy (cfg b) Γ C with
  | .proved t => s!"PROVED({t.size})"
  | .refuted M w _ => s!"REFUTED[n={M.n},w={w}]"
  | .unknown (.budgetExhausted b) => s!"?budget({b})"
  | .unknown _ => "?other"

def P : PLLFormula := .prop pv

def timed (f : Unit → String) : IO (String × Nat) := do
  let t0 ← IO.monoMsNow
  let s ← IO.lazyPure f
  let _ ← IO.lazyPure (fun _ => s.length)
  let t1 ← IO.monoMsNow
  pure (s, t1 - t0)

def run : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  pl "== sizes =="
  for n in [0,1,2,3,4,5,6,7,8,9,10,11] do
    pl s!"  |rnSub {n}| = {sz (rnSub n)}"
  for k in [1,2,3,4,5] do
    pl s!"  |gap {k}| = {sz (gap k)}   |chainF {k}| = {sz (chainF k)}"
  pl s!"  |wC 1| = {sz (wC 1)}"
  pl ""
  pl "== timing: positive queries (known PROVED: t3 ⊢ gap k) =="
  for k in [1,2,3,4,5] do
    let (s, ms) ← timed (fun _ => verd 40000 [rnSub 3] (gap k))
    pl s!"  t3 ⊢ gap {k} : {s}   [{ms} ms]"
  pl ""
  pl "== timing: sequent form  φ, chainF k ⊢ rnSub (2k+1) =="
  for k in [1,2,3] do
    let (s, ms) ← timed (fun _ => verd 40000 [rnSub 3, chainF k] (rnSub (2*k+1)))
    pl s!"  k={k} : {s}   [{ms} ms]"
  pl ""
  pl "== timing: negative queries (expected REFUTED) =="
  let (s1, m1) ← timed (fun _ => verd 40000 [P] (gap 1))
  pl s!"  p ⊢ gap 1 : {s1}   [{m1} ms]"
  let (s2, m2) ← timed (fun _ => verd 40000 [P] (gap 2))
  pl s!"  p ⊢ gap 2 : {s2}   [{m2} ms]"
  let (s3, m3) ← timed (fun _ => verd 40000 [P.somehow] (gap 1))
  pl s!"  ◯p ⊢ gap 1 : {s3}   [{m3} ms]"
  let (s4, m4) ← timed (fun _ => verd 40000 [P.ifThen falsePLL] (gap 1))
  pl s!"  ¬p ⊢ gap 1 : {s4}   [{m4} ms]"
  pl ""
  pl "== timing: rung-dodge filter (φ ⊬ rnSub n) =="
  for n in [1,3,5,7,9] do
    let (s, ms) ← timed (fun _ => verd 40000 [P] (rnSub n))
    pl s!"  p ⊢ rnSub {n} : {s}   [{ms} ms]"
  pl ""
  pl "== timing: w15 dodge =="
  let (s5, m5) ← timed (fun _ => verd 40000 [P] (wC 1))
  pl s!"  p ⊢ w15 : {s5}   [{m5} ms]"
  pl "done"

end WScout

def main : IO Unit := WScout.run
