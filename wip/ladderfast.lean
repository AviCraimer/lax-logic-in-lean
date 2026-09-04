import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnEmbed
import wip.rnDict

/-!
# The same questions on small equivalents

`rnSub 7` has weight 45 and `rnSub 8` weight 64, which puts the direct
distribution question out of reach of the searcher.  But the rungs have
small representatives: `rnSub 4 ≡ ¬¬◯⊥`, `rnSub 5 ≡ ¬◯⊥ ∨ ¬¬◯⊥`, and
so on.  This probe

* certifies the rung-to-representative identifications, then
* asks the ◯-column and distribution questions on the small forms.

Everything here is a formula of weight under 20, so the searcher
finishes.

Run: `lake build ladderfast && .lake/build/bin/ladderfast`.
-/

open PLLFormula PLLND PLLND.Search

namespace LadderFast

open PLLND.RNEmbed
open PLLND.SemUI.RND

def cfg : Config := { findBudget := some 60000, emitClosureCap := 30 }

def verd (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy cfg Γ C with
  | .proved t => s!"PROVED({t.size})"
  | .refuted M w _ => s!"REFUTED[n={M.n},ri={M.ri},rm={M.rm},F={M.fall},w={w}]"
  | .unknown _ => "?"

def eqv (A B : PLLFormula) : String :=
  let f := verd [A] B
  let g := verd [B] A
  if f.startsWith "PROVED" && g.startsWith "PROVED" then "EQUIVALENT"
  else s!"NOT: (A|-B)={f}  (B|-A)={g}"

def dict : List PLLFormula :=
  [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14]

def matchIn (A : PLLFormula) : String := Id.run do
  let mut i := 0
  for B in dict do
    if (verd [A] B).startsWith "PROVED" && (verd [B] A).startsWith "PROVED" then
      return s!"q{i}"
    i := i + 1
  return "OUTSIDE the 15 representatives"

/-- `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`. -/
def distr (A B : PLLFormula) : PLLFormula :=
  (A.or B).somehow.ifThen ((A.somehow).or (B.somehow))

def say (out : IO.FS.Stream) (label : String) (thunk : Unit → String) : IO Unit := do
  let s ← IO.lazyPure thunk
  let _ ← IO.lazyPure (fun _ => s.length)
  out.putStrLn s!"  {label}: {s}"
  out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush

  pl "===== (A) THE RUNGS HAVE SMALL REPRESENTATIVES ====="
  say out "rnSub 0 = q0  (bot)          " (fun _ => eqv (rnSub 0) q0)
  say out "rnSub 1 = q2  (box bot)      " (fun _ => eqv (rnSub 1) q2)
  say out "rnSub 2 = q3  (not box bot)  " (fun _ => eqv (rnSub 2) q3)
  say out "rnSub 3 = q4  (Obot v ~Obot) " (fun _ => eqv (rnSub 3) q4)
  say out "rnSub 4 = q6  (~~Obot)       " (fun _ => eqv (rnSub 4) q6)
  say out "rnSub 5 = q7  (~Obot v ~~Obot)" (fun _ => eqv (rnSub 5) q7)
  say out "rnSub 6 = q10 (~~Obot > Obot)" (fun _ => eqv (rnSub 6) q10)
  say out "rnSub 7 = q11 (q6 v q10)     " (fun _ => eqv (rnSub 7) q11)
  pl ""

  pl "===== (B) THE BOX COLUMN, on the small forms ====="
  pl "  where does box send each rung?"
  say out "box(rnSub 0) = box bot       " (fun _ => matchIn (q0.somehow))
  say out "box(rnSub 1) = box box bot   " (fun _ => matchIn (q2.somehow))
  say out "box(rnSub 2) = box ~Obot     " (fun _ => matchIn (q3.somehow))
  say out "box(rnSub 3) = box(Obot v ~Obot)" (fun _ => matchIn (q4.somehow))
  say out "box(rnSub 4) = box ~~Obot    " (fun _ => matchIn (q6.somehow))
  say out "box(rnSub 5) = box q7        " (fun _ => matchIn (q7.somehow))
  say out "box(rnSub 6) = box q10       " (fun _ => matchIn (q10.somehow))
  say out "box(rnSub 7) = box q11       " (fun _ => matchIn (q11.somehow))
  pl ""

  pl "===== (C) THE QUESTION ASKED, reduced ====="
  pl "  box(rnSub4 v rnSub3) -> (box rnSub4 v box rnSub3)"
  pl "  reduces to    box q7 -> (box q6 v box q4)"
  say out "is box q7 |- box q6 v box q4 ?" (fun _ => verd [q7.somehow] ((q6.somehow).or (q4.somehow)))
  say out "the closed form, |- distr q6 q4" (fun _ => verd [] (distr q6 q4))
  pl ""

  pl "===== (D) DISTRIBUTION over the small rung representatives ====="
  pl "  |- box(A v B) -> (box A v box B)   for A,B among the rung reps"
  let reps : List (String × PLLFormula) :=
    [("r1=q2", q2), ("r2=q3", q3), ("r3=q4", q4), ("r4=q6", q6),
     ("r5=q7", q7), ("r6=q10", q10)]
  for (na, a) in reps do
    for (nb, b) in reps do
      say out s!"distr {na} {nb}" (fun _ => verd [] (distr a b))
  pl ""
  pl "===== done ====="

end LadderFast

def main : IO Unit := LadderFast.main
