import LaxLogic.PLLSearch
import LaxLogic.PLLSearchPin
import wip.rnDict

/-!
# The meet `◯¬◯⊥ ∧ ¬¬◯⊥`: the one visible candidate for a fresh seed

A fresh embedding of RN({p}) needs a NON-dense seed off the image of
`h` (`wip/overlap.lean`).  Non-dense means not above the guard; every
known off-image class is above the guard.  The only way to build an
off-image candidate below the guard cone from known material is a meet,
and `q5 ∧ q6` is the one meet of an off-image class with a ladder class
where neither side derives the other.  This probe asks what it is:
`⊥`?  an existing class?  or a new, non-dense, off-image class?

Run: `scripts/probe 240 meetprobe > wip/meetprobe_out.txt`.
-/

open PLLFormula PLLND PLLND.Search PLLND.SemUI.RND

namespace MeetProbe

def m : PLLFormula := q5.and q6

def cfg : Config := { findBudget := some 40000, emitClosureCap := 30 }

def verd (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match settleWhy cfg Γ C with
  | .proved t => s!"PROVED({t.size})"
  | .refuted M w _ => s!"REFUTED[n={M.n},ri={M.ri},rm={M.rm},F={M.fall},w={w}]"
  | .unknown _ => "?"

def dict : List (String × PLLFormula) :=
  [("q0",q0),("q1",q1),("q2",q2),("q3",q3),("q4",q4),("q5",q5),("q6",q6),
   ("q7",q7),("q8",q8),("q9",q9),("q10",q10),("q11",q11),("q12",q12),
   ("q13",q13),("q14",q14)]

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (x : String) : IO Unit := do out.putStrLn x; out.flush
  pl s!"m = q5 ∧ q6 = {m.toString}"
  pl ""
  let c ← IO.lazyPure (fun _ => verd [m] falsePLL)
  let _ ← IO.lazyPure (fun _ => c.length)
  pl s!"consistency:  m ⊢ ⊥ : {c}"
  let d ← IO.lazyPure (fun _ => verd [] ((m.ifThen falsePLL).ifThen falsePLL))
  let _ ← IO.lazyPure (fun _ => d.length)
  pl s!"density:  ⊢ ¬¬m : {d}"
  let g ← IO.lazyPure (fun _ => verd [q4] m)
  let _ ← IO.lazyPure (fun _ => g.length)
  pl s!"guard ⊢ m : {g}"
  pl ""
  pl "identity against the 15:"
  for (nm, B) in dict do
    let f ← IO.lazyPure (fun _ => verd [m] B)
    let _ ← IO.lazyPure (fun _ => f.length)
    let b ← IO.lazyPure (fun _ => verd [B] m)
    let _ ← IO.lazyPure (fun _ => b.length)
    pl s!"  m ⊢ {nm}: {f}   {nm} ⊢ m: {b}"
  pl "done"

end MeetProbe

def main : IO Unit := MeetProbe.main
