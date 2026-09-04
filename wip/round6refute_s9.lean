import round6refute

/-! # ROUND 6, stage 9 — instrumentation: closure lengths

Whether the closure emitter (complete over the closure) actually RAN on
a `~` cell depends on `closureOf ≤ emitClosureCap`; the printed reason
(`budgetExhausted`) does not distinguish.  This records the closure
lengths for the three escalated JB2 cells (cap was 24) and a sample
∨-cell (cap was 16). -/

open PLLFormula PLLND PLLND.Search
open PLLND.Round5Refute PLLND.Round6Refute

def cloLen (Γ : List PLLFormula) (C : PLLFormula) : Nat :=
  (CounterEmit.closureOf (Γ.map nf) (nf C)).length

def cellClo (i : BInst) (fs ft b : Nat) : Nat :=
  cloLen [srcOf i fs b, ambOf i ft b] (tgtOf i ft b)

#eval banner6 "stage 9: closure lengths (emitter feasibility record)"
#eval do
  let h ← IO.FS.Handle.mk outPath6 IO.FS.Mode.append
  emit6 h s!"JB2 b=3 (1,5) closure = {cellClo i21 1 5 3} (cap was 24)"
  emit6 h s!"JB2 b=3 (4,5) closure = {cellClo i21 4 5 3} (cap was 24)"
  emit6 h s!"JB2 b=3 (5,5) closure = {cellClo i21 5 5 3} (cap was 24)"
  emit6 h s!"OR-BOX/miss-e,f b=1 (3,3) closure = {cellClo j22 3 3 1} (cap was 16)"
  emit6 h s!"OR-BOX/miss-e,f b=3 (6,6) closure = {cellClo j22 6 6 3} (cap was 16)"
  emit6 h s!"JULY ctx=Gk D=gk b=1 (4,4) closure = {cellClo j11 4 4 1} (emitter off)"
#eval banner6 "stage 9 done"
