import round6refute

/-! # ROUND 6 screen, stage 6 — deep settling pass on the `~` residue

The breadth stages (1–4) ran countermodel-first at `findBudget 400` with
the closure emitter OFF; their `~` cells saw the full battery and
nothing else.  This stage re-runs the interesting residue two-sidedly:

* the ∨-families' residual cells (tiny — |s+a+t| ≤ 3k — so the closure
  emitter, a COMPLETE refuter over the closure, is feasible: cap 16);
* the July `ctx = Gk` band at `d = 8/9` (the round's priority-1 cells;
  sizes 1–35k, emitter infeasible, positive stage deepened to 20000
  nodes).

Writes to `wip/round6refute_out2.txt` (stage 5 owns the main transcript
while it runs). -/

open PLLFormula PLLND PLLND.Search
open PLLND.Round5Refute PLLND.Round6Refute

namespace PLLND
namespace Round6Refute

def outPath6b : System.FilePath := "wip/round6refute_out2.txt"

def banner6b (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath6b IO.FS.Mode.append
  emit6 h s!"== {s} =="

/-- `runInst6` with the output path swapped — see `runInst6` for the
schema.  Kept as a verbatim copy so stage 6 can run concurrently with
stage 5 without interleaving transcripts. -/
def runInst6b (cf : Config) (cap : Nat) (i : BInst) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath6b IO.FS.Mode.append
  let S := i.S
  let d := defect S i.ctx
  let J := (jumpGoals S).card
  let room := d * (J + 2)
  emit6 h s!"{i.name}: |S|={i.Sl.length} d={d} J={J} room={room} \
adm={admissible i} gates(jump/box/env)=\
{liveJumpGates i.Sl i.ctx}/{liveBoxGates i.Sl i.ctx}/{liveBoxEnv i.Sl i.ctx}"
  if !(admissible i) then
    emit6 h "  INADMISSIBLE — skipped"
  else
    let bs := if i.budgets.isEmpty then [1, 2, 3] else i.budgets
    for b in bs do
      if b == 0 then
        emit6 h "  b=0: outside the statement (1 ≤ b) — skipped"
      else
        let band := if b < room then "SUB" else "ROOM+"
        let fps := if i.fuels.isEmpty then
            [(b+2, b+2), (b+1, b+2), (1, b+2), (2, b+3), (b+3, b+3)]
          else i.fuels
        for fp in fps do
          if fp.1 > fp.2 then pure () else do
            let fs := fp.1; let ft := fp.2
            let t0 ← IO.monoMsNow
            let src ← IO.lazyPure (fun _ => srcOf i fs b)
            let amb ← IO.lazyPure (fun _ => ambOf i ft b)
            let tgt ← IO.lazyPure (fun _ => tgtOf i ft b)
            let nsz ← IO.lazyPure (fun _ =>
              TowerKit.sz src + TowerKit.sz amb + TowerKit.sz tgt)
            if nsz > cap then
              emit6 h s!"  fs={fs} ft={ft} b={b} {band}: SKIP |s+a+t|={nsz} > {cap}"
            else
              let act ← IO.lazyPure (fun _ => tgtOf i ft (b + 1) != tgt)
              let v ← IO.lazyPure (fun _ => settleWhy cf [src, amb] tgt)
              let t1 ← IO.monoMsNow
              match v with
              | .proved _ =>
                  emit6 h s!"  fs={fs} ft={ft} b={b} {band}: P  act={act} \
|s+a+t|={nsz} ({t1 - t0} ms)"
              | .refuted M w _ =>
                  emit6 h s!"  fs={fs} ft={ft} b={b} {band}: R! *** REFUTES \
BoxDesc *** act={act} |s+a+t|={nsz} ({t1 - t0} ms) w={w} M={reprStr M}"
              | .unknown r =>
                  emit6 h s!"  fs={fs} ft={ft} b={b} {band}: ~  act={act} \
|s+a+t|={nsz} ({t1 - t0} ms) [{r.describe}]"

/-- Two-sided config for the tiny ∨-cells: deep positive stage AND the
closure emitter (complete over closures ≤ 16). -/
def cfgS : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 20000
  , emitClosureCap := 16 }

/-- Deep positive stage only (July band; closures too big to emit). -/
def cfgD : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 20000
  , emitClosureCap := 0 }

/-! The ∨-families, same grids as stages 3–4. -/

def s41d : BInst := { j21 with name := "OR-BOX/miss-e DEEP" }
def s42d : BInst := { j22 with name := "OR-BOX/miss-e,f DEEP" }
def s45d : BInst := { j25 with name := "OR-IN-JUMP/miss-c DEEP" }
def s46d : BInst := { j26 with name := "OR-IN-JUMP/miss-b,c DEEP" }
def s47d : BInst := { j27 with name := "OR-GATE/miss-f∨c DEEP" }
def s48d : BInst := { j28 with name := "OR-GATE/miss-f,c,f∨c DEEP" }
def s43d : BInst := { i41 with name := "OR/miss-e DEEP (r5 i41)" }
def s44d : BInst := { i42 with name := "OR/miss-e,f DEEP (r5 i42)" }
def s49d : BInst := { i43 with name := "OR/miss-D DEEP (r5 i43)" }

/-! The July `ctx = Gk` cells, budget-1 rows plus matched-fuel b=2/3. -/

def julyDeepFuels1 : List (Nat × Nat) := [(4,4), (3,4), (1,4), (5,5)]
def julyDeepFuels23 : List (Nat × Nat) := [(4,4), (1,4)]

def s11d : BInst :=
  { j11 with name := "J-JULY ctx=Gk D=gk DEEP b=1", budgets := [1], fuels := julyDeepFuels1 }
def s12d : BInst :=
  { j11 with name := "J-JULY ctx=Gk D=gk DEEP b=2,3", budgets := [2, 3], fuels := julyDeepFuels23 }
def s13d : BInst :=
  { j12 with name := "J-JULY ctx=Gk D=r DEEP b=1", budgets := [1], fuels := julyDeepFuels1 }
def s14d : BInst :=
  { j12 with name := "J-JULY ctx=Gk D=r DEEP b=2,3", budgets := [2, 3], fuels := julyDeepFuels23 }
def s15d : BInst :=
  { j13 with name := "J-JULY ctx=Gk D=p DEEP b=1", budgets := [1], fuels := julyDeepFuels1 }
def s16d : BInst :=
  { j13 with name := "J-JULY ctx=Gk D=p DEEP b=2,3", budgets := [2, 3], fuels := julyDeepFuels23 }
def s17d : BInst :=
  { j1A with name := "J-JULY plain-Sk D=r DEEP b=1", budgets := [1], fuels := julyDeepFuels1 }
def s18d : BInst :=
  { j1B with name := "J-JULY plain-Sk D=p DEEP b=1", budgets := [1], fuels := julyDeepFuels1 }

end Round6Refute
end PLLND

open PLLND.Round6Refute

#eval banner6b "round 6, stage 6: deep settling (∨ two-sided w/ emitter; July 20k nodes)"
#eval runInst6b cfgS 60000 s41d
#eval runInst6b cfgS 60000 s42d
#eval runInst6b cfgS 60000 s45d
#eval runInst6b cfgS 60000 s46d
#eval runInst6b cfgS 60000 s47d
#eval runInst6b cfgS 60000 s48d
#eval runInst6b cfgS 60000 s43d
#eval runInst6b cfgS 60000 s44d
#eval runInst6b cfgS 60000 s49d
#eval banner6b "∨ block done; July deep block"
#eval runInst6b cfgD 60000 s15d
#eval runInst6b cfgD 60000 s16d
#eval runInst6b cfgD 60000 s13d
#eval runInst6b cfgD 60000 s14d
#eval runInst6b cfgD 60000 s17d
#eval runInst6b cfgD 60000 s18d
#eval runInst6b cfgD 60000 s11d
#eval runInst6b cfgD 60000 s12d
#eval banner6b "stage 6 done"
