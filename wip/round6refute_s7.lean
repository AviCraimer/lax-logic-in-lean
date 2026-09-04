import round6refute

/-! # ROUND 6 screen, stage 7 — stage 6's tail, re-run after the kill

Stage 6's shell was killed mid `s17d`, before its olean was written; the
∨ block and the July `D=p` / `D=r` deep blocks completed and are on
`wip/round6refute_out2.txt`.  This file is standalone (it re-declares
the second-transcript runner, since `round6refute_s6.olean` does not
exist) and runs exactly the unfinished blocks: the plain-`Sk` deep rows
and the July `D=gk` deep cells.  Same configs, same transcript. -/

open PLLFormula PLLND PLLND.Search
open PLLND.Round5Refute PLLND.Round6Refute

namespace PLLND
namespace Round6RefuteS7

def outPath7 : System.FilePath := "wip/round6refute_out2.txt"

def banner7 (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath7 IO.FS.Mode.append
  emit6 h s!"== {s} =="

/-- `Round6Refute.runInst6` with the output path swapped to the second
transcript (verbatim copy of stage 6's `runInst6b`). -/
def runInst7 (cf : Config) (cap : Nat) (i : BInst) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath7 IO.FS.Mode.append
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

/-- Deep positive stage only (July band; closures too big to emit). -/
def cfgD7 : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 20000
  , emitClosureCap := 0 }

def julyDeepFuels1' : List (Nat × Nat) := [(4,4), (3,4), (1,4), (5,5)]
def julyDeepFuels23' : List (Nat × Nat) := [(4,4), (1,4)]

def t17 : BInst :=
  { j1A with name := "J-JULY plain-Sk D=r DEEP b=1", budgets := [1], fuels := julyDeepFuels1' }
def t18 : BInst :=
  { j1B with name := "J-JULY plain-Sk D=p DEEP b=1", budgets := [1], fuels := julyDeepFuels1' }
def t11 : BInst :=
  { j11 with name := "J-JULY ctx=Gk D=gk DEEP b=1", budgets := [1], fuels := julyDeepFuels1' }
def t12 : BInst :=
  { j11 with name := "J-JULY ctx=Gk D=gk DEEP b=2,3", budgets := [2, 3], fuels := julyDeepFuels23' }

end Round6RefuteS7
end PLLND

open PLLND.Round6RefuteS7

#eval banner7 "round 6, stage 7: stage-6 tail (plain-Sk deep; July D=gk deep)"
#eval runInst7 cfgD7 60000 t17
#eval runInst7 cfgD7 60000 t18
#eval runInst7 cfgD7 60000 t11
#eval runInst7 cfgD7 60000 t12
#eval banner7 "stage 7 done"
