import round5refute
import round5refute_bdefs
import round4Comp

/-!
# ROUND 6, REFUTE prong — `Round4.BoxDesc` hunted in the SUB-ROOM band

Round 5 certified that the room-free `Round4.BoxDesc`
(`wip/round4Comp.lean`)

    BoxDesc :  E@(ft, b+1)(Γ)  ⟶  A@(fs, b+1)(Γ, ◯D)  ⟶  A@(ft, b)(Γ, ◯D)
               (◯D ∈ S,  Γ ⊆ S,  fs ≤ ft,  1 ≤ b)

suffices for the development's one remaining `sorry`
(`Round5.boxgoal_pos_of_boxDesc`), and the round-6 prove prong is building
it at general bodies.  This file tries to REFUTE it first.

The new surface: `BoxDesc` carries NO room hypothesis, so — unlike the
round-5 screen of `cascade_boxgoal_pos`, which admitted only cells at or
above the floor `defect·(J+2) ≤ b` — the ENTIRE sub-room band is fair
game.  Every certified July refutation of the unboxed descent lived
~30× below its room; the only existing sub-room test of the BOXED form is
`Round4Probe3.boxed_survives`, a single cell against two fixed models.
This screen sweeps that band with the full battery.

§1 supplies the refutation schema `not_boxDesc_of_check`: a `checkB`
certificate at any instance satisfying the statement's four hypotheses
(`◯D ∈ S`, `Γ ⊆ S`, `fs ≤ ft`, `1 ≤ b` — there is no room to check)
refutes `BoxDesc p S` outright.  §2 is the harness — `Round5Refute`'s
`runInst` with the room-floor admissibility gate DELETED (the point of the
round) and sub-room budgets `[1, 2, 3]` as the default grid.  §3 defines
the round-6 instance families: the July `Skb`/`Sk` configurations at
budgets 1–3, ∨-carrying spaces screened hard (the prove prong's sub-task
(ii) lifts `itpA_atom_forces`'s ∨-freeness), and the round-5 families'
sub-room siblings; the escalated JB2 residual cells ride in the stage
files.

Admissibility here = the statement's own hypotheses (`◯D ∈ S`, `Γ ⊆ S`)
plus piece-closure of `S`.  Piece-closure is NOT a hypothesis of
`BoxDesc`, but every space swept is piece-closed so that a refutation
also kills any closure-carrying variant the prove prong might state.
Verdicts are countermodel-first (`settleWhy`, widened battery); an `R!`
at an admissible cell refutes `BoxDesc` and is then pinned by
`decide +kernel` in a separate file.  A clean screen is NOT a proof.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round6Refute

open PLLND.Round5Refute

/-! ## §1  The refutation schema

`Round4.BoxDesc` has exactly four hypotheses at an instance — `◯D ∈ S`,
`Γ ⊆ S`, `fs ≤ ft`, `1 ≤ b`.  No closure, no defect, no room.  So a
`checkB` certificate with the source and ambient tables as the deriving
context refutes it as soon as those four hold. -/

theorem not_boxDesc_of_check {p : String} {S : Finset PLLFormula}
    {fs ft b : Nat} {Γ : List PLLFormula} {D : PLLFormula}
    {M : FinCM} {w : Nat}
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hfs : fs ≤ ft) (hb : 1 ≤ b)
    (hchk : FinCM.checkB M w
        [itpA p S fs (b + 1) Γ D.somehow, itpE p S ft (b + 1) Γ]
        (itpA p S ft b Γ D.somehow) = true) :
    ¬ Round4.BoxDesc p S := by
  intro h
  refine FinCM.not_provable_of_check hchk (G4c.equiv_nd.mp ?_)
  exact h fs ft b Γ _ D hgS hΓS hfs hb
    (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (G4c.identity_mem (List.mem_cons_self ..))

/-! ## §2  The harness — `runInst` minus the room gate -/

def outPath6 : System.FilePath := "wip/round6refute_out.txt"

def emit6 (h : IO.FS.Handle) (s : String) : IO Unit := do
  IO.println s
  h.putStrLn s
  h.flush

def banner6 (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath6 IO.FS.Mode.append
  emit6 h s!"== {s} =="

/-- Screen one instance over its budget × fuel grid with NO room gate:
sub-room budgets are the round's target, so each line reports the band
(`SUB`/`ROOM+`) instead of skipping.  Default budgets `[1, 2, 3]` — far
below every family's floor.  Everything else (`admissible`, sizes, the
adaptive fuel grid, countermodel-first verdicts) is `Round5Refute.runInst`
verbatim; `~` lines additionally carry the searcher's reason. -/
def runInst6 (cf : Config) (cap : Nat) (i : BInst) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath6 IO.FS.Mode.append
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

/-! ### Calibration, both directions

The screen must reproduce round 4's two fixed-model verdicts through its
own machinery before the sweep is worth anything:

* the UNBOXED control `[srcU, ambB] ⊢ tgtU` must come back `R!` (the
  battery contains `Mk`'s frame — a firing screen);
* the BOXED cell `[srcB, ambB] ⊢ tgtB` ran only against `Mk` and `Mr` in
  round 4 (`boxed_survives`); here it meets the full battery for the
  first time.  `R!` on THIS line is not a calibration failure — it is a
  refutation of `BoxDesc` at the July instance, the round's jackpot. -/

def runCalib6 (cf : Config) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath6 IO.FS.Mode.append
  let t0 ← IO.monoMsNow
  let vU ← IO.lazyPure (fun _ =>
    settleWhy cf [Round4Probe3.srcU, Round4Probe3.ambB] Round4Probe3.tgtU)
  let t1 ← IO.monoMsNow
  match vU with
  | .proved _ => emit6 h s!"CALIB(unboxed r4p3): P — BROKEN SCREEN ({t1 - t0} ms)"
  | .refuted _ w _ =>
      emit6 h s!"CALIB(unboxed r4p3): R! as expected, w={w} ({t1 - t0} ms)"
  | .unknown _ =>
      emit6 h s!"CALIB(unboxed r4p3): ~ — battery MISSES the known model ({t1 - t0} ms)"
  let t2 ← IO.monoMsNow
  let vB ← IO.lazyPure (fun _ =>
    settleWhy cf [Round4Probe3.srcB, Round4Probe3.ambB] Round4Probe3.tgtB)
  let t3 ← IO.monoMsNow
  match vB with
  | .proved _ => emit6 h s!"CALIB(boxed r4p3, full battery): P ({t3 - t2} ms)"
  | .refuted M w _ =>
      emit6 h s!"CALIB(boxed r4p3, full battery): R! *** REFUTES BoxDesc \
at the July cell *** w={w} ({t3 - t2} ms) M={reprStr M}"
  | .unknown r =>
      emit6 h s!"CALIB(boxed r4p3, full battery): ~ ({t3 - t2} ms) [{r.describe}]"

/-! ## §3  The round-6 instance families -/

/-! ### J1 — THE JULY FAMILY in the sub-room band

`SkbL` (round 5's transcription of `Round4Probe3.Skb`), `gk = (◯r⊃s)⊃t`.
At `ctx = Gk` the room is `9·7 = 63`; budgets 1–3 sit ~30× below it —
exactly where every July refutation of the unboxed descent lived, and
where the room-carrying round-5 screen could not look (its floor made the
cells vacuous).  Fuel ≤ 5 keeps the tables feasible. -/

def GkL : List PLLFormula := [(pA.somehow).ifThen rA]

def subFuels : List (Nat × Nat) := [(4,4), (3,4), (1,4), (2,4), (4,5), (5,5)]
def subBudgets : List Nat := [1, 2, 3]

def j11 : BInst :=
  { name := "J-JULY ctx=Gk d=9 D=gk", Sl := SkbL
  , ctx := GkL, body := gkL, budgets := subBudgets, fuels := subFuels }
def j12 : BInst :=
  { name := "J-JULY ctx=Gk d=9 D=r (atom)", Sl := SkbL
  , ctx := GkL, body := rA, budgets := subBudgets, fuels := subFuels }
def j13 : BInst :=
  { name := "J-JULY ctx=Gk d=9 D=p (elim var)", Sl := SkbL
  , ctx := GkL, body := pA, budgets := subBudgets, fuels := subFuels }
def j14 : BInst :=
  { name := "J-JULY/miss-r d=1 D=gk", Sl := SkbL
  , ctx := without SkbL [rA], body := gkL, budgets := subBudgets, fuels := subFuels }
def j15 : BInst :=
  { name := "J-JULY/miss-s d=1 D=gk", Sl := SkbL
  , ctx := without SkbL [sA], body := gkL, budgets := subBudgets, fuels := subFuels }
def j16 : BInst :=
  { name := "J-JULY/miss-t d=1 D=gk", Sl := SkbL
  , ctx := without SkbL [tA], body := gkL, budgets := subBudgets, fuels := subFuels }
def j17 : BInst :=
  { name := "J-JULY/miss-r,s d=2 D=gk", Sl := SkbL
  , ctx := without SkbL [rA, sA], body := gkL, budgets := subBudgets, fuels := subFuels }
def j18 : BInst :=
  { name := "J-JULY/miss-r,s,t d=3 D=gk", Sl := SkbL
  , ctx := without SkbL [rA, sA, tA], body := gkL, budgets := subBudgets, fuels := subFuels }
def j19 : BInst :=
  { name := "J-JULY/miss-s,t d=2 D=gk", Sl := SkbL
  , ctx := without SkbL [sA, tA], body := gkL, budgets := subBudgets, fuels := subFuels }

/-- Plain `Sk` (no `◯gk`): bodies `r`, `p` are the boxed members it has. -/
def SkL : List PLLFormula :=
  [(pA.somehow).ifThen rA, pA.somehow, pA, rA,
   gkL, (rA.somehow).ifThen sA, rA.somehow, sA, tA]
def j1A : BInst :=
  { name := "J-JULY plain-Sk ctx=Gk d=8 D=r", Sl := SkL
  , ctx := GkL, body := rA, budgets := subBudgets, fuels := subFuels }
def j1B : BInst :=
  { name := "J-JULY plain-Sk ctx=Gk d=8 D=p", Sl := SkL
  , ctx := GkL, body := pA, budgets := subBudgets, fuels := subFuels }

/-! ### J2 — ∨-spaces, screened hard

The prove prong's sub-task (ii) lifts `itpA_atom_forces`'s ∨-freeness, so
the ∨-apparatus is the least exercised.  Beyond round 5's `S4` family
(swept sub-room in the stages): the ∨-body one box up, an ∨-space with a
live jump gate, ∨ inside a jump body, and ∨ as a box-gate consequent. -/

def orB6 : PLLFormula := eA.or fA

/-- `D = ◯(e∨f)`: needs `◯◯(e∨f) ∈ S`. -/
def S4b : List PLLFormula :=
  [orB6.somehow.somehow, orB6.somehow, orB6, eA, fA]
def j21 : BInst :=
  { name := "OR-BOX/miss-e D=◯(e∨f)", Sl := S4b
  , ctx := without S4b [eA], body := orB6.somehow }
def j22 : BInst :=
  { name := "OR-BOX/miss-e,f d=2 D=◯(e∨f)", Sl := S4b
  , ctx := without S4b [eA, fA], body := orB6.somehow }

/-- ∨-space with a live jump gate `(e⊃f)⊃c`. -/
def SJ : List PLLFormula :=
  [orB6.somehow, orB6, eA, fA, (eA.ifThen fA).ifThen cA, eA.ifThen fA, cA]
def j23 : BInst :=
  { name := "OR-JUMP/miss-c D=e∨f (J=1)", Sl := SJ
  , ctx := without SJ [cA], body := orB6 }
def j24 : BInst :=
  { name := "OR-JUMP/miss-f,c d=2 D=e∨f", Sl := SJ
  , ctx := without SJ [fA, cA], body := orB6 }

/-- ∨ inside the jump body: `jOr = ((e∨f)⊃b)⊃c`, boxed in `S`. -/
def jOr : PLLFormula := ((eA.or fA).ifThen bA).ifThen cA
def SOJ : List PLLFormula :=
  [jOr.somehow, jOr, (eA.or fA).ifThen bA, eA.or fA, eA, fA, bA, cA]
def j25 : BInst :=
  { name := "OR-IN-JUMP/miss-c D=((e∨f)⊃b)⊃c", Sl := SOJ
  , ctx := without SOJ [cA], body := jOr }
def j26 : BInst :=
  { name := "OR-IN-JUMP/miss-b,c d=2", Sl := SOJ
  , ctx := without SOJ [bA, cA], body := jOr }

/-- ∨ as the consequent of a `⊃◯` gate: `◯e ⊃ (f∨c)`. -/
def SOG : List PLLFormula :=
  [(eA.somehow).ifThen (fA.or cA), eA.somehow, eA, fA.or cA, fA, cA]
def j27 : BInst :=
  { name := "OR-GATE/miss-f∨c D=e", Sl := SOG
  , ctx := without SOG [fA.or cA], body := eA }
def j28 : BInst :=
  { name := "OR-GATE/miss-f,c,f∨c d=3 D=e", Sl := SOG
  , ctx := without SOG [fA, cA, fA.or cA], body := eA }

end Round6Refute
end PLLND

/-! ### Axiom audit -/

/--
info: 'PLLND.Round6Refute.not_boxDesc_of_check' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms PLLND.Round6Refute.not_boxDesc_of_check
