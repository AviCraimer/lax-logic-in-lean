import absorb_base
import round4probe3
import wip.towerkit

/-!
# ROUND 5, REFUTE prong — `cascade_boxgoal_pos` hunted inside its own room

`wip/absorb_base.lean:2269` has the tower's single `sorry`:

    cascade_boxgoal_pos :
      piece-closure of S → ◯D ∈ S → Γ ⊆ S → fs ≤ ft → 1 ≤ b →
      1 ≤ defect S Γ → defect S Γ · (|jumpGoals S| + 2) ≤ b →
      Δ ⊢ E@(ft, b+1)(Γ) → Δ ⊢ A@(fs, b+1)(Γ, ◯D) →
      Δ ⊢ A@(ft, b)(Γ, ◯D)

§1 states it as a proposition `BoxGoalPos p S` (universally quantified in
everything but the eliminated variable and the space, closure hypotheses as
arguments so a refutation refutes the whole implication) and supplies the
refutation schema `not_boxGoalPos_of_check`: a `FinCM.checkB` certificate at
an instance satisfying EVERY hypothesis — the room included — refutes the
statement outright.  This is `RoomPin.not_roomDescent_of_check`'s pattern
specialised to the `◯`-goal form.

§2 is the screening harness.  The coverage design point: a `◯D` goal is
budget-gated by its OWN goal clause (`itpA`'s `.somehow` goal arm reads `b`
at every budget, and the truncation disjunct with it), so — unlike the
July general-goal descents, where a live gate forced `|jumpGoals S| ≥ 1`
and hence room ≥ 3 — the box-goal statement has a live band already at
`J = 0`, floor `b = 2·defect`.  That corner (and the whole at-the-room
band) has never been screened: every July refutation sat ~30× below its
room, and the round-4 compound-body screen ran the room-FREE `BoxDesc` at
`b ≤ 3` over `J = 2` spaces (also below the room).  The families aim at
the prove prong's soft spots (PROGRESS §60(d)): jump-shaped bodies,
nested `◯`, `∨`-bodies, wide fuel gaps `fs < ft`, defect ≥ 2, room-floor
exactness, and the July `Sk` configuration at its own room floor
(`b = 63` is feasible: fuel ≤ 5 bounds the tables, not the budget).

Verdicts are countermodel-first (`settleWhy`, widened battery, positive
stage budget-capped); an `R!` at an admissible cell is a refutation of
the target statement and is then pinned by `decide +kernel` in a
separate file.  A clean screen is NOT a proof.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND
namespace Round5Refute

/-! ## §1  The target as a proposition, and the refutation schema -/

/-- `cascade_boxgoal_pos` (`wip/absorb_base.lean:2269`), transcribed
verbatim at fixed `(p, S)`: closure hypotheses as arguments, every other
hypothesis kept — the room included.  If the `sorry` were provable, this
proposition would hold for every `p` and `S`; a single concrete
`¬ BoxGoalPos p S` therefore refutes it. -/
def BoxGoalPos (p : String) (S : Finset PLLFormula) : Prop :=
  (∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S) →
  (∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S) →
  ∀ (fs ft b : Nat) (Γ Δ : List PLLFormula) (D : PLLFormula),
    D.somehow ∈ S → (∀ X ∈ Γ, X ∈ S) →
    fs ≤ ft → 1 ≤ b → 1 ≤ defect S Γ →
    defect S Γ * ((jumpGoals S).card + 2) ≤ b →
    G4c Δ (itpE p S ft (b + 1) Γ) →
    G4c Δ (itpA p S fs (b + 1) Γ D.somehow) →
    G4c Δ (itpA p S ft b Γ D.somehow)

/-- **The refutation schema.**  A `checkB` certificate — source and ambient
tables at `b+1` as the deriving context, the target table at `b` refuted in
the model — kills `BoxGoalPos p S`, PROVIDED the instance satisfies every
hypothesis of the statement.  All side conditions are `decide`able at a
concrete instance. -/
theorem not_boxGoalPos_of_check {p : String} {S : Finset PLLFormula}
    {fs ft b : Nat} {Γ : List PLLFormula} {D : PLLFormula}
    {M : FinCM} {w : Nat}
    (hand : ∀ {A B : PLLFormula}, A.and B ∈ S → A ∈ S ∧ B ∈ S)
    (hor : ∀ {A B : PLLFormula}, A.or B ∈ S → A ∈ S ∧ B ∈ S)
    (himp : ∀ {A B : PLLFormula}, A.ifThen B ∈ S → A ∈ S ∧ B ∈ S)
    (hsome : ∀ {A : PLLFormula}, A.somehow ∈ S → A ∈ S)
    (hgS : D.somehow ∈ S) (hΓS : ∀ X ∈ Γ, X ∈ S)
    (hfs : fs ≤ ft) (hb : 1 ≤ b) (hd1 : 1 ≤ defect S Γ)
    (hroom : defect S Γ * ((jumpGoals S).card + 2) ≤ b)
    (hchk : FinCM.checkB M w
        [itpA p S fs (b + 1) Γ D.somehow, itpE p S ft (b + 1) Γ]
        (itpA p S ft b Γ D.somehow) = true) :
    ¬ BoxGoalPos p S := by
  intro h
  refine FinCM.not_provable_of_check hchk (G4c.equiv_nd.mp ?_)
  exact h hand hor himp hsome fs ft b Γ _ D hgS hΓS hfs hb hd1 hroom
    (G4c.identity_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (G4c.identity_mem (List.mem_cons_self ..))

/-! ## §2  The screening harness -/

/-- One screening instance: space (as a list), context, box body. -/
structure BInst where
  name : String
  Sl : List PLLFormula
  ctx : List PLLFormula
  body : PLLFormula
  /-- Budgets to screen; `[]` means `[room, room + 1]`. -/
  budgets : List Nat := []
  /-- `(fs, ft)` pairs; `[]` means the adaptive grid
  `[(b+2,b+2), (b+1,b+2), (1,b+2), (2,b+3), (b+3,b+3)]`. -/
  fuels : List (Nat × Nat) := []

def BInst.S (i : BInst) : Finset PLLFormula := i.Sl.toFinset

/-- Computable piece-closure of the space list (implies the four closure
hypotheses of the statement for `Sl.toFinset`). -/
def pieceClosedB (Sl : List PLLFormula) : Bool :=
  Sl.all (fun F => match F with
    | .and A B => Sl.contains A && Sl.contains B
    | .or A B => Sl.contains A && Sl.contains B
    | .ifThen A B => Sl.contains A && Sl.contains B
    | .somehow A => Sl.contains A
    | _ => true)

def admissible (i : BInst) : Bool :=
  pieceClosedB i.Sl && i.Sl.contains i.body.somehow
    && i.ctx.all (fun F => i.Sl.contains F)

/-! Gate-liveness instruments (transcribed from `wip/roomhunt.lean` §1,
restricted to what the `◯`-goal screen needs). -/

def liveJumpGates (Sl ctx : List PLLFormula) : Nat :=
  (ctx.filter (fun F => match F with
    | .ifThen (.ifThen _ B) E =>
        !(ctx.contains E) && Sl.contains E && ctx.contains (B.ifThen E)
          && Sl.contains F
    | _ => false)).length

def liveBoxGates (Sl ctx : List PLLFormula) : Nat :=
  (ctx.filter (fun F => match F with
    | .ifThen (.somehow _) B =>
        !(ctx.contains B) && Sl.contains B && Sl.contains F
    | _ => false)).length

def liveBoxEnv (Sl ctx : List PLLFormula) : Nat :=
  (ctx.filter (fun F => match F with
    | .somehow x => !(ctx.contains x) && Sl.contains x
    | _ => false)).length

/-! The sequent of a cell. -/

def pv : String := "p"

def srcOf (i : BInst) (fs b : Nat) : PLLFormula :=
  itpA pv i.S fs (b + 1) i.ctx i.body.somehow

def ambOf (i : BInst) (ft b : Nat) : PLLFormula :=
  itpE pv i.S ft (b + 1) i.ctx

def tgtOf (i : BInst) (ft b : Nat) : PLLFormula :=
  itpA pv i.S ft b i.ctx i.body.somehow

/-! Frames: the round-4 probe battery plus the ladder shapes of
`wip/roomhunt.lean` (rigid chains, infallible variants, rigid fork). -/

def xFrames : List Frame :=
  [ ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨2, [(0,1)], [], []⟩
  , ⟨2, [(0,1)], [], [1]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [], [2]⟩
  , ⟨3, [(0,1),(0,2)], [], []⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [], []⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3]⟩
  , ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩ ]

/-- Pass-1 configuration: countermodel-first over the widened battery,
positive stage capped, closure emitter off. -/
def cfg1 : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 400
  , emitClosureCap := 0 }

/-- A deeper positive stage for cells worth settling two-sidedly. -/
def cfg2 : Config :=
  { frames := xFrames ++ defaultFrames
  , findBudget := some 20000
  , emitClosureCap := 0 }

/-! Durable output: every line is appended (and flushed) to
`wip/round5refute_out.txt`, so a killed elaboration loses nothing. -/

def outPath : System.FilePath := "wip/round5refute_out.txt"

def emit (h : IO.FS.Handle) (s : String) : IO Unit := do
  IO.println s
  h.putStrLn s
  h.flush

def banner (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
  emit h s!"== {s} =="

/-- Screen one instance: admissibility, room, then the budget × fuel grid,
countermodel-first, sizes guarded by `cap`.  An `R!` prints the model for
the kernel pin. -/
def runInst (cf : Config) (cap : Nat) (i : BInst) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
  let S := i.S
  let d := defect S i.ctx
  let J := (jumpGoals S).card
  let room := d * (J + 2)
  emit h s!"{i.name}: |S|={i.Sl.length} d={d} J={J} room={room} \
adm={admissible i} gates(jump/box/env)=\
{liveJumpGates i.Sl i.ctx}/{liveBoxGates i.Sl i.ctx}/{liveBoxEnv i.Sl i.ctx}"
  if !(admissible i) || d == 0 then
    emit h "  INADMISSIBLE — skipped"
  else
    let bs := if i.budgets.isEmpty then [room, room + 1] else i.budgets
    for b in bs do
      if b < room then
        emit h s!"  b={b}: BELOW ROOM — vacuous, skipped"
      else
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
              emit h s!"  fs={fs} ft={ft} b={b}: SKIP |s+a+t|={nsz} > {cap}"
            else
              let act ← IO.lazyPure (fun _ => tgtOf i ft (b + 1) != tgt)
              let v ← IO.lazyPure (fun _ => settleWhy cf [src, amb] tgt)
              let t1 ← IO.monoMsNow
              match v with
              | .proved _ =>
                  emit h s!"  fs={fs} ft={ft} b={b}: P  act={act} \
|s+a+t|={nsz} ({t1 - t0} ms)"
              | .refuted M w _ =>
                  emit h s!"  fs={fs} ft={ft} b={b}: R! *** REFUTES *** \
act={act} |s+a+t|={nsz} ({t1 - t0} ms) w={w} M={reprStr M}"
              | .unknown _ =>
                  emit h s!"  fs={fs} ft={ft} b={b}: ~  act={act} \
|s+a+t|={nsz} ({t1 - t0} ms)"

/-- Live-fire calibration: the harness's own machinery on round 4's
UNBOXED control (`Round4Probe3.srcU/ambB/tgtU`), which is
`checkB`-certified refutable.  A screen that cannot reproduce `R!` here
reports nothing when it prints `~`. -/
def runCalib (cf : Config) : IO Unit := do
  let h ← IO.FS.Handle.mk outPath IO.FS.Mode.append
  let t0 ← IO.monoMsNow
  let v ← IO.lazyPure (fun _ =>
    settleWhy cf [Round4Probe3.srcU, Round4Probe3.ambB] Round4Probe3.tgtU)
  let t1 ← IO.monoMsNow
  match v with
  | .proved _ => emit h s!"CALIB(unboxed r4p3): P — BROKEN SCREEN ({t1 - t0} ms)"
  | .refuted _ w _ => emit h s!"CALIB(unboxed r4p3): R! as expected, w={w} ({t1 - t0} ms)"
  | .unknown _ => emit h s!"CALIB(unboxed r4p3): ~ — battery MISSES the known model ({t1 - t0} ms)"

/-! ## §3  The instance families -/

def aA : PLLFormula := prop "a"
def bA : PLLFormula := prop "b"
def cA : PLLFormula := prop "c"
def eA : PLLFormula := prop "e"
def fA : PLLFormula := prop "f"
def pA : PLLFormula := prop "p"
def rA : PLLFormula := prop "r"
def sA : PLLFormula := prop "s"
def tA : PLLFormula := prop "t"

def without (Sl xs : List PLLFormula) : List PLLFormula :=
  Sl.filter (fun F => !(xs.contains F))

/-! ### F1 — jump-shaped body `D = (a⊃b)⊃c` (`J = 1`, room `3·d`) -/

def jB : PLLFormula := (aA.ifThen bA).ifThen cA
def S1 : List PLLFormula := [jB.somehow, jB, aA.ifThen bA, bA.ifThen cA, aA, bA, cA]
def i11 : BInst := { name := "JB/miss-c    D=(a⊃b)⊃c", Sl := S1, ctx := without S1 [cA], body := jB }
def i12 : BInst := { name := "JB/miss-D    D=(a⊃b)⊃c", Sl := S1, ctx := without S1 [jB], body := jB }
def i13 : BInst := { name := "JB/miss-boxD D=(a⊃b)⊃c", Sl := S1, ctx := without S1 [jB.somehow], body := jB }
def jBp : PLLFormula := (pA.ifThen bA).ifThen cA
def S1p : List PLLFormula := [jBp.somehow, jBp, pA.ifThen bA, bA.ifThen cA, pA, bA, cA]
def i14 : BInst := { name := "JBp/miss-c   D=(p⊃b)⊃c", Sl := S1p, ctx := without S1p [cA], body := jBp }
def i15 : BInst :=
  { name := "JB/miss-b,c  d=2", Sl := S1, ctx := without S1 [bA, cA], body := jB
  , fuels := [(8,8), (7,8), (1,8), (2,9)] }

/-! ### F2 — jump body one `◯` down: `D = ◯((a⊃b)⊃c)` (`J = 1`) -/

def S2 : List PLLFormula :=
  [jB.somehow.somehow, jB.somehow, jB, aA.ifThen bA, bA.ifThen cA, aA, bA, cA]
def i21 : BInst := { name := "JB2/miss-c   D=◯((a⊃b)⊃c)", Sl := S2, ctx := without S2 [cA], body := jB.somehow }
def i22 : BInst := { name := "JB2/miss-◯E  D=◯((a⊃b)⊃c)", Sl := S2, ctx := without S2 [jB.somehow], body := jB.somehow }

/-! ### F3 — nested `◯`, `J = 0` (room `2·d` — the absolute floor) -/

def S3 : List PLLFormula := [eA.somehow.somehow, eA.somehow, eA]
def i31 : BInst := { name := "BB/miss-e    D=◯e", Sl := S3, ctx := without S3 [eA], body := eA.somehow }
def i32 : BInst := { name := "BB/miss-◯e   D=◯e", Sl := S3, ctx := without S3 [eA.somehow], body := eA.somehow }
def i33 : BInst := { name := "BB/miss-◯◯e  D=◯e", Sl := S3, ctx := without S3 [eA.somehow.somehow], body := eA.somehow }
def S3p : List PLLFormula := [pA.somehow.somehow, pA.somehow, pA]
def i34 : BInst := { name := "BBp/miss-p   D=◯p", Sl := S3p, ctx := without S3p [pA], body := pA.somehow }
def S3a : List PLLFormula := [eA.somehow, eA]
def i35 : BInst := { name := "ATOM/miss-e  D=e (control)", Sl := S3a, ctx := without S3a [eA], body := eA }
def S3ap : List PLLFormula := [pA.somehow, pA]
def i36 : BInst := { name := "ATOMp/miss-p D=p (control)", Sl := S3ap, ctx := without S3ap [pA], body := pA }

/-! ### F4 — `∨`-carrying body (`J = 0`) -/

def orB : PLLFormula := eA.or fA
def S4 : List PLLFormula := [orB.somehow, orB, eA, fA]
def i41 : BInst := { name := "OR/miss-e    D=e∨f", Sl := S4, ctx := without S4 [eA], body := orB }
def i42 : BInst := { name := "OR/miss-e,f  d=2 (or-growth live)", Sl := S4, ctx := without S4 [eA, fA], body := orB }
def i43 : BInst := { name := "OR/miss-D    D=e∨f", Sl := S4, ctx := without S4 [orB], body := orB }

/-! ### F5 — `⊃◯` gate over the body (`J = 2`, room `4·d`) -/

def S5a : List PLLFormula := [(aA.somehow).ifThen cA, aA.somehow, aA, cA]
def i51 : BInst := { name := "GATE/miss-c  D=a, ◯a⊃c", Sl := S5a, ctx := without S5a [cA], body := aA }
def impB : PLLFormula := aA.ifThen bA
def S5i : List PLLFormula := [(impB.somehow).ifThen cA, impB.somehow, impB, aA, bA, cA]
def i52 : BInst := { name := "GATE/miss-c  D=a⊃b, ◯(a⊃b)⊃c", Sl := S5i, ctx := without S5i [cA], body := impB }
def i53 : BInst :=
  { name := "GATE/miss-a,c d=2", Sl := S5a, ctx := without S5a [aA, cA], body := aA
  , fuels := [(10,10), (9,10), (1,10), (2,11)] }

/-! ### F6 — defect 2 at `J = 0` (two live box-env growths) -/

def S6 : List PLLFormula := [eA.somehow.somehow, eA.somehow, eA, fA.somehow, fA]
def i61 : BInst := { name := "BB2/miss-e,f d=2 J=0", Sl := S6, ctx := without S6 [eA, fA], body := eA.somehow }

/-! ### F7 — the July configuration at its OWN room

`Skb = insert ◯gk Sk` (round 4's screen space), `gk = (◯r⊃s)⊃t`.  At
`ctx = Gk` the room is `9·7 = 63`; fuel ≤ 5 keeps the tables small, so
the cells are feasible — the first time this family is screened at a
budget its room admits.  The saturated variants sit at `d = 1`,
room `7`. -/

def gkL : PLLFormula := ((rA.somehow).ifThen sA).ifThen tA
def SkbL : List PLLFormula :=
  [gkL.somehow, (pA.somehow).ifThen rA, pA.somehow, pA, rA,
   gkL, (rA.somehow).ifThen sA, rA.somehow, sA, tA]
def julyFuels : List (Nat × Nat) := [(4,4), (3,4), (1,4), (4,5), (5,5)]
def i71 : BInst :=
  { name := "JULY@room    ctx=Gk d=9 D=gk", Sl := SkbL
  , ctx := [(pA.somehow).ifThen rA], body := gkL, fuels := julyFuels }
def i72 : BInst :=
  { name := "JULY-sat/miss-r D=gk", Sl := SkbL
  , ctx := without SkbL [rA], body := gkL, fuels := julyFuels }
def i73 : BInst :=
  { name := "JULY-sat/miss-s D=gk", Sl := SkbL
  , ctx := without SkbL [sA], body := gkL, fuels := julyFuels }
def i74 : BInst :=
  { name := "JULY-sat/miss-r D=r (atom)", Sl := SkbL
  , ctx := without SkbL [rA], body := rA, fuels := julyFuels }
def i75 : BInst :=
  { name := "JULY-sat/miss-r D=p (elim var)", Sl := SkbL
  , ctx := without SkbL [rA], body := pA, fuels := julyFuels }

end Round5Refute
end PLLND

