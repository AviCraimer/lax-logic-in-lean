import frontier

/-!
# ROUND 8, PHASE 1 — the goal-row residue candidates, replayed over the corpus

PROGRESS §66(h) names the round-8 residue: `Round7.CompProd`'s goal-row case
at jump-shaped unboxed bodies — absorb the source table's goal row

    Gsrc := ◯( E@(f, b−1)(Γ) ⊃ A@(f, b)(Γ, D) )        (f = ft − 1)

into the target table at `c < b` from the ambient alone, `D` compound
unboxed, WITHOUT the pointwise descent (kernel-refuted at every ambient
elevation, `Round7Pin.goalrow_landing_refuted_elev1/_elev2`) and WITHOUT a
budget-priced side condition (`Round6.no_self_financed_nest`).  Before any
build is scoped (§65 standing rule), the candidate statements are screened
over the corpus.

## The candidates (all ROOM-FREE, all two-premise)

**GR-W** (the residue verbatim — goal row to the full target table):

    Δ ⊢ E@(ft, b+1)(Γ)  →  Δ ⊢ Gsrc  →  Δ ⊢ A@(ft, c)(Γ, ◯D)     1 ≤ c < b

The walk position also holds the introduced guard `E@(ft, c)(Γ)`, but the
guard is ambient-derivable (downward budget monotonicity), so the
two-premise form screens the same statement.

**GR-X** (the committed-goal-clause route — the walk commits the target to
its OWN goal disjunct, exact inner slots):

    Δ ⊢ E@(ft, b+1)(Γ)  →  Δ ⊢ Gsrc  →
    Δ ⊢ ◯( E@(f, c−1)(Γ) ⊃ A@(f, c)(Γ, D) )

Round 7's passes C/D screened the TABLE-premise, fuel-`ft` weakening of
this; GR-X is the walk's actual position (row premise, inner fuel) and is
strictly more refutable.  A hit here redirects the absorption to non-goal
target disjuncts; quiet supports the committed route.

**CP-P** (`CompProd` proper at the cell's OWN body — G/H screened it only at
the γ-clause antecedent body):

    Δ ⊢ E@(ft, b+1)(Γ)  →  Δ ⊢ ◯( E@(fs, b)(Γ) ⊃ A@(fs, b)(Γ, ◯D) )  →
    Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c)(Γ, ◯D) )

A hit at admissible parameters refutes `CompProd` and hence, by
`Round7.not_boxDesc_of_not_compProd`, kills `Round4.BoxDesc` and the whole
room-free route — a campaign-level result.

**GR-E** (the γ-env-row route: land the goal row in the target's γ-head env
disjunct instead; γ-cells only, `◯A₁ ⊃ B₀ ∈ Γ`, `B₀ ∈ S ∖ Γ`):

    Δ ⊢ E@(ft, b+1)(Γ)  →  Δ ⊢ Gsrc  →
    Δ ⊢ ( ◯( E@(f, c−1)(Γ) ⊃ A@(f, c−1)(Γ, ◯A₁) ) ) ∧ A@(f, c)(B₀::Γ, ◯D)

Expected the most refutable (the γ-head component must come from the
ambient and the goal row alone); a clean run here would open the env route.

**Controls** (live-fire calibration at THIS premise pair): `GR-W` and the
component production at `c = 0`, where round 7's pass Z certified 344
refutable instances from the weaker table premise.

## The passes

Over every corpus record with `why=run` (zero generation cost; skipped
records agree by construction, exactly as `replayUnboxed`):

* `Z0` control: `[Gsrc, amb] ⊢ comp2 0`             — expect hits
* `Z1` control: `[Gsrc, amb] ⊢ tgt(0)`              — expect hits
* `P1` CP-P:    `[compS, amb] ⊢ comp2 (b−1)`        (b ≥ 2)
* `P2` CP-P:    `[compS, amb] ⊢ comp2 1`            (b ≥ 2)
* `W1` GR-W:    `[Gsrc, amb] ⊢ tgt(b−1)`            (b ≥ 2)
* `W2` GR-W:    `[Gsrc, amb] ⊢ tgt(1)`              (b ≥ 2)
* `X1` GR-X:    `[Gsrc, amb] ⊢ gclause(b−1)`        (b ≥ 2)
* `X2` GR-X:    `[Gsrc, amb] ⊢ gclause(1)`          (b ≥ 2)
* `E1` GR-E:    `[Gsrc, amb] ⊢ genv(b−1)`           (γ-cells, b ≥ 2)

where `comp2 c = ◯(E@(ft,c)(Γ) ⊃ A@(ft,c)(Γ,◯D))` (round 7's shape),
`compS = ◯(E@(fs,b)(Γ) ⊃ A@(fs,b)(Γ,◯D))`,
`gclause c = ◯(E@(f,c−1)(Γ) ⊃ A@(f,c)(Γ,D))`, `tgt c = A@(ft,c)(Γ,◯D)`.

Durable output: `wip/frontier_g8.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g8Ledger : Ledger := { path := "wip/frontier_g8.txt" }

/-- Round 7's `comp2` shape, cloned locally (`frontier_g7.lean` is a
recorded artifact, not an import): the boxed component at the cell's own
goal body, both slots at `(ft, cb)`. -/
def Cell.comp2T (c : Cell) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S c.ft cb c.ctx).ifThen
    (itpA pv c.S c.ft cb c.ctx c.body.somehow)).somehow

/-- The source table's goal row at the reference fuel: the row the walk
holds in `CompProd`'s goal-row case (`f = ft − 1`; the fired value was
lifted to fuel `ft`, so its rows sit at inner fuel `ft − 1`). -/
def Cell.gsrc (c : Cell) : PLLFormula :=
  ((itpE pv c.S (c.ft - 1) (c.b - 1) c.ctx).ifThen
    (itpA pv c.S (c.ft - 1) c.b c.ctx c.body)).somehow

/-- The target table at budget `cb` (the GR-W conclusion). -/
def Cell.tgtAt (c : Cell) (cb : Nat) : PLLFormula :=
  itpA pv c.S c.ft cb c.ctx c.body.somehow

/-- The target's own goal disjunct at budget `cb = c`, exact inner slots
(guard `c−1`, value `c`, both at fuel `ft − 1`, body UNBOXED). -/
def Cell.gclause (c : Cell) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S (c.ft - 1) (cb - 1) c.ctx).ifThen
    (itpA pv c.S (c.ft - 1) cb c.ctx c.body)).somehow

/-- `CompProd`'s own premise component: slots at `(fs, b)`. -/
def Cell.compS (c : Cell) : PLLFormula :=
  ((itpE pv c.S c.fs c.b c.ctx).ifThen
    (itpA pv c.S c.fs c.b c.ctx c.body.somehow)).somehow

/-- The cell's first live γ-clause as the PAIR `(A₁, B₀)`, if any. -/
def Cell.liveGammaPair? (c : Cell) : Option (PLLFormula × PLLFormula) :=
  match c.ctx.find? (fun F => match F with
    | .ifThen (.somehow _) B => !(c.ctx.contains B) && c.Sl.contains B
    | _ => false) with
  | some (.ifThen (.somehow X) B) => some (X, B)
  | _ => none

/-- The target's γ-head env disjunct at budget `cb`: boxed head at
`(f, cb−1)`, grown second component at `(f, cb)`. -/
def Cell.genv (c : Cell) (ant hd : PLLFormula) (cb : Nat) : PLLFormula :=
  (((itpE pv c.S (c.ft - 1) (cb - 1) c.ctx).ifThen
      (itpA pv c.S (c.ft - 1) (cb - 1) c.ctx ant.somehow)).somehow).and
    (itpA pv c.S (c.ft - 1) cb (hd :: c.ctx) c.body.somehow)

/-- One replay pass (the round-7 `passOn`, re-pointed at this round's
ledger): premises and target from the cell, size-capped like the campaign,
countermodel-only.  `none` from `mk` = pass not applicable to this cell
(agree with the recorded verdict by construction). -/
def passOnG8 (tag : String) (cap : Nat)
    (mk : Cell → Option (List PLLFormula × PLLFormula)) : IO Unit := do
  let r ← replay corpus regen (fun c rc => do
    if (rc.col? "why").getD "" != "run" then pure { triage := rc.triage }
    else match mk c with
    | none => pure { triage := rc.triage }
    | some (prems, tgt) => do
      let n ← IO.lazyPure (fun _ =>
        (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
      if n > cap then pure { triage := rc.triage }
      else do
        let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
        match v with
        | some ⟨M, w, _⟩ =>
            pure { triage := .hit, cert := s!"w={w} M={reprStr M}" }
        | none => pure { triage := .quiet })
  g8Ledger.comment s!"PASS {tag}: {r.render}"
  for n in r.notes.take 40 do g8Ledger.comment s!"  {n}"

def passZ0 (cap : Nat) : IO Unit :=
  passOnG8 "Z0 (control: goal row to comp2 0, expect hits)" cap (fun c =>
    some ([c.gsrc, c.amb], c.comp2T 0))

def passZ1 (cap : Nat) : IO Unit :=
  passOnG8 "Z1 (control: goal row to tgt 0, expect hits)" cap (fun c =>
    some ([c.gsrc, c.amb], c.tgtAt 0))

def passP1 (cap : Nat) : IO Unit :=
  passOnG8 "P1 (CP-P: CompProd at own body, c=b-1)" cap (fun c =>
    if c.b < 2 then none else some ([c.compS, c.amb], c.comp2T (c.b - 1)))

def passP2 (cap : Nat) : IO Unit :=
  passOnG8 "P2 (CP-P: CompProd at own body, c=1)" cap (fun c =>
    if c.b < 2 then none else some ([c.compS, c.amb], c.comp2T 1))

def passW1 (cap : Nat) : IO Unit :=
  passOnG8 "W1 (GR-W: goal row to target table, c=b-1)" cap (fun c =>
    if c.b < 2 then none else some ([c.gsrc, c.amb], c.tgtAt (c.b - 1)))

def passW2 (cap : Nat) : IO Unit :=
  passOnG8 "W2 (GR-W: goal row to target table, c=1)" cap (fun c =>
    if c.b < 2 then none else some ([c.gsrc, c.amb], c.tgtAt 1))

def passX1 (cap : Nat) : IO Unit :=
  passOnG8 "X1 (GR-X: goal row to committed goal clause, c=b-1)" cap (fun c =>
    if c.b < 2 then none else some ([c.gsrc, c.amb], c.gclause (c.b - 1)))

def passX2 (cap : Nat) : IO Unit :=
  passOnG8 "X2 (GR-X: goal row to committed goal clause, c=1)" cap (fun c =>
    if c.b < 2 then none else some ([c.gsrc, c.amb], c.gclause 1))

def passE1 (cap : Nat) : IO Unit :=
  passOnG8 "E1 (GR-E: goal row to gamma env disjunct, c=b-1)" cap (fun c =>
    match c.liveGammaPair? with
    | none => none
    | some (ant, hd) =>
        if c.b < 2 then none
        else some ([c.gsrc, c.amb], c.genv ant hd (c.b - 1)))

def g8All : IO Unit := do
  let ok ← calibrate
  if !ok then
    g8Ledger.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    g8Ledger.comment "=== round-8 goal-row candidate replay ==="
    passZ0 40000
    passZ1 40000
    passP1 40000
    passP2 40000
    passW1 40000
    passW2 40000
    passX1 40000
    passX2 40000
    passE1 40000
    g8Ledger.comment "=== round-8 replay done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g8All
