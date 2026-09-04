import frontier

/-!
# ROUND 7, PHASE 1 — the guard-stack candidates, replayed over the corpus

PROGRESS §63(e) fork (1): at the γ-row landing of the `◯`-goal descent,
instead of financing a budget descent, produce the needed boxed γ-head
component directly.  Before any build is scoped (§65 standing rule), the
candidate statements are screened over the 948-cell corpus.

## The candidates (all ROOM-FREE — any room demand at the landing re-enters
`no_self_financed_nest` territory at depth ≥ 3)

**C-PROD** (the build target; the γ-row landing obligation as a two-premise
sequent).  For a live γ-clause `◯A₁ ⊃ B₀ ∈ Γ` (`B₀ ∈ S ∖ Γ`), from the
ambient and the source's own γ-head component,

    Δ ⊢ E@(ft, b+1)(Γ)                        (the ambient)
    Δ ⊢ ◯( E@(fs, b)(Γ) ⊃ A@(fs, b)(Γ, ◯A₁) )  (the held γ-head component)
    ────────────────────────────────────────────  for 1 ≤ c ≤ b
    Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c)(Γ, ◯A₁) )

**C-TBL** (the same production from the full source table — what the
statement's own premises supply):

    Δ ⊢ E@(ft, b+1)(Γ) → Δ ⊢ A@(fs, b+1)(Γ, ◯D) →
    Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c)(Γ, ◯D) )      for 1 ≤ c ≤ b

Note C-TBL is implied by iterating the room-free `Round4.BoxDesc`, so a hit
here refutes iterated `BoxDesc` — a stronger negative than any on record.

**C-GOAL** (the committed goal clause: `boxSnd_tight`'s conclusion at a
COMPOUND body — the "fire"-horn extension; expected FALSE at compound `D`):

    Δ ⊢ E@(ft, b+1)(Γ) → Δ ⊢ A@(fs, b+1)(Γ, ◯D) →
    Δ ⊢ ◯( E@(ft, c)(Γ) ⊃ A@(ft, c+1)(Γ, D) )

At `c = b−1` this is the target's own goal disjunct, so a derivation of it
implies the target outright; a hit pins WHY the fire horn cannot extend.

**Control** (expected refutable — the live-fire calibration of the pass):
C-TBL at `c = 0`.  Hand-check at the `S3` cell: `A@(ft, 0)(Γ3, ◯D)` has an
empty disjunct table (`⊥`), so the component asserts `◯(E@0 ⊃ ⊥)` — false
in any battery frame where the atoms hold.  A pass that cannot fire here
measures nothing.

## The passes

Over every corpus record with `why=run` (same instances, zero generation
cost; skipped records agree by construction, exactly as `replayUnboxed`):

* `Z`  control:  `[src, amb] ⊢ comp2 0`          — expect hits
* `A`  C-TBL:    `[src, amb] ⊢ comp2 (b−1)`      (b ≥ 2)
* `B`  C-TBL:    `[src, amb] ⊢ comp2 1`
* `C`  C-GOAL:   `[src, amb] ⊢ comp1 (b−1)`
* `D`  C-GOAL:   `[src, amb] ⊢ comp1 1`          (b ≥ 2)
* `G`  C-PROD:   `[boxedSrc, amb] ⊢ gcomp (b−1)` (γ-cells, b ≥ 2)
* `H`  C-PROD:   `[boxedSrc, amb] ⊢ gcomp 1`     (γ-cells)

where `comp2 c = ◯(E@(ft,c)(Γ) ⊃ A@(ft,c)(Γ, ◯D))`,
`comp1 c = ◯(E@(ft,c)(Γ) ⊃ A@(ft,c+1)(Γ, D))`, and for the cell's live
γ-clause `◯A₁ ⊃ B₀ ∈ Γ`: `gcomp c = ◯(E@(ft,c)(Γ) ⊃ A@(ft,c)(Γ, ◯A₁))`,
`boxedSrc = ◯(E@(fs,b)(Γ) ⊃ A@(fs,b)(Γ, ◯A₁))`.

Durable output: `wip/frontier_g7.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g7Ledger : Ledger := { path := "wip/frontier_g7.txt" }

/-- `comp2 c` — the boxed γ-head-shaped component at the cell's own goal
body, both slots at `(ft, c)`. -/
def Cell.comp2 (c : Cell) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S c.ft cb c.ctx).ifThen
    (itpA pv c.S c.ft cb c.ctx c.body.somehow)).somehow

/-- `comp1 c` — the committed goal clause: guard at `c`, value at `c+1`,
body UNBOXED (the shape of `itpAgoal` at a `◯`-goal). -/
def Cell.comp1 (c : Cell) (cg : Nat) : PLLFormula :=
  ((itpE pv c.S c.ft cg c.ctx).ifThen
    (itpA pv c.S c.ft (cg + 1) c.ctx c.body)).somehow

/-- The cell's first LIVE γ-clause `◯A₁ ⊃ B₀ ∈ Γ` (`B₀ ∈ S ∖ Γ`), if any. -/
def Cell.liveGammaAnt? (c : Cell) : Option PLLFormula :=
  match c.ctx.find? (fun F => match F with
    | .ifThen (.somehow _) B => !(c.ctx.contains B) && c.Sl.contains B
    | _ => false) with
  | some (.ifThen (.somehow X) _) => some X.somehow
  | _ => none

/-- The source's own γ-head component for that clause (budget `b`, the slot
the source table carries it at). -/
def Cell.boxedSrc (c : Cell) (ant : PLLFormula) : PLLFormula :=
  ((itpE pv c.S c.fs c.b c.ctx).ifThen
    (itpA pv c.S c.fs c.b c.ctx ant)).somehow

/-- The needed component for that clause at budget `cb`. -/
def Cell.gcomp (c : Cell) (ant : PLLFormula) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S c.ft cb c.ctx).ifThen
    (itpA pv c.S c.ft cb c.ctx ant)).somehow

/-- One replay pass: premises and target from the cell, size-capped like the
campaign, countermodel-only.  `none` from `mk` = this pass does not apply to
this cell (agree with the recorded verdict by construction). -/
def passOn (tag : String) (cap : Nat)
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
  g7Ledger.comment s!"PASS {tag}: {r.render}"
  for n in r.notes.take 40 do g7Ledger.comment s!"  {n}"

def passZ (cap : Nat) : IO Unit :=
  passOn "Z (control: C-TBL c=0, expect hits)" cap (fun c =>
    some ([c.src, c.amb], c.comp2 0))

def passA (cap : Nat) : IO Unit :=
  passOn "A (C-TBL c=b-1)" cap (fun c =>
    if c.b < 2 then none else some ([c.src, c.amb], c.comp2 (c.b - 1)))

def passB (cap : Nat) : IO Unit :=
  passOn "B (C-TBL c=1)" cap (fun c =>
    some ([c.src, c.amb], c.comp2 1))

def passC (cap : Nat) : IO Unit :=
  passOn "C (C-GOAL c=b-1)" cap (fun c =>
    some ([c.src, c.amb], c.comp1 (c.b - 1)))

def passD (cap : Nat) : IO Unit :=
  passOn "D (C-GOAL c=1)" cap (fun c =>
    if c.b < 2 then none else some ([c.src, c.amb], c.comp1 1))

def passG (cap : Nat) : IO Unit :=
  passOn "G (C-PROD c=b-1, gamma cells)" cap (fun c =>
    match c.liveGammaAnt? with
    | none => none
    | some ant =>
        if c.b < 2 then none
        else some ([c.boxedSrc ant, c.amb], c.gcomp ant (c.b - 1)))

def passH (cap : Nat) : IO Unit :=
  passOn "H (C-PROD c=1, gamma cells)" cap (fun c =>
    match c.liveGammaAnt? with
    | none => none
    | some ant => some ([c.boxedSrc ant, c.amb], c.gcomp ant 1))

def g7All : IO Unit := do
  let ok ← calibrate
  if !ok then
    g7Ledger.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    g7Ledger.comment "=== round-7 guard-stack candidate replay ==="
    passZ 40000
    passA 40000
    passB 40000
    passC 40000
    passD 40000
    passG 40000
    passH 40000
    g7Ledger.comment "=== round-7 replay done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g7All
