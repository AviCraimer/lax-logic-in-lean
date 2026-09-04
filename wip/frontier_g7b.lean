import frontier_g7

/-!
# ROUND 7, PHASE 1b — the BOTTOM of the gap-preserving component recursion

Design analysis of the C-PROD build (recorded in the round report): opening
the held component with the ambient (`laxL` + fire with `ambE`-lowered
ambient) turns C-PROD into a gap-preserving pair recursion
`(b, c) → (b−1, c−1)` on the γ-head rows — no room is consumed per level, so
`no_self_financed_nest` does not apply — but the chain bottoms at `c = 1`,
where the source's γ-head row hands a component at budget `1` and the target
table at budget `1` must be closed from it.  The bottom obligation, as a
two-premise sequent:

    [ ◯( E@(fs,1)(Γ) ⊃ A@(fs,1)(Γ, ◯X) ) , E@(ft, b+1)(Γ) ]
      ⊢ A@(ft, 1)(Γ, ◯X)

for `X` the cell's γ-clause antecedent body (pass `T`) and for the cell's
own goal body `D` (pass `U`).  A hit refutes the two-premise bottom and
pins that the bottom needs more resources (the grown conjunct, or the top
room); quiet supports the bottom as stated.

Pass `V` re-screens any bottom hits with the γ-row's SECOND conjunct (the
grown component `A@(fs, 2)(B₀::Γ, ◯X)`) added as a third premise — the
resource the walk actually holds at the bottom.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

/-- The component at budget 1 in the source's own slots. -/
def Cell.srcComp1 (c : Cell) (body : PLLFormula) : PLLFormula :=
  ((itpE pv c.S c.fs 1 c.ctx).ifThen
    (itpA pv c.S c.fs 1 c.ctx body)).somehow

/-- The bottom target: the full table at budget 1, reference fuel. -/
def Cell.tbl1 (c : Cell) (body : PLLFormula) : PLLFormula :=
  itpA pv c.S c.ft 1 c.ctx body

/-- The γ-row's grown second conjunct at budget 2: `A@(fs,2)(B₀::Γ, ◯X)`. -/
def Cell.grown2? (c : Cell) : Option PLLFormula :=
  match c.ctx.find? (fun F => match F with
    | .ifThen (.somehow _) B => !(c.ctx.contains B) && c.Sl.contains B
    | _ => false) with
  | some (.ifThen (.somehow X) B) =>
      some (itpA pv c.S c.fs 2 (B :: c.ctx) X.somehow)
  | _ => none

def passT (cap : Nat) : IO Unit :=
  passOn "T (bottom, gamma body)" cap (fun c =>
    match c.liveGammaAnt? with
    | none => none
    | some ant => some ([c.srcComp1 ant, c.amb], c.tbl1 ant))

def passU (cap : Nat) : IO Unit :=
  passOn "U (bottom, goal body)" cap (fun c =>
    some ([c.srcComp1 c.body.somehow, c.amb], c.tbl1 c.body.somehow))

def passV (cap : Nat) : IO Unit :=
  passOn "V (bottom + grown conjunct, gamma body)" cap (fun c =>
    match c.liveGammaAnt?, c.grown2? with
    | some ant, some gr => some ([c.srcComp1 ant, gr, c.amb], c.tbl1 ant)
    | _, _ => none)

def g7bAll : IO Unit := do
  let ok ← calibrate
  if !ok then
    g7Ledger.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    g7Ledger.comment "=== round-7 bottom-obligation replay ==="
    passT 40000
    passU 40000
    passV 40000
    g7Ledger.comment "=== round-7 bottom replay done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g7bAll
