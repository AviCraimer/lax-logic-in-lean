import frontier

/-!
# ROUND 9, PHASE 1c — the candidate passes, re-driven over the ENLARGED corpus

The round-8 passes (`wip/frontier_g8.lean`) came back clean on 1152 records
for statements that round 9 has since REFUTED (`wip/round9pin.lean`).  This
file re-drives them over the corpus enlarged by the round-9 strata, whose
last three empty the context — the region campaign 1, campaign 2 and g8
never sampled.  The question the run answers is not whether the statements
hold (they do not) but whether the SAMPLER catches it: a stratum is worth
its seeds exactly when it turns a clean pass into a hit.

## The passes

* `Z0`/`Z1` controls — as in round 8, live-fire calibration at this premise
  pair.
* `BD` — the standard screen `[src, amb] ⊢ tgt`, i.e. `Round4.BoxDesc`.
* `W1`/`W2` — `Round8.GoalRowAbsorb` (`c = b−1`, `c = 1`).
* `X1`/`X2` — the committed goal clause.
* `P1`/`P2` — `Round7.CompProd` at the cell's own body.
* `F1`/`F2` — **the round-9 residue**, the fresh-row descent

      [ E@(f,b)(C₁::Γ) ⊃ A@(f,b)(C₁::Γ,C₂), amb ] ⊢
        E@(f,c)(C₁::Γ) ⊃ A@(f,c)(C₁::Γ,C₂)

  run only where the body is an implication whose antecedent is ABSENT from
  the context (`f = ft − 1`, matching the walk's inner fuel).
* `Fp` — the matched PRESENT-antecedent row (guard one budget below the
  value), the control for `F1`/`F2`.

Durable output: `wip/frontier_g9c.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9cLedger : Ledger := { path := "wip/frontier_g9c.txt" }

/-- **The frame the battery was missing.**  `wip/round9pin.lean`'s `P3c` is
the three-world chain `0 ⊑ 1 ⊑ 2` whose only modal step is `1 ⊳ 2`, with NO
fallible world.  `Round5Refute.xFrames` has the three-chain with `rm` EMPTY;
`defaultFrames` has it with `rm = [(1,2)]` but a FALLIBLE top (`fall = [2]`),
which forces every atom at world `2` and destroys the configuration.  The
infallible single-step three-chain is in neither list — and it is the frame
that refutes `Round4.BoxDesc`.  Every `quiet` verdict in the corpus was
produced by a battery blind to it. -/
def frameP3c : Frame := ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], []⟩

/-- …and its four-world analogue, for one more step of head-room. -/
def frameP4c : Frame := ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], []⟩

/-- The widened countermodel-only configuration. -/
def cfgCM9 : Config :=
  { frames := frameP3c :: frameP4c :: (Round5Refute.xFrames ++ defaultFrames)
  , emitClosureCap := 0 }

def Cell.g9comp (c : Cell) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S c.ft cb c.ctx).ifThen
    (itpA pv c.S c.ft cb c.ctx c.body.somehow)).somehow

def Cell.g9gsrc (c : Cell) : PLLFormula :=
  ((itpE pv c.S (c.ft - 1) (c.b - 1) c.ctx).ifThen
    (itpA pv c.S (c.ft - 1) c.b c.ctx c.body)).somehow

def Cell.g9tgtAt (c : Cell) (cb : Nat) : PLLFormula :=
  itpA pv c.S c.ft cb c.ctx c.body.somehow

def Cell.g9gclause (c : Cell) (cb : Nat) : PLLFormula :=
  ((itpE pv c.S (c.ft - 1) (cb - 1) c.ctx).ifThen
    (itpA pv c.S (c.ft - 1) cb c.ctx c.body)).somehow

def Cell.g9compS (c : Cell) : PLLFormula :=
  ((itpE pv c.S c.fs c.b c.ctx).ifThen
    (itpA pv c.S c.fs c.b c.ctx c.body.somehow)).somehow

/-- The body's implication parts, when it is one. -/
def Cell.impParts (c : Cell) : Option (PLLFormula × PLLFormula) :=
  match c.body with
  | .ifThen A B => some (A, B)
  | _ => none

/-- The FRESH row at budget `cb`: both slots at `cb` (the `C₁ ∉ Γ` branch of
`itpAgoal`), inner fuel `ft − 1`. -/
def Cell.freshRow (c : Cell) (C₁ C₂ : PLLFormula) (cb : Nat) : PLLFormula :=
  (itpE pv c.S (c.ft - 1) cb (C₁ :: c.ctx)).ifThen
    (itpA pv c.S (c.ft - 1) cb (C₁ :: c.ctx) C₂)

/-- The PRESENT row at budget `cb`: guard one budget below the value. -/
def Cell.presentRow (c : Cell) (C₁ C₂ : PLLFormula) (cb : Nat) : PLLFormula :=
  (itpE pv c.S (c.ft - 1) (cb - 1) (C₁ :: c.ctx)).ifThen
    (itpA pv c.S (c.ft - 1) cb (C₁ :: c.ctx) C₂)

def passOnG9 (cfg : Config) (tag : String) (cap : Nat)
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
        let v ← IO.lazyPure (fun _ => refute? cfg prems tgt)
        match v with
        | some ⟨M, w, _⟩ =>
            pure { triage := .hit, cert := s!"w={w} M={reprStr M}" }
        | none => pure { triage := .quiet })
  g9cLedger.comment s!"PASS {tag}: {r.render}"
  for n in r.notes.take 40 do g9cLedger.comment s!"  {n}"

def g9cAll : IO Unit := do
  let ok ← calibrate
  if !ok then
    g9cLedger.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    g9cLedger.comment "=== round-9 candidate replay over the enlarged corpus ==="
    passOnG9 cfgCM9 "Z0 (control: goal row to comp 0, expect hits)" 40000 (fun c =>
      some ([c.g9gsrc, c.amb], c.g9comp 0))
    passOnG9 cfgCM9 "F2 (RESIDUE: fresh-row descent, c=1)" 40000 (fun c =>
      match c.impParts with
      | none => none
      | some (a, b) =>
          if c.b < 2 || c.ctx.contains a then none
          else some ([c.freshRow a b c.b, c.amb], c.freshRow a b 1))
    passOnG9 cfgCM9 "F1 (RESIDUE: fresh-row descent, c=b-1)" 40000 (fun c =>
      match c.impParts with
      | none => none
      | some (a, b) =>
          if c.b < 2 || c.ctx.contains a then none
          else some ([c.freshRow a b c.b, c.amb], c.freshRow a b (c.b - 1)))
    passOnG9 cfgCM9 "Fp (CONTROL: present-antecedent row descent, c=1)" 40000 (fun c =>
      match c.impParts with
      | none => none
      | some (a, b) =>
          if c.b < 2 || !(c.ctx.contains a) then none
          else some ([c.presentRow a b c.b, c.amb], c.presentRow a b 1))
    passOnG9 cfgCM9 "BD (Round4.BoxDesc: [src, amb] |- tgt)" 40000 (fun c =>
      some ([c.src, c.amb], c.tgt))
    passOnG9 cfgCM9 "W2 (GoalRowAbsorb, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.g9gsrc, c.amb], c.g9tgtAt 1))
    passOnG9 cfgCM9 "W1 (GoalRowAbsorb, c=b-1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.g9gsrc, c.amb], c.g9tgtAt (c.b - 1)))
    passOnG9 cfgCM9 "X2 (committed goal clause, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.g9gsrc, c.amb], c.g9gclause 1))
    passOnG9 cfgCM9 "P2 (CompProd at own body, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.g9compS, c.amb], c.g9comp 1))
    g9cLedger.comment "--- the same two passes at the ROUND-8 battery, for contrast ---"
    passOnG9 cfgCM "BD-old (Round4.BoxDesc, round-8 frame list)" 40000 (fun c =>
      some ([c.src, c.amb], c.tgt))
    passOnG9 cfgCM "W2-old (GoalRowAbsorb c=1, round-8 frame list)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.g9gsrc, c.amb], c.g9tgtAt 1))
    g9cLedger.comment "=== round-9 replay done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9cAll
