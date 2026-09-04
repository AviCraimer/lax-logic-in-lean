import frontier_g8

/-!
# ROUND 8, PHASE 1b — the residue stratum, generated, gated, screened, and
# re-driven at the round-8 sequents

The §65 standing rule, applied to the round-8 residue (PROGRESS §66(h)):
the residue shape defines a sampler stratum, run BEFORE any proof build is
scoped.  The shape: jump-shaped UNBOXED goal bodies `D = (x⊃y)⊃z` over a
γ-carrying space (`g8-d1jump`: γ-depth 1; `g8-d2jump`: γ-depth 2, the `S3`
nest).  Both strata are new to `wip/frontier.lean` (seeds 20000/21000);
their cells are appended to the shared corpus by the STANDARD triage
(`[src, amb] ⊢ tgt` — a hit at any admissible cell kills the room-free
`Round4.BoxDesc` outright, sub-room cells included), and then re-driven at
the nine round-8 pass sequents of `wip/frontier_g8.lean`, restricted to
the `g8-*` strata (the older strata were re-driven by `frontier_g8.lean`
itself).

A `CP-P` hit here would refute `Round7.CompProd` at an admissible cell of
exactly the residue shape and, through
`Round7.not_boxDesc_of_not_compProd`, kill the room-free route — the
campaign-level negative this stratum exists to hunt.

Durable output: campaign lines in `wip/frontier_corpus.txt`, pass reports
in `wip/frontier_g8.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

/-- The round-8 pass, restricted to the `g8-*` strata (everything else
agrees by construction — the full-corpus verdicts are `frontier_g8.lean`'s
report). -/
def passOnG8s (tag : String) (cap : Nat)
    (mk : Cell → Option (List PLLFormula × PLLFormula)) : IO Unit := do
  let r ← replay corpus regen (fun c rc => do
    if !(rc.stratum.startsWith "g8-") then pure { triage := rc.triage }
    else if (rc.col? "why").getD "" != "run" then pure { triage := rc.triage }
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
  g8Ledger.comment s!"PASS {tag} [g8 strata]: {r.render}"
  for n in r.notes.take 40 do g8Ledger.comment s!"  {n}"

def g8bAll : IO Unit := do
  let ok ← calibrate
  if !ok then
    g8Ledger.comment "CALIBRATION FAILED — screen is broken, results discarded"
  else do
    g8Ledger.comment "=== round-8 residue stratum: campaign ==="
    let _ ← runCampaign corpus "g8" campaignG8Strata gates cols (triage 40000)
    g8Ledger.comment "=== round-8 residue stratum: pass re-drive ==="
    passOnG8s "Z0 (control: goal row to comp2 0, expect hits)" 40000 (fun c =>
      some ([c.gsrc, c.amb], c.comp2T 0))
    passOnG8s "Z1 (control: goal row to tgt 0, expect hits)" 40000 (fun c =>
      some ([c.gsrc, c.amb], c.tgtAt 0))
    passOnG8s "P1 (CP-P: CompProd at own body, c=b-1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.compS, c.amb], c.comp2T (c.b - 1)))
    passOnG8s "P2 (CP-P: CompProd at own body, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.compS, c.amb], c.comp2T 1))
    passOnG8s "W1 (GR-W: goal row to target table, c=b-1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.gsrc, c.amb], c.tgtAt (c.b - 1)))
    passOnG8s "W2 (GR-W: goal row to target table, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.gsrc, c.amb], c.tgtAt 1))
    passOnG8s "X1 (GR-X: goal row to committed goal clause, c=b-1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.gsrc, c.amb], c.gclause (c.b - 1)))
    passOnG8s "X2 (GR-X: goal row to committed goal clause, c=1)" 40000 (fun c =>
      if c.b < 2 then none else some ([c.gsrc, c.amb], c.gclause 1))
    passOnG8s "E1 (GR-E: goal row to gamma env disjunct, c=b-1)" 40000 (fun c =>
      match c.liveGammaPair? with
      | none => none
      | some (ant, hd) =>
          if c.b < 2 then none
          else some ([c.gsrc, c.amb], c.genv ant hd (c.b - 1)))
    g8Ledger.comment "=== round-8 residue stratum done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g8bAll
