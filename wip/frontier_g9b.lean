import frontier

/-!
# ROUND 9, PHASE 1b — the fresh-antecedent stratum, generated and screened

Two steps, in order, on one ledger:

1. **Determinism audit.**  Round 9 edited `wip/frontier.lean` (a
   `gimp` branch in `genBase`, a `bgrid` field on `Base`, four new strata).
   Every pre-round-9 stratum takes the `genBaseStd` branch and an empty
   `bgrid`, so the 1152-record corpus must regenerate byte-identically.  This
   is checked FIRST: if it disagrees, nothing later in the round is usable.

2. **The residue stratum.**  `campaignG9Strata` — `g9-gimp`, `g9-gimpX`,
   `g9-gimp0` (fresh antecedent) and `g9-gimpP` (the present-antecedent
   control) — appended to the corpus under the standard gate stack and the
   standard countermodel-only triage `[src, amb] ⊢ tgt`.  A hit there is a
   refutation of `Round4.BoxDesc` outright.

Durable output: `wip/frontier_g9b.txt` (this file's own ledger) and the
corpus `wip/frontier_corpus.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9bLedger : Ledger := { path := "wip/frontier_g9b.txt" }

/-- The §7 regression replay, on this round's own ledger. -/
def g9Regression : IO Unit := do
  let r ← replay corpus regen (fun c rc => pure
    { triage := if shapeOf c == shapeFromRec rc then rc.triage else Triage.hit
    , cert := shapeOf c })
  g9bLedger.comment s!"REGRESSION (shape agreement): {r.render}"
  for n in r.notes.take 20 do g9bLedger.comment s!"  {n}"

def g9bAll : IO Unit := do
  g9bLedger.comment "=== round-9 stratum generation (g9b) ==="
  -- what the generator actually produced, before any search time is spent
  for st in campaignG9cStrata do
    g9bLedger.comment s!"== {st.name} : {st.note}"
    for i in [0:4] do
      let sd := (st.seed0 / cellsPerBase + i) * cellsPerBase
      match st.gen sd st.size with
      | none => g9bLedger.comment s!"  seed {sd}: (no cell)"
      | some c =>
        let sf := String.intercalate " ⋄ " (c.seeds.map reprStr)
        let dr := String.intercalate " ⋄ " (c.dropped.map reprStr)
        let cx := String.intercalate " ⋄ " (c.ctx.map reprStr)
        let gt := (firstFailure gates c).getD "ok"
        g9bLedger.comment s!"  seed={sd} sf={sf} D={reprStr c.body} |S|={c.Sl.length} \
d={c.defect} J={c.J} room={c.room} b={c.b} fs={c.fs} ft={c.ft} lg={c.liveGates} \
drop={dr} ctx={cx} gate={gt}"
  g9bLedger.comment "=== generating the g9c (fuel-untied) campaign into the corpus ==="
  campaignOf 40000 "g9c" campaignG9cStrata
  g9bLedger.comment "=== g9b done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9bAll
