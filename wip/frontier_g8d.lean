import frontier_g8

/-!
# ROUND 8, PHASE 1c′ — the two DISCRIMINATORS, run out of order

Split from `wip/frontier_g8c.lean` so their verdicts land first (the
ordered run spends its budget on the searcher-quiet `Skb` table rows):

* `Skb-F/F3` — the delimited inner obligation of the committed route at
  the FRESH inner goal row (`gk`'s antecedent `◯r ⊃ s ∉ Gk`): the
  source's fresh goal disjunct to the target's fresh goal disjunct, from
  the ambient alone.  This is the step whose only known financing is the
  room-priced guard ascent (`cascade_main_bf`'s `hroomE`;
  `Round6.easc_tight`), which a room-free walk does not have.
* `Skb-U/U0` — the unboxed same-context descent at the GROWN context
  `r :: Gk` (defect one below July's refuted `Gk` instance), with the
  grown ambient: what the γ-row-within-goal-row landing consumes.

Durable output: `wip/frontier_g8.txt` (tagged `g8d`).
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

/-- `frontier_g8c.lean`'s `runInst`, cloned (that file is a concurrent
recorded artifact, not an import): countermodel-first, then bounded
positive with the found derivation printed. -/
def runInstD (nm : String) (prems : List PLLFormula) (tgt : PLLFormula)
    (pbudget : Nat) : IO Unit := do
  let n ← IO.lazyPure (fun _ =>
    (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
  g8Ledger.comment s!"{nm} sz={n}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g8Ledger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => prove?Bounded pbudget prems tgt)
      match d with
      | some t =>
          g8Ledger.comment s!"  P (proved, budget {pbudget})"
          let s ← IO.lazyPure (fun _ => t.pretty)
          g8Ledger.comment s!"  TERM {s.take 6000}"
      | none => g8Ledger.comment s!"  ~ (quiet, unproved at {pbudget})"

open Round4Probe3 AscRefute in
def g8dAll : IO Unit := do
  let amb : PLLFormula := itpE "p" Skb 4 3 Gk
  let amb4 : PLLFormula := itpE "p" Skb 4 4 Gk
  let freshRow (bb : Nat) : PLLFormula :=
    (itpE "p" Skb 2 bb (((prop "r").somehow).ifThen (prop "s") :: Gk)).ifThen
      (itpA "p" Skb 2 bb (((prop "r").somehow).ifThen (prop "s") :: Gk)
        (prop "t"))
  let rGk : List PLLFormula := prop "r" :: Gk
  g8Ledger.comment "=== round-8 discriminators (g8d, out of order) ==="
  runInstD "g8d Skb-F  [freshRow@2, amb@3] |- freshRow@1"
    [freshRow 2, amb] (freshRow 1) 40000
  runInstD "g8d Skb-F3 [freshRow@3, amb@4] |- freshRow@1"
    [freshRow 3, amb4] (freshRow 1) 40000
  runInstD "g8d Skb-U  [A@(4,2)(r::Gk,gk), E@(4,3)(r::Gk)] |- A@(4,1)(r::Gk,gk)"
    [itpA "p" Skb 4 2 rGk gk, itpE "p" Skb 4 3 rGk]
    (itpA "p" Skb 4 1 rGk gk) 40000
  runInstD "g8d Skb-U0 [A@(4,2)(r::Gk,gk), E@(4,3)(rGk), amb@3] |- A@(4,1)(r::Gk,gk)"
    [itpA "p" Skb 4 2 rGk gk, itpE "p" Skb 4 3 rGk, amb]
    (itpA "p" Skb 4 1 rGk gk) 40000
  g8Ledger.comment "=== g8d done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g8dAll
