import frontier_g8d

/-!
# ROUND 8, PHASE 1c″ — the remaining witness instances, re-ordered

The ordered `frontier_g8c.lean` run spent its budget on searcher-quiet
`Skb` rows and was superseded by this trimmed driver (its durable verdicts
stand: `Skb-CTRL R!`, `Skb-W ~`, `Skb-P ~`; the `Skb-X` verdict line was
lost to a concurrent-writer race with `frontier_g8d.lean` — re-derived
here FIRST, on this file's own ledger so no two processes share a file).

Order: the lost `Skb-X`; then the `S3` block (the present-antecedent
witness, where the searcher is expected to PROVE and the terms carry the
build mechanics); then the gap-2 `Skb` block.

Durable output: `wip/frontier_g8e.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g8eLedger : Ledger := { path := "wip/frontier_g8e.txt" }

def runInstE (nm : String) (prems : List PLLFormula) (tgt : PLLFormula)
    (pbudget : Nat) : IO Unit := do
  let n ← IO.lazyPure (fun _ =>
    (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
  g8eLedger.comment s!"{nm} sz={n}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g8eLedger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => prove?Bounded pbudget prems tgt)
      match d with
      | some t =>
          g8eLedger.comment s!"  P (proved, budget {pbudget})"
          let s ← IO.lazyPure (fun _ => t.pretty)
          g8eLedger.comment s!"  TERM {s.take 6000}"
      | none => g8eLedger.comment s!"  ~ (quiet, unproved at {pbudget})"

/-- `S3`/`Γ3` cloned locally (the `frontier_g8c.lean` clones, repeated so
this file does not depend on that in-flight artifact). -/
def s3le : List PLLFormula :=
  [ ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b", prop "c" ]

def g3e : List PLLFormula := s3le.filter (fun F => F != prop "c")

def s3Fe : Finset PLLFormula := s3le.toFinset

def aibe : PLLFormula := (prop "a").ifThen (prop "b")

open Round4Probe3 AscRefute in
def g8eAll : IO Unit := do
  g8eLedger.comment "=== round-8 witness instances, re-ordered (g8e) ==="
  -- the lost Skb-X verdict, re-derived
  let amb : PLLFormula := itpE "p" Skb 4 3 Gk
  let gsrcK : PLLFormula :=
    ((itpE "p" Skb 3 1 Gk).ifThen (itpA "p" Skb 3 2 Gk gk)).somehow
  let xK : PLLFormula :=
    ((itpE "p" Skb 3 0 Gk).ifThen (itpA "p" Skb 3 1 Gk gk)).somehow
  runInstE "g8e Skb-X  [gsrc, amb] |- gclause@1" [gsrcK, amb] xK 40000
  -- the S3 block (fs = ft = 5, b = 4, f = 4, D = a⊃b present-antecedent)
  let amb3 : PLLFormula := itpE pv s3Fe 5 5 g3e
  let gsrc3 : PLLFormula :=
    ((itpE pv s3Fe 4 3 g3e).ifThen (itpA pv s3Fe 4 4 g3e aibe)).somehow
  let w3 (c : Nat) : PLLFormula := itpA pv s3Fe 5 c g3e aibe.somehow
  let x3 (c : Nat) : PLLFormula :=
    ((itpE pv s3Fe 4 (c - 1) g3e).ifThen (itpA pv s3Fe 4 c g3e aibe)).somehow
  let compS3 : PLLFormula :=
    ((itpE pv s3Fe 5 4 g3e).ifThen (itpA pv s3Fe 5 4 g3e aibe.somehow)).somehow
  let p3 (c : Nat) : PLLFormula :=
    ((itpE pv s3Fe 5 c g3e).ifThen (itpA pv s3Fe 5 c g3e aibe.somehow)).somehow
  runInstE "g8e S3-X c=3  [gsrc, amb] |- gclause@3" [gsrc3, amb3] (x3 3) 40000
  runInstE "g8e S3-X c=1  [gsrc, amb] |- gclause@1" [gsrc3, amb3] (x3 1) 40000
  runInstE "g8e S3-W c=3  [gsrc, amb] |- tgt@3" [gsrc3, amb3] (w3 3) 40000
  runInstE "g8e S3-W c=1  [gsrc, amb] |- tgt@1" [gsrc3, amb3] (w3 1) 40000
  runInstE "g8e S3-P c=3  [compS, amb] |- comp@3" [compS3, amb3] (p3 3) 40000
  runInstE "g8e S3-P c=1  [compS, amb] |- comp@1" [compS3, amb3] (p3 1) 40000
  -- the gap-2 Skb block
  let amb4 : PLLFormula := itpE "p" Skb 4 4 Gk
  let gsrcK3 : PLLFormula :=
    ((itpE "p" Skb 3 2 Gk).ifThen (itpA "p" Skb 3 3 Gk gk)).somehow
  let compSK3 : PLLFormula :=
    ((itpE "p" Skb 4 3 Gk).ifThen (itpA "p" Skb 4 3 Gk gk.somehow)).somehow
  let wK : PLLFormula := itpA "p" Skb 4 1 Gk gk.somehow
  let pK : PLLFormula :=
    ((itpE "p" Skb 4 1 Gk).ifThen (itpA "p" Skb 4 1 Gk gk.somehow)).somehow
  runInstE "g8e Skb-W3 [gsrc@3, amb@4] |- tgt@1" [gsrcK3, amb4] wK 40000
  runInstE "g8e Skb-X3 [gsrc@3, amb@4] |- gclause@1" [gsrcK3, amb4] xK 40000
  runInstE "g8e Skb-P3 [compS@3, amb@4] |- comp@1" [compSK3, amb4] pK 40000
  g8eLedger.comment "=== g8e done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g8eAll
