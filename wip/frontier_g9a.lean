import frontier

/-!
# ROUND 9, PHASE 1a — the FRESH-ROW DESCENT at the witnesses

PROGRESS §67(h) delimits the whole campaign to one sequent.  With
`D = C₁ ⊃ C₂` an unboxed compound goal body whose antecedent is FRESH
(`C₁ ∉ Γ`), the target table's own goal disjunct and the source table's
own goal disjunct sit at MATCHED slots (both guard and value at the
displayed budget — the `C₁ ∈ Γ` branch of `itpAgoal` is the one that
lowers the guard, and it is not taken here), so the absorption's inner
obligation is

    freshRow(b) := E@(f,b)(C₁::Γ) ⊃ A@(f,b)(C₁::Γ, C₂)
    ambient     := E@(ft,b+1)(Γ)
    ─────────────────────────────────────────────────
    freshRow(c) := E@(f,c)(C₁::Γ) ⊃ A@(f,c)(C₁::Γ, C₂)          (c < b)

Under `impR` the target's guard `E@(f,c)(C₁::Γ)` is available and the
value `A@(f,c)(C₁::Γ,C₂)` is wanted; the only known route fires the
source row, which demands the guard at the SOURCE budget — the ascent
`c → b` at the grown context.  That ascent is `AmbGuardAscent`, and
`AscRefute.not_ambGuardAscent` refutes it room-free at exactly this
shape (`Xr = ◯r ⊃ s` fresh over `Gr = [◯p ⊃ r]`, budget floor).
`Round6.easc_tight` finances it only from `J + 2 + defect′·(J+2) ≤ c`.

## The instances

`Skb`/`Gk` is July's witness: `gk = (◯r ⊃ s) ⊃ t`, so `C₁ = ◯r ⊃ s`,
`C₂ = t`, and `C₁ ∉ Gk = [◯p ⊃ r]` — the fresh antecedent is itself a
`⊃◯`-clause, which is what makes the grown context's guard
budget-gated.  Rows are named `Fk`; the ascent control is `Ak`.

`S3`/`Γ3` is round 6's nest witness with the goal antecedent DELETED
from the context (`Γ3f := Γ3 ∖ {a}`): the same shape at a
`⊃`-antecedent that is NOT a `⊃◯`-clause, which separates "fresh" from
"fresh AND budget-gated".

Every instance is countermodel-first (`refute?`, full certified battery,
`emitClosureCap := 0`), then `prove?Bounded` with the derivation printed.

Durable output: `wip/frontier_g9a.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

def g9aLedger : Ledger := { path := "wip/frontier_g9a.txt" }

def runInst9 (nm : String) (prems : List PLLFormula) (tgt : PLLFormula)
    (pbudget : Nat) : IO Unit := do
  let n ← IO.lazyPure (fun _ =>
    (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
  g9aLedger.comment s!"{nm} sz={n}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g9aLedger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => prove?Bounded pbudget prems tgt)
      match d with
      | some t =>
          g9aLedger.comment s!"  P (proved, budget {pbudget})"
          let s ← IO.lazyPure (fun _ => t.pretty)
          g9aLedger.comment s!"  TERM {s.take 6000}"
      | none => g9aLedger.comment s!"  ~ (quiet, unproved at {pbudget})"

/-! ### `S3` with the goal antecedent deleted — the non-gated fresh shape -/

def s3l9 : List PLLFormula :=
  [ ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b", prop "c" ]

def s3F9 : Finset PLLFormula := s3l9.toFinset

/-- `Γ3` with BOTH `c` and the goal antecedent `a` deleted: `a ∉ Γ3f`, so
the goal disjunct of `A(Γ3f, a ⊃ b)` is the FRESH row. -/
def g3f9 : List PLLFormula :=
  s3l9.filter (fun F => F != prop "c" && F != prop "a")

def aib9 : PLLFormula := (prop "a").ifThen (prop "b")

open Round4Probe3 AscRefute in
def g9aAll : IO Unit := do
  g9aLedger.comment "=== round-9 fresh-row witnesses (g9a) ==="
  -- `Skb`/`Gk`: C₁ = ◯r ⊃ s (fresh, ⊃◯-shaped), C₂ = t
  let c1 : PLLFormula := ((prop "r").somehow).ifThen (prop "s")
  let cGk : List PLLFormula := c1 :: Gk
  let amb3 : PLLFormula := itpE "p" Skb 4 3 Gk
  let amb4 : PLLFormula := itpE "p" Skb 4 4 Gk
  let fk (f bb : Nat) : PLLFormula :=
    (itpE "p" Skb f bb cGk).ifThen (itpA "p" Skb f bb cGk (prop "t"))
  -- (1) the ASCENT control at the grown context: expect a refutation
  --     (`AscRefute.not_ambGuardAscent`'s shape, ambient one budget higher)
  runInst9 "g9a Ak-ASC  [E@(2,1)(C₁::Gk), amb@3] |- E@(2,2)(C₁::Gk)"
    [itpE "p" Skb 2 1 cGk, amb3] (itpE "p" Skb 2 2 cGk) 40000
  runInst9 "g9a Ak-ASC4 [E@(2,1)(C₁::Gk), amb@4] |- E@(2,2)(C₁::Gk)"
    [itpE "p" Skb 2 1 cGk, amb4] (itpE "p" Skb 2 2 cGk) 40000
  -- (2) the residue verbatim, gap 1, inner fuel 2 (the §67(g) `Skb-F` row)
  runInst9 "g9a Fk-1   [freshRow@2, amb@3] |- freshRow@1"
    [fk 2 2, amb3] (fk 2 1) 40000
  -- (3) the residue WITH the walk's outer introduced guard added
  runInst9 "g9a Fk-1g  [freshRow@2, E@(3,0)(Gk), amb@3] |- freshRow@1"
    [fk 2 2, itpE "p" Skb 3 0 Gk, amb3] (fk 2 1) 40000
  -- (4) the residue with the ambient ALREADY at the grown context: isolates
  --     the grown-ambient gap as the whole obstruction
  runInst9 "g9a Fk-1G  [freshRow@2, E@(4,3)(C₁::Gk)] |- freshRow@1"
    [fk 2 2, itpE "p" Skb 4 3 cGk] (fk 2 1) 40000
  -- (5) the value descent at the grown context under the LOW guard
  runInst9 "g9a Fk-V   [A@(2,2)(C₁::Gk,t), E@(2,1)(C₁::Gk), amb@3] |- A@(2,1)(C₁::Gk,t)"
    [itpA "p" Skb 2 2 cGk (prop "t"), itpE "p" Skb 2 1 cGk, amb3]
    (itpA "p" Skb 2 1 cGk (prop "t")) 40000
  -- (6) inner fuel 3
  runInst9 "g9a Fk-f3  [freshRow₃@2, amb@3] |- freshRow₃@1"
    [fk 3 2, amb3] (fk 3 1) 40000
  -- (7) gap 1 one budget up
  runInst9 "g9a Fk-32  [freshRow@3, amb@4] |- freshRow@2"
    [fk 2 3, amb4] (fk 2 2) 40000
  -- `S3` fresh: C₁ = a (atomic, NOT budget-gated), C₂ = b
  let amb3s : PLLFormula := itpE pv s3F9 5 5 g3f9
  let f3 (bb : Nat) : PLLFormula :=
    (itpE pv s3F9 4 bb (prop "a" :: g3f9)).ifThen
      (itpA pv s3F9 4 bb (prop "a" :: g3f9) (prop "b"))
  runInst9 "g9a S3f-43 [freshRow@4, amb@5] |- freshRow@3" [f3 4, amb3s] (f3 3) 40000
  runInst9 "g9a S3f-41 [freshRow@4, amb@5] |- freshRow@1" [f3 4, amb3s] (f3 1) 40000
  g9aLedger.comment "=== g9a done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g9aAll
