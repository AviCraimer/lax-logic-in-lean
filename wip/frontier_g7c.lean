import frontier_g7

/-!
# ROUND 7, PHASE 1c — the bottom obligation AT THE ROUND-6 WITNESS `S3`

Two-sided instance check of the gap-preserving recursion's bottom at the
exact space that killed the round-6 tower (`Round6.S3`, the piece-closure of
`◯◯(a⊃b) ⊃ c`, context `Γ3` = everything but the γ-consequent `c`):

    [ comp@1 , grown@2 , amb@(b+1) ]  ⊢  A@(ft,1)(Γ3, ◯X)

with `X = ◯(a⊃b)` (the γ-clause antecedent), `comp@1 = ◯(E@1 ⊃ A@1(Γ3,◯X))`,
`grown@2 = A@(fs,2)(c::Γ3, ◯X)`, at the room floor `b = 4`, fuels
`fs = ft = 5` (budget-active) and the truncating pair `(2,2)`.

Countermodel first (`refute?`, full battery); then a bounded positive pass
(`prove?Bounded`, findBudget-style caps) — a `P` here would certify the
bottom at the witness, an `R!` would kill the two-premise-plus-grown bottom.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

/-- `S3`/`Γ3` cloned locally (`Round6` is not imported by the frontier
stack): pieces of `◯◯(a⊃b) ⊃ c`, context = all but `c`. -/
def s3l : List PLLFormula :=
  [ ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b", prop "c" ]

def g3 : List PLLFormula := s3l.filter (fun F => F != prop "c")

def s3F : Finset PLLFormula := s3l.toFinset

/-- The γ-clause antecedent `◯◯(a⊃b)`. -/
def xAnt : PLLFormula := ((prop "a").ifThen (prop "b")).somehow.somehow

def s3comp1 (fs : Nat) : PLLFormula :=
  ((itpE pv s3F fs 1 g3).ifThen (itpA pv s3F fs 1 g3 xAnt)).somehow

def s3grown2 (fs : Nat) : PLLFormula :=
  itpA pv s3F fs 2 (prop "c" :: g3) xAnt

def s3amb (ft b : Nat) : PLLFormula := itpE pv s3F ft (b + 1) g3

def s3tbl1 (ft : Nat) : PLLFormula := itpA pv s3F ft 1 g3 xAnt

def s3cell (fs ft b : Nat) : List PLLFormula × PLLFormula :=
  ([s3comp1 fs, s3grown2 fs, s3amb ft b], s3tbl1 ft)

def runS3 (fs ft b pbudget : Nat) : IO Unit := do
  let (prems, tgt) := s3cell fs ft b
  let n ← IO.lazyPure (fun _ =>
    (prems.map TowerKit.sz).foldl (· + ·) 0 + TowerKit.sz tgt)
  g7Ledger.comment s!"S3-bottom fs={fs} ft={ft} b={b} sz={n}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g7Ledger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => (prove?Bounded pbudget prems tgt).isSome)
      g7Ledger.comment (if d then s!"  P (proved, budget {pbudget})"
                        else s!"  ~ (quiet, unproved at {pbudget})")

/-- Also the TWO-premise bottom (no grown conjunct), same witness. -/
def runS3noGrown (fs ft b pbudget : Nat) : IO Unit := do
  let prems := [s3comp1 fs, s3amb ft b]
  let tgt := s3tbl1 ft
  g7Ledger.comment s!"S3-bottom-nogrown fs={fs} ft={ft} b={b}"
  let v ← IO.lazyPure (fun _ => refute? cfgCM prems tgt)
  match v with
  | some ⟨M, w, _⟩ =>
      g7Ledger.comment s!"  R! w={w} M={reprStr M}"
  | none =>
      let d ← IO.lazyPure (fun _ => (prove?Bounded pbudget prems tgt).isSome)
      g7Ledger.comment (if d then s!"  P (proved, budget {pbudget})"
                        else s!"  ~ (quiet, unproved at {pbudget})")

def g7cAll : IO Unit := do
  g7Ledger.comment "=== round-7 S3 bottom instance ==="
  runS3 5 5 4 40000
  runS3 2 2 4 40000
  runS3 2 5 4 40000
  runS3noGrown 5 5 4 40000
  runS3noGrown 2 2 4 40000
  g7Ledger.comment "=== S3 bottom done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g7cAll
