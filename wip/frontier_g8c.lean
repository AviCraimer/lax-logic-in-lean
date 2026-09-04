import frontier_g8

/-!
# ROUND 8, PHASE 1c — the goal-row obligation AT THE TWO INHERITED WITNESSES

Two-sided instance checks (`refute?` full battery first, then a bounded
positive pass, the `frontier_g7c.lean` pattern) of the round-8 candidate
sequents at the two spaces the campaign's negatives live at:

* **`Skb`/`Gk`** (July's jump witness, `wip/round4probe3.lean`): the space
  whose UNBOXED same-context descent is kernel-refuted
  (`AscRefute.not_roomFreeDescent`) and whose elevated goal-row landing is
  kernel-refuted (`Round7Pin.goalrow_landing_refuted_elev1/_elev2`).
  `D = gk = (◯r ⊃ s) ⊃ t` is jump-shaped compound unboxed — the residue
  shape proper.  Configuration: `fs = ft = 4`, `b = 2`, `c = 1`,
  ambient `E@(4, 3)(Gk)` (the `CompProd` walk position).

* **`S3`/`Γ3`** (the round-6 nest witness): `D = a⊃b` compound unboxed
  (`◯(a⊃b) ∈ S3`), room floor `b = 4`, budget-active fuels `fs = ft = 5`,
  `c ∈ {3, 1}`.

The control row re-runs the round-7 pinned landing refutation
(`[srcU, ambE3] ⊢ tgtU`, expect `R!`) so a quiet verdict on the candidates
is calibrated silence.

Durable output: `wip/frontier_g8.txt`.
-/

open PLLFormula PLLND PLLND.Search FrontierSampler

namespace PLLND
namespace Frontier

/-- Countermodel-first, then bounded positive — one report line each. -/
def runInst (nm : String) (prems : List PLLFormula) (tgt : PLLFormula)
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
          -- the found derivation, as its rule tree (truncated): phase 2
          -- reads the mechanics off it
          let s ← IO.lazyPure (fun _ => t.pretty)
          g8Ledger.comment s!"  TERM {s.take 6000}"
      | none => g8Ledger.comment s!"  ~ (quiet, unproved at {pbudget})"

/-! ## The `Skb`/`Gk` witness (`fs = ft = 4`, `b = 2`, `c = 1`, `f = 3`) -/

open Round4Probe3 AscRefute in
def g8cSkb : IO Unit := do
  let amb : PLLFormula := itpE "p" Skb 4 3 Gk          -- Round7Pin.ambE3
  let gsrcK : PLLFormula :=
    ((itpE "p" Skb 3 1 Gk).ifThen (itpA "p" Skb 3 2 Gk gk)).somehow
  let wK : PLLFormula := itpA "p" Skb 4 1 Gk gk.somehow  -- = tgtB
  let xK : PLLFormula :=
    ((itpE "p" Skb 3 0 Gk).ifThen (itpA "p" Skb 3 1 Gk gk)).somehow
  let compSK : PLLFormula :=
    ((itpE "p" Skb 4 2 Gk).ifThen (itpA "p" Skb 4 2 Gk gk.somehow)).somehow
  let pK : PLLFormula :=
    ((itpE "p" Skb 4 1 Gk).ifThen (itpA "p" Skb 4 1 Gk gk.somehow)).somehow
  -- the γ-clause of `Gk` is `◯p ⊃ r`: ant = p, head = r
  let eK : PLLFormula :=
    (((itpE "p" Skb 3 0 Gk).ifThen
        (itpA "p" Skb 3 0 Gk (prop "p").somehow)).somehow).and
      (itpA "p" Skb 3 1 (prop "r" :: Gk) gk.somehow)
  g8cLedgerBanner "Skb/Gk witness (fs=ft=4 b=2 c=1)"
  runInst "Skb-CTRL (round-7 landing, expect R!) [srcU, ambE3] |- tgtU"
    [srcU, amb] tgtU 40000
  runInst "Skb-W  [gsrc, amb] |- tgt@1" [gsrcK, amb] wK 40000
  runInst "Skb-X  [gsrc, amb] |- gclause@1" [gsrcK, amb] xK 40000
  runInst "Skb-P  [compS, amb] |- comp@1" [compSK, amb] pK 40000
  runInst "Skb-E  [gsrc, amb] |- genv@1" [gsrcK, amb] eK 40000
  -- gap 2 (b = 3, c = 1): the configuration where a fresh-antecedent guard
  -- ascent inside the goal-row case is most budget-starved.  `gk`'s
  -- antecedent `◯r ⊃ s` is NOT in `Gk`, so the inner goal row of the fired
  -- `D`-table grows the context — the §61(f)(i) shape with no room in the
  -- sequent.
  let amb4 : PLLFormula := itpE "p" Skb 4 4 Gk
  let gsrcK3 : PLLFormula :=
    ((itpE "p" Skb 3 2 Gk).ifThen (itpA "p" Skb 3 3 Gk gk)).somehow
  let compSK3 : PLLFormula :=
    ((itpE "p" Skb 4 3 Gk).ifThen (itpA "p" Skb 4 3 Gk gk.somehow)).somehow
  g8cLedgerBanner "Skb/Gk witness, gap 2 (fs=ft=4 b=3 c=1)"
  runInst "Skb-W3 [gsrc@3, amb@4] |- tgt@1" [gsrcK3, amb4] wK 40000
  runInst "Skb-X3 [gsrc@3, amb@4] |- gclause@1" [gsrcK3, amb4] xK 40000
  runInst "Skb-P3 [compS@3, amb@4] |- comp@1" [compSK3, amb4] pK 40000
  -- the DELIMITED INNER OBLIGATION of the committed route at the fresh
  -- inner goal row (`gk`'s antecedent `◯r ⊃ s ∉ Gk`): from the source's
  -- fresh goal disjunct (inner fuel 2, budget b) and the ambient, the
  -- target's fresh goal disjunct at budget c — the step whose room-free
  -- financing is the suspected wall (`cascade_main_bf` pays it with
  -- `hroomE`, the room the walk does not have).
  let freshRow (bb : Nat) : PLLFormula :=
    (itpE "p" Skb 2 bb (((prop "r").somehow).ifThen (prop "s") :: Gk)).ifThen
      (itpA "p" Skb 2 bb (((prop "r").somehow).ifThen (prop "s") :: Gk) (prop "t"))
  g8cLedgerBanner "Skb/Gk fresh-antecedent inner row (inner fuel 2)"
  runInst "Skb-F  [freshRow@2, amb@3] |- freshRow@1"
    [freshRow 2, amb] (freshRow 1) 40000
  runInst "Skb-F3 [freshRow@3, amb@4] |- freshRow@1"
    [freshRow 3, amb4] (freshRow 1) 40000
  -- the UNBOXED descent at the GROWN context `r :: Gk` (defect one below
  -- July's refuted `Gk` instance): the γ-row-within-goal-row landing needs
  -- exactly this, with the grown ambient.  July's `Mk` refutation lives at
  -- `Gk` itself and says nothing here; an `R!` kills the inner landing at
  -- the witness, a `P` finances it.
  let rGk : List PLLFormula := prop "r" :: Gk
  g8cLedgerBanner "Skb/Gk grown-context unboxed descent (r::Gk, defect-1)"
  runInst "Skb-U  [A@(4,2)(r::Gk,gk), E@(4,3)(r::Gk)] |- A@(4,1)(r::Gk,gk)"
    [itpA "p" Skb 4 2 rGk gk, itpE "p" Skb 4 3 rGk]
    (itpA "p" Skb 4 1 rGk gk) 40000
  runInst "Skb-U0 [A@(4,2)(r::Gk,gk), E@(4,3)(rGk), amb@3] |- A@(4,1)(r::Gk,gk)"
    [itpA "p" Skb 4 2 rGk gk, itpE "p" Skb 4 3 rGk, amb]
    (itpA "p" Skb 4 1 rGk gk) 40000
where
  g8cLedgerBanner (s : String) : IO Unit :=
    g8Ledger.comment s!"=== round-8 witness: {s} ==="

/-! ## The `S3`/`Γ3` witness (`fs = ft = 5`, `b = 4`, `c ∈ {3, 1}`, `f = 4`)

`S3`/`Γ3` cloned locally exactly as in `frontier_g7c.lean` (`Round6` is not
imported by the frontier stack). -/

def s3l' : List PLLFormula :=
  [ ((prop "a").ifThen (prop "b")).somehow.somehow.ifThen (prop "c"),
    ((prop "a").ifThen (prop "b")).somehow.somehow,
    ((prop "a").ifThen (prop "b")).somehow,
    (prop "a").ifThen (prop "b"),
    prop "a", prop "b", prop "c" ]

def g3' : List PLLFormula := s3l'.filter (fun F => F != prop "c")

def s3F' : Finset PLLFormula := s3l'.toFinset

/-- The compound unboxed body at `S3`: `a ⊃ b` (`◯(a⊃b) ∈ S3`). -/
def aib : PLLFormula := (prop "a").ifThen (prop "b")

def g8cS3 : IO Unit := do
  let amb : PLLFormula := itpE pv s3F' 5 5 g3'
  let gsrc3 : PLLFormula :=
    ((itpE pv s3F' 4 3 g3').ifThen (itpA pv s3F' 4 4 g3' aib)).somehow
  let w3 (c : Nat) : PLLFormula := itpA pv s3F' 5 c g3' aib.somehow
  let x3 (c : Nat) : PLLFormula :=
    ((itpE pv s3F' 4 (c - 1) g3').ifThen (itpA pv s3F' 4 c g3' aib)).somehow
  let compS3 : PLLFormula :=
    ((itpE pv s3F' 5 4 g3').ifThen (itpA pv s3F' 5 4 g3' aib.somehow)).somehow
  let p3 (c : Nat) : PLLFormula :=
    ((itpE pv s3F' 5 c g3').ifThen (itpA pv s3F' 5 c g3' aib.somehow)).somehow
  g8Ledger.comment "=== round-8 witness: S3/Γ3 (fs=ft=5 b=4) ==="
  runInst "S3-W c=3  [gsrc, amb] |- tgt@3" [gsrc3, amb] (w3 3) 40000
  runInst "S3-W c=1  [gsrc, amb] |- tgt@1" [gsrc3, amb] (w3 1) 40000
  runInst "S3-X c=3  [gsrc, amb] |- gclause@3" [gsrc3, amb] (x3 3) 40000
  runInst "S3-X c=1  [gsrc, amb] |- gclause@1" [gsrc3, amb] (x3 1) 40000
  runInst "S3-P c=3  [compS, amb] |- comp@3" [compS3, amb] (p3 3) 40000
  runInst "S3-P c=1  [compS, amb] |- comp@1" [compS3, amb] (p3 1) 40000

def g8cAll : IO Unit := do
  g8cSkb
  g8cS3
  g8Ledger.comment "=== round-8 witness checks done ==="

end Frontier
end PLLND

#eval PLLND.Frontier.g8cAll
