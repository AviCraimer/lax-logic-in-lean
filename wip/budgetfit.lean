import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# Budget extraction: measuring the room the descent actually needs

Every previous statement of the low-band descent has *assumed* a budget
law and then been probed around its edges:

* `cascade_low_pos_box` assumes `defect S Γ * (|jumpGoals S| + 2) ≤ c`
  — a worst-case product, guessed;
* the July "no-room" reformulation assumed `1 ≤ c` — refuted
  (`wip/ascRefute.lean`);
* "`2 ≤ c`" is the obvious next guess — and it is *still a guess*.

This file replaces guessing by **extraction**, in the sense the repo
already uses for timing (`LaxLogic/PLLConstraints.lean`, after Mendler's
*proofs-as-delays*): treat the budget as an unknown, run the object over
a family of instances, and let the data say what the function is.

Two instruments.

**§1 Shape coverage.**  The budget `b` is read at exactly two clause
branches of `itpE`/`itpA` — the ones driven by a context/space formula of
shape `(A ⊃ B) ⊃ D` or `◯A ⊃ B` (`LaxLogic/PLLG4UITrunc.lean`, lines
252-269 and 270-290).  A probe family containing no formula of either
shape *cannot exercise the budget at all*, whatever else it tests.
`budgetBlind` decides that, and `missingTags` reports which of the eleven
clause branches a family fails to reach.  This is the mechanical form of
the coverage discipline: derive the probe family from the definition's
case split, not from intuition about the lemma.

**§2 Minimal budget.**  For an instance `(S, Γ, g, fuel)` the descent step
is the sequent

    itpA p S fuel (c+1) Γ g ,  itpE p S fuel (c+1) Γ   ⊢   itpA p S fuel c Γ g

(the sharpest instance of `cascade_low_pos_box`: `Δ` the two hypotheses,
`fh = fuel`).  `minBudget` walks `c` upwards and returns the least `c` at
which the two-sided oracle certifies derivability, together with the whole
verdict row, so a non-monotone column would be visible rather than hidden.

The families are chains of budget-gated pieces of growing length: if the
true law is a constant, `minBudget` is flat in the chain length; if it is
a chain-depth measure, `minBudget` tracks it; if it is the assumed
product, it tracks `defect * (|jumpGoals| + 2)`.  The three predictions
are printed side by side with the measurement.

Run: `lake build budgetfit && .lake/build/bin/budgetfit`.
-/

open PLLFormula PLLND PLLND.Search

namespace BudgetFit

/-! ## 1. Shape coverage — which clause branches a family reaches -/

/-- The clause branch a formula drives, as a tag.  The two starred tags
are the **budget-gated** branches: they are the only places where `itpE`
and `itpA` read `b`. -/
def shapeTag : PLLFormula → String
  | .falsePLL => "bot"
  | .prop _ => "atom"
  | .and _ _ => "conj"
  | .or _ _ => "disj"
  | .somehow _ => "box"
  | .ifThen .falsePLL _ => "imp-bot"
  | .ifThen (.prop _) _ => "imp-atom"
  | .ifThen (.and _ _) _ => "imp-conj"
  | .ifThen (.or _ _) _ => "imp-disj"
  | .ifThen (.ifThen _ _) _ => "imp-imp*"
  | .ifThen (.somehow _) _ => "imp-box*"

/-- Every clause branch of the two tables. -/
def allTags : List String :=
  ["bot", "atom", "conj", "disj", "box", "imp-bot", "imp-atom",
   "imp-conj", "imp-disj", "imp-imp*", "imp-box*"]

/-- The branches a family reaches. -/
def coverTags (L : List PLLFormula) : List String := (L.map shapeTag).dedup

/-- The branches it misses. -/
def missingTags (L : List PLLFormula) : List String :=
  allTags.filter (fun t => ¬ (coverTags L).contains t)

/-- **Budget-blindness**: no formula of either budget-gated shape, hence
no instance of the family can distinguish one budget from another.  The
July "Z5" family `{u, u ⊃ r, ◯u}` is blind by this test. -/
def budgetBlind (L : List PLLFormula) : Bool :=
  ¬ ((coverTags L).contains "imp-imp*" || (coverTags L).contains "imp-box*")

/-! ## 2. Predictors -/

/-- `jumpGoals` of `wip/absorb_base.lean`, inlined (that file is not a
lake library target, so it cannot be imported from a probe). -/
def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

/-- The room the kernel currently assumes: `defect · (|jumpGoals| + 2)`. -/
def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

/-- The number of budget-gated pieces in the space — the crude
chain-length predictor. -/
def gatedCount (L : List PLLFormula) : Nat :=
  (L.filter (fun F => shapeTag F == "imp-imp*" || shapeTag F == "imp-box*")).length

/-! ## 3. The descent instance, and its verdict -/

/-- The sharpest instance of the low-band descent at budget `c`. -/
def descHyps (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : List PLLFormula :=
  [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]

def descGoal (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : PLLFormula :=
  itpA p S fuel c Γ g

/-- Three-valued verdict, **countermodel-first**.

Locating a threshold does not need the positive side decided: it needs
the failure region certified and its complement clean.  The battery
sweep (`sweepCert`) is a model check — cheap, and its hits are
`checkB`-certified underivability.  Proof search on these sequents is
the expensive half (the hypotheses are the tables at `c+1`), so it runs
only as a cheap spot-check.

* `prov`   — a proof term was found within the spot-check budget
  (certified derivable);
* `refCert` — a battery countermodel that passes `checkB` (certified
  underivable);
* `clean`  — no countermodel in the battery and no cheap proof:
  *consistent with derivable*, and reported as evidence, not as a
  verdict. -/
inductive V4 | prov | refCert | clean
deriving BEq

def V4.tag : V4 → String
  | .prov => "P" | .refCert => "R!" | .clean => "~"

def cfg : Config := { findBudget := some 20000, emitClosureCap := 0 }

/-- The **focused** configuration: the positive stage reduced to a token
spot-check, so that the (polynomial) battery can be run on instances far
too large for proof search.  Certified failures are what a threshold
measurement needs; a `~` cell here means "no countermodel in the
battery" — the evidence side, not a verdict. -/
def cfgCheap : Config := { findBudget := some 1500, emitClosureCap := 0 }

/-- Countermodel-first verdict on one descent instance. -/
def descVerdictC (cf : Config) (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : V4 :=
  match settleWhy cf (descHyps p S fuel c Γ g) (descGoal p S fuel c Γ g) with
  | .proved _ => .prov
  | .refuted _ _ _ => .refCert
  | .unknown _ => .clean

/-- The default-configuration verdict. -/
def descVerdict (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : V4 :=
  descVerdictC cfg p S fuel c Γ g

/-! ### Guard reachability — coverage, second order

Covering a clause *shape* is not enough.  Each budget-gated branch also
carries **guard conditions**, and `itpE`/`itpA` iterate over the
**context**, not the space: a gated piece sitting in `S` but not in `Γ`
drives nothing until growth puts it there.  Reading the two branches off
`LaxLogic/PLLG4UITrunc.lean`:

* `◯A ⊃ B ∈ Γ` reaches its gate iff `B ∉ Γ`, `B ∈ S` and `◯A ⊃ B ∈ S`;
* `(A ⊃ B) ⊃ D ∈ Γ` reaches its gate iff `D ∉ Γ`, `D ∈ S`,
  `B ⊃ D ∈ Γ` and `(A ⊃ B) ⊃ D ∈ S`.

`gateLive` reports this per context formula.  A family whose gates are
all dead is as uninformative about the budget as a budget-blind one, and
much harder to notice by eye. -/
def gateLive (S : Finset PLLFormula) (Γ : List PLLFormula) :
    List (String × Bool) :=
  Γ.filterMap (fun F => match F with
    | .ifThen (.somehow A) B =>
        some (s!"◯{A.toString}⊃{B.toString}",
          (¬ (Γ.contains B)) && (B ∈ S) && (F ∈ S))
    | .ifThen (.ifThen A B) D =>
        some (s!"({A.toString}⊃{B.toString})⊃{D.toString}",
          (¬ (Γ.contains D)) && (D ∈ S) && (Γ.contains (B.ifThen D)) && (F ∈ S))
    | _ => none)

/-! ## 4. The instance families

Chain `n`: the `◯`-gated pieces `◯a₀ ⊃ a₁, …, ◯aₙ₋₁ ⊃ aₙ` with `a₀ = p`
the eliminated variable, closed under subformulas, plus a goal piece
`(◯aₙ₋₁ ⊃ aₙ) ⊃ z` — the shape the two refutations found fatal at
budget 1.  The context is always the head piece alone, so the remaining
pieces are live growth material. -/

def atomAt : Nat → PLLFormula
  | 0 => prop "p"
  | 1 => prop "r"
  | 2 => prop "s"
  | 3 => prop "t"
  | 4 => prop "u"
  | _ => prop "v"

/-- The `n` chained `◯`-gated pieces. -/
def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

/-- Subformula material the clauses look for. -/
def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

/-- The goal piece: an implication whose antecedent is the last gated
piece. -/
def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

/-- The `⊃⊃`-gated variant of the goal piece, for the other gated
branch. -/
def goalPieceII (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).ifThen (atomAt n))).ifThen (prop "z")

/-- The chain family as a **list** (`Finset.toList` is noncomputable, so
the coverage instrument must read the list, not the space). -/
def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

/-- The `⊃⊃`-chain: `(a₀ ⊃ a₁) ⊃ a₂`, `(a₂ ⊃ a₃) ⊃ a₄`, … -/
def chainPiecesII (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i =>
    ((atomAt (2 * i)).ifThen (atomAt (2 * i + 1))).ifThen (atomAt (2 * i + 2)))

def chainListII (n : Nat) : List PLLFormula :=
  (chainPiecesII n ++ (List.range (2 * n + 1)).map atomAt
    ++ (List.range (2 * n + 1)).map (fun i => (atomAt i).ifThen (atomAt (i + 1)))
    ++ [prop "z"]).dedup

def chainSpaceII (n : Nat) : Finset PLLFormula := (chainListII n).toFinset

/-! ## 5. The sweep -/

def pf (F : PLLFormula) : String := F.toString

/-- Size cap: skip an instance whose target table exceeds this weight,
rather than grinding on it silently. -/
def WEIGHT_CAP : Nat := 4000

/-- The verdict row for one instance across budgets `0 … cmax`, and the
least certified budget.  Prints as it goes (a buffered probe that dies
mid-run tells you nothing). -/
def rowIOC (out : IO.FS.Stream) (cf : Config) (cap : Nat)
    (p : String) (S : Finset PLLFormula) (fuel : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) (cmax : Nat) :
    IO (String × Option Nat) := do
  let mut cells : List (Nat × V4) := []
  for c in List.range (cmax + 1) do
    let tgt := descGoal p S fuel c Γ g
    let w := tgt.weight
    if w > cap then
      out.putStrLn s!"      c{c}: SKIP (target weight {w} > {cap})"
      out.flush
      cells := cells ++ [(c, V4.clean)]
    else
      let t0 ← IO.monoMsNow
      let v ← IO.lazyPure (fun _ => descVerdictC cf p S fuel c Γ g)
      let _ ← IO.lazyPure (fun _ => v.tag.length)
      let t1 ← IO.monoMsNow
      out.putStrLn s!"      c{c}: {v.tag}  (target weight {w}, {t1 - t0} ms)"
      out.flush
      cells := cells ++ [(c, v)]
  let s := String.intercalate " " (cells.map (fun (c, v) => s!"c{c}:{v.tag}"))
  -- the threshold: one past the last certified failure
  let lastFail := (cells.filter (fun (_, v) => v == V4.refCert)).reverse.head?.map Prod.fst
  let m := lastFail.map (· + 1)
  return (s, m)

/-- The default-configuration row. -/
def rowIO (out : IO.FS.Stream) (p : String) (S : Finset PLLFormula) (fuel : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) (cmax : Nat) :
    IO (String × Option Nat) :=
  rowIOC out cfg WEIGHT_CAP p S fuel Γ g cmax

def showOpt : Option Nat → String
  | none => "0 (no failure at any probed budget)"
  | some k => toString k

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== budget extraction: what room does the descent actually need? =="
  pl ""
  pl "-- §1 coverage check on the probe families --"
  let z5 : List PLLFormula :=
    [prop "u", (prop "u").ifThen (prop "r"), (prop "u").somehow]
  pl s!"July Z5 family {z5.map pf}:"
  pl s!"   covers {coverTags z5}"
  pl s!"   misses {missingTags z5}"
  pl s!"   BUDGET-BLIND = {budgetBlind z5}"
  for n in [1, 2, 3] do
    let L := chainList n
    pl s!"chain{n} space (|S| = {L.length}):"
    pl s!"   covers {coverTags L}"
    pl s!"   misses {missingTags L}"
    pl s!"   BUDGET-BLIND = {budgetBlind L}"
  pl ""
  pl "-- §2 minimal certified budget, ◯-gated chains --"
  pl "   (goal = the ⊃◯-antecedent implication, the shape refuted at c=1)"
  for n in [1, 2, 3] do
    let L := chainList n
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    let g := goalPiece n
    let dfc := defect S Γ
    let jg := (jumpGoals S).card
    pl s!"chain{n}: |S|={L.length} defect={dfc} |jumpGoals|={jg} \
gated={gatedCount L} PRODUCT-law={roomProduct S Γ}"
    for fuel in [n + 2, n + 3] do
      pl s!"   fuel={fuel}:"
      let t0 ← IO.monoMsNow
      let (s, m) ← rowIO out "p" S fuel Γ g 3
      let t1 ← IO.monoMsNow
      pl s!"   fuel={fuel}  {s}   threshold={showOpt m}   ({t1 - t0} ms)"
  pl ""
  pl "-- §3 same chains, safe goals (atom / box) --"
  for n in [1, 2, 3] do
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    for (nm, g) in [("atom", atomAt n), ("box", (atomAt n).somehow)] do
      pl s!"chain{n} goal={nm}:"
      let (s, m) ← rowIO out "p" S (n + 2) Γ g 3
      pl s!"chain{n} goal={nm}: {s}   threshold={showOpt m}"
  pl ""
  pl "-- §4 ⊃⊃-gated chains --"
  for n in [1, 2] do
    let L := chainListII n
    let S := chainSpaceII n
    let Γ := [chainPiecesII n |>.headD (prop "p")]
    let g := goalPieceII (2 * n)
    let dfc := defect S Γ
    let jg := (jumpGoals S).card
    pl s!"chainII{n}: |S|={L.length} defect={dfc} |jumpGoals|={jg} \
gated={gatedCount L} PRODUCT-law={roomProduct S Γ}"
    let (s, m) ← rowIO out "p" S (n + 3) Γ g 3
    pl s!"   {s}   threshold={showOpt m}"
  pl ""
  pl "-- §5 FOCUSED: the cells §2 had to skip, battery-only --"
  for n in [2, 3, 4] do
    let L := chainList n
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    let g := goalPiece n
    let dfc := defect S Γ
    let jg := (jumpGoals S).card
    pl s!"chain{n}: |S|={L.length} defect={dfc} |jumpGoals|={jg} \
gated={gatedCount L} PRODUCT-law={roomProduct S Γ}  gateLive={gateLive S Γ}"
    let t0 ← IO.monoMsNow
    let (s, m) ← rowIOC out cfgCheap 400000 "p" S (n + 2) Γ g 3
    let t1 ← IO.monoMsNow
    pl s!"   fuel={n + 2}  {s}   threshold={showOpt m}   ({t1 - t0} ms)"
  pl ""
  pl "-- §6 the ⊃⊃ gate, guard REPAIRED (B ⊃ D put into the context) --"
  for n in [1, 2] do
    let S := chainSpaceII n
    let head := chainPiecesII n |>.headD (prop "p")
    -- the guard the plain family missed: (A⊃B)⊃D needs B⊃D in Γ
    let Γ := [head, (atomAt (2 * n - 1)).ifThen (atomAt (2 * n))]
    let g := goalPieceII (2 * n)
    pl s!"chainII{n}: |S|={(chainListII n).length} defect={defect S Γ} \
|jumpGoals|={(jumpGoals S).card} PRODUCT-law={roomProduct S Γ}  \
gateLive={gateLive S Γ}"
    let (s, m) ← rowIOC out cfgCheap 400000 "p" S (n + 3) Γ g 3
    pl s!"   {s}   threshold={showOpt m}"
  pl ""
  pl "== done =="

end BudgetFit

def main : IO Unit := BudgetFit.main
