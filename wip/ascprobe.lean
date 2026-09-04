import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# Does the budget boundary MOVE with the size of the space?

Two statements are known false at budget `1` and not known false above it:

* the **ambient-relative existential ascent** (`AmbGuardAscent` of
  `wip/cascadeBox.lean`, refuted at `c = 1` in `wip/ascRefute.lean` §1)

      E@(c+1)(Γ),  E@c(X::Γ)   ⊢   E@(c+1)(X::Γ)        (X ∈ S ∖ Γ)

* the **descent** itself (refuted at `c = 1` in `wip/ascRefute.lean` §2)

      A@(c+1)(Γ,g),  E@(c+1)(Γ)   ⊢   A@c(Γ,g).

Both refutations live on a chain of two `◯`-gated pieces.  The question
this file measures is the one that decides whether a *constant* budget law
is possible at all:

> does the failure boundary stay at `1` as the chain grows, or does it
> climb with the chain length?

If it climbs, no constant law can work and the room requirement really is
a size measure (the tower's assumed `defect · (|jumpGoals| + 2)`, or
something like it).  If it stays flat, a constant law is consistent with
the data and the ledger is an over-estimate.

`wip/budgetfit.lean` answered this for the descent at *one* goal shape
(the `⊃◯`-antecedent implication): flat at `2` for chains of length
2, 3, 4.  This file extends the measurement in the two directions that
matter for the rebuild:

* **§2 the ascent**, which `wip/budgetfit.lean` never probed at all, at
  every position of `X` along the chain;
* **§3 the descent at jump goals** — the goals a budget-gated clause puts
  in first-component position (`A`, `◯A` from `◯A ⊃ B ∈ S`; `A ⊃ B` from
  `(A⊃B)⊃D ∈ S`).  These are exactly the goals the descent recurses into,
  so their boundary is the one that governs the recursion.

Countermodel-first throughout, as in `wip/budgetfit.lean`: `R!` is a
`checkB`-certified failure, `P` a found proof, `~` neither (evidence, not
a verdict).  A boundary is read off the certified failures alone.

Run: `lake build ascprobe && .lake/build/bin/ascprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace AscProbe

/-! ## 1. Instruments (shared with `wip/budgetfit.lean`, copied because
neither file is a lake library target) -/

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

def coverTags (L : List PLLFormula) : List String := (L.map shapeTag).dedup

def budgetBlind (L : List PLLFormula) : Bool :=
  ¬ ((coverTags L).contains "imp-imp*" || (coverTags L).contains "imp-box*")

/-- Which budget-gated clauses of `Γ` actually reach their gate.  The
tables iterate over the *context*, so a gated piece in `S ∖ Γ` drives
nothing. -/
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

def liveCount (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  ((gateLive S Γ).filter (fun (_, b) => b)).length

def jumpGoals (S : Finset PLLFormula) : Finset PLLFormula :=
  S.biUnion (fun F => match F with
    | .ifThen (.ifThen A B) _ => {A.ifThen B}
    | .ifThen (.somehow A) _ => {A, A.somehow}
    | _ => ∅)

def roomProduct (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  defect S Γ * ((jumpGoals S).card + 2)

inductive V4 | prov | refCert | clean
deriving BEq

def V4.tag : V4 → String
  | .prov => "P" | .refCert => "R!" | .clean => "~"

/-- Countermodel-first, positive side a token spot-check: the failure
region is the cheap half and is what a boundary measurement needs. -/
def cfgCheap : Config := { findBudget := some 1500, emitClosureCap := 0 }

def verdict (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) : V4 :=
  match settleWhy cf hyps goal with
  | .proved _ => .prov
  | .refuted _ _ _ => .refCert
  | .unknown _ => .clean

/-! ## 2. The two statements, as sequents -/

/-- The ambient-relative existential ascent at budget `c`, exactly as
`AmbGuardAscent` instantiates it (`wip/cascadeBox.lean`): ambient at the
ungrown context and *one fuel higher*, low value at the grown context. -/
def ascHyps (p : String) (S : Finset PLLFormula) (fl c : Nat)
    (Γ : List PLLFormula) (X : PLLFormula) : List PLLFormula :=
  [itpE p S (fl + 1) (c + 1) Γ, itpE p S fl c (X :: Γ)]

def ascGoal (p : String) (S : Finset PLLFormula) (fl c : Nat)
    (Γ : List PLLFormula) (X : PLLFormula) : PLLFormula :=
  itpE p S fl (c + 1) (X :: Γ)

/-- The descent at budget `c`, sharpest instance. -/
def descHyps (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : List PLLFormula :=
  [itpA p S fuel (c + 1) Γ g, itpE p S fuel (c + 1) Γ]

def descGoal (p : String) (S : Finset PLLFormula) (fuel c : Nat)
    (Γ : List PLLFormula) (g : PLLFormula) : PLLFormula :=
  itpA p S fuel c Γ g

/-! ## 3. Families -/

def atomAt : Nat → PLLFormula
  | 0 => prop "p"
  | 1 => prop "r"
  | 2 => prop "s"
  | 3 => prop "t"
  | 4 => prop "u"
  | 5 => prop "v"
  | _ => prop "w"

/-- The `n` chained `◯`-gated pieces `◯aᵢ ⊃ aᵢ₊₁`, `a₀ = p`. -/
def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

/-- The `⊃⊃`-gated chain, with the `B ⊃ D` guard material present. -/
def chainPiecesII (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i =>
    ((atomAt (2 * i)).ifThen (atomAt (2 * i + 1))).ifThen (atomAt (2 * i + 2)))

def chainListII (n : Nat) : List PLLFormula :=
  (chainPiecesII n ++ (List.range (2 * n + 1)).map atomAt
    ++ (List.range (2 * n + 1)).map (fun i => (atomAt i).ifThen (atomAt (i + 1)))
    ++ [prop "z"]).dedup

def chainSpaceII (n : Nat) : Finset PLLFormula := (chainListII n).toFinset

/-- The jump goals of the `◯`-chain, as a list: `aᵢ` and `◯aᵢ` for each
gated piece `◯aᵢ ⊃ aᵢ₊₁`, plus the `⊃`-jump goal of the goal piece. -/
def chainJumpGoals (n : Nat) : List (String × PLLFormula) :=
  ((List.range n).flatMap (fun i =>
      [(s!"a{i}", atomAt i), (s!"◯a{i}", (atomAt i).somehow)]))
  ++ [("last⊃", ((atomAt (n - 1)).somehow).ifThen (atomAt n))]

/-! ## 4. The sweep -/

def WEIGHT_CAP : Nat := 400000

/-- One row: verdicts at budgets `0 … cmax`, printed as they land, plus
the boundary (one past the last certified failure). -/
def row (out : IO.FS.Stream) (cf : Config)
    (hyps : Nat → List PLLFormula) (goal : Nat → PLLFormula)
    (cmax : Nat) : IO (String × Option Nat) := do
  let mut cells : List (Nat × V4) := []
  for c in List.range (cmax + 1) do
    let g := goal c
    let w := g.weight
    if w > WEIGHT_CAP then
      out.putStrLn s!"        c{c}: SKIP (goal weight {w})"
      out.flush
      cells := cells ++ [(c, V4.clean)]
    else
      let t0 ← IO.monoMsNow
      let v ← IO.lazyPure (fun _ => verdict cf (hyps c) g)
      let _ ← IO.lazyPure (fun _ => v.tag.length)
      let t1 ← IO.monoMsNow
      out.putStrLn s!"        c{c}: {v.tag}  (goal weight {w}, {t1 - t0} ms)"
      out.flush
      cells := cells ++ [(c, v)]
  let s := String.intercalate " " (cells.map (fun (c, v) => s!"c{c}:{v.tag}"))
  let lastFail := (cells.filter (fun (_, v) => v == V4.refCert)).reverse.head?.map Prod.fst
  return (s, lastFail.map (· + 1))

def showOpt : Option Nat → String
  | none => "0 (no certified failure at any probed budget)"
  | some k => toString k

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== does the budget boundary move with the size of the space? =="
  pl ""

  pl "-- §1 the ambient-relative existential ascent, X at each chain position --"
  pl "   hyps: E@(c+1)(Γ) [fuel fl+1],  E@c(X::Γ) [fuel fl]"
  pl "   goal: E@(c+1)(X::Γ) [fuel fl]"
  for n in [2, 3, 4] do
    let L := chainList n
    let S := chainSpace n
    let pieces := chainPieces n
    pl s!"chain{n}: |S|={L.length} |jumpGoals|={(jumpGoals S).card} \
blind={budgetBlind L}"
    -- X = piece k, Γ = the first k pieces (so Γ ⊆ S, X ∈ S ∖ Γ)
    for k in List.range n do
      let Γ := pieces.take k
      let X := pieces.getD k (prop "p")
      if Γ.isEmpty then
        pl s!"   k={k}: Γ=[] X={X.toString}  (defect={defect S (X :: Γ)})"
      else
        pl s!"   k={k}: Γ={Γ.map (fun F => F.toString)} X={X.toString}  \
liveGates(X::Γ)={liveCount S (X :: Γ)} defect={defect S (X :: Γ)}"
      let fl := n + 2
      let (s, m) ← row out cfgCheap
        (fun c => ascHyps "p" S fl c Γ X) (fun c => ascGoal "p" S fl c Γ X) 3
      pl s!"   k={k}  {s}   boundary={showOpt m}"
  pl ""

  pl "-- §2 the ascent on the ⊃⊃-gated chain --"
  for n in [1, 2] do
    let L := chainListII n
    let S := chainSpaceII n
    let pieces := chainPiecesII n
    pl s!"chainII{n}: |S|={L.length} |jumpGoals|={(jumpGoals S).card}"
    for k in List.range n do
      -- keep the (A⊃B)⊃D guard material B⊃D in the context
      let Γ := pieces.take k ++ (List.range (2 * n + 1)).map
        (fun i => (atomAt i).ifThen (atomAt (i + 1)))
      let X := pieces.getD k (prop "p")
      pl s!"   k={k}: |Γ|={Γ.length} X={X.toString}  \
liveGates(X::Γ)={liveCount S (X :: Γ)}"
      let fl := n + 3
      let (s, m) ← row out cfgCheap
        (fun c => ascHyps "p" S fl c Γ X) (fun c => ascGoal "p" S fl c Γ X) 3
      pl s!"   k={k}  {s}   boundary={showOpt m}"
  pl ""

  pl "-- §3 the descent at JUMP GOALS (the goals the recursion enters) --"
  for n in [2, 3] do
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    pl s!"chain{n}: defect={defect S Γ} |jumpGoals|={(jumpGoals S).card} \
PRODUCT-law={roomProduct S Γ}  liveGates={liveCount S Γ}"
    for (nm, g) in chainJumpGoals n do
      pl s!"   goal={nm} = {g.toString}"
      let (s, m) ← row out cfgCheap
        (fun c => descHyps "p" S (n + 2) c Γ g)
        (fun c => descGoal "p" S (n + 2) c Γ g) 3
      pl s!"   goal={nm}  {s}   boundary={showOpt m}"
  pl ""
  pl "== done =="

end AscProbe

def main : IO Unit := AscProbe.main
