import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLSearch

/-!
# The two blocked branches, as sequents handed to the oracle

PROGRESS §85 localises the residue of the descent to two environment-clause
branches at target budget `1`.  Both are *branch obligations*, not the
descent itself: each has the source disjunct and the ambient as hypotheses,
plus whatever the defect tier supplies, and has to reach **some** disjunct of
the target table.  Written out they are ordinary sequents, so the two-sided
oracle can adjudicate them — and if one is derivable, proof search may find
the derivation, which is then a blueprint for the Lean proof.

## Branch 1 — the γ-clause's boxed disjunct (`GammaPairFloorBox`)

With `◯A ⊃ B ∈ Γ ∩ S`, `B ∈ S ∖ Γ`, at target budget `1`:

    E@2(Γ)                        (the ambient)
    ◯( E@1(Γ) ⇢ A@1(Γ, ◯A) )      (the source's boxed first component)
    A@1(B::Γ, C)                  (its second component, already descended
                                   by the defect tier — `B::Γ` has strictly
                                   smaller defect)
    ────────────────────────────
    ⋁ itpAoth p S fl 1 Γ C        (the target table, any disjunct)

The matching target disjunct would be
`◯(E@0(Γ) ⇢ A@0(Γ,◯A)) ∧ A@1(B::Γ,C)`, whose first component needs the
descent to budget `0` at the boxed goal `◯A` — certified false as a plain
statement (`wip/ascprobe.lean`).  So if this sequent is derivable at all, it
is derivable through some *other* disjunct, and that is exactly what needs
finding.

## Branch 2 — the same branch's plain disjunct (`GammaPairFloorA`)

    E@2(Γ),  A@1(Γ, A),  A@1(B::Γ, C)  ⊢  ⋁ itpAoth p S fl 1 Γ C

Here the matching target disjunct needs `A@0(Γ,A)` — the descent to budget
`0` at the *unboxed* jump goal `A`, which `wip/jumpprobe.lean` proves by
search at budget `0`.  So this one is expected to go through; it is included
as a control, to check that the harness is asking the right question.

## Branch 3 — the jump-clause pair (`JumpPairFloor`)

    E@2(Γ),  E@1(Γ) ⇢ A@1(Γ, A⊃B),  A@1(D::Γ, C)  ⊢  ⋁ itpAoth p S fl 1 Γ C

with `(A⊃B)⊃D ∈ Γ ∩ S`, `B⊃D ∈ Γ`, `D ∈ S ∖ Γ`.

Run: `lake build sealprobe && .lake/build/bin/sealprobe`.
-/

open PLLFormula PLLND PLLND.Search

namespace SealProbe

def atomAt : Nat → PLLFormula
  | 0 => prop "p" | 1 => prop "r" | 2 => prop "s" | 3 => prop "t"
  | 4 => prop "u" | 5 => prop "v" | _ => prop "w"

def chainPieces (n : Nat) : List PLLFormula :=
  (List.range n).map (fun i => ((atomAt i).somehow).ifThen (atomAt (i + 1)))

def chainClosure (n : Nat) : List PLLFormula :=
  (List.range (n + 1)).flatMap (fun i => [atomAt i, (atomAt i).somehow])

def goalPiece (n : Nat) : PLLFormula :=
  (((atomAt (n - 1)).somehow).ifThen (atomAt n)).ifThen (prop "z")

def chainList (n : Nat) : List PLLFormula :=
  (chainPieces n ++ chainClosure n ++ [goalPiece n, prop "z"]).dedup

def chainSpace (n : Nat) : Finset PLLFormula := (chainList n).toFinset

/-- The γ-branch obligation, boxed disjunct. -/
def branchBoxed (p : String) (S : Finset PLLFormula) (F fl : Nat)
    (Γ : List PLLFormula) (A B C : PLLFormula) : List PLLFormula × PLLFormula :=
  ([ itpE p S (fl + 1) 2 Γ,
     (((itpE p S F 1 Γ).ifThen (itpA p S F 1 Γ A.somehow)).somehow),
     itpA p S F 1 (B :: Γ) C ],
   orAll (itpAoth p S fl 1 Γ C))

/-- The γ-branch obligation, plain disjunct (the control). -/
def branchPlain (p : String) (S : Finset PLLFormula) (F fl : Nat)
    (Γ : List PLLFormula) (A B C : PLLFormula) : List PLLFormula × PLLFormula :=
  ([ itpE p S (fl + 1) 2 Γ,
     itpA p S F 1 Γ A,
     itpA p S F 1 (B :: Γ) C ],
   orAll (itpAoth p S fl 1 Γ C))

def cfgOf (bud cap : Nat) : Config :=
  { findBudget := some bud, emitClosureCap := cap }

def verdictStr (cf : Config) (hyps : List PLLFormula) (goal : PLLFormula) :
    String :=
  match settleWhy cf hyps goal with
  | .proved _ => "PROVED"
  | .refuted _ _ _ => "REFUTED!"
  | .unknown (.budgetExhausted k) => s!"~ (search budget {k} exhausted)"
  | .unknown (.closureTooBig sz cap) => s!"~ (closure {sz} > cap {cap})"
  | .unknown .allStagesMissed => "~ (every stage ran, none certified)"

def run (out : IO.FS.Stream) (nm : String) (hyps : List PLLFormula)
    (goal : PLLFormula) : IO Unit := do
  for (bud, cap) in [(20000, 0), (200000, 0), (200000, 14)] do
    let t0 ← IO.monoMsNow
    let v ← IO.lazyPure (fun _ => verdictStr (cfgOf bud cap) hyps goal)
    let _ ← IO.lazyPure (fun _ => v.length)
    let t1 ← IO.monoMsNow
    out.putStrLn s!"    {nm}  find={bud} emitCap={cap}: {v}  \
(goal weight {goal.weight}, {t1 - t0} ms)"
    out.flush

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== the blocked branch obligations, as sequents =="
  pl ""
  for n in [2, 3] do
    let S := chainSpace n
    let Γ := [chainPieces n |>.headD (prop "p")]
    -- the γ-clause in Γ is ◯a₀ ⊃ a₁, so A = a₀ and B = a₁
    let A := atomAt 0
    let B := atomAt 1
    let F := n + 2
    let fl := n + 2
    pl s!"chain{n}: Γ = {Γ.map (fun F => F.toString)}, γ-clause ◯{A.toString} ⊃ {B.toString}"
    -- goals C worth trying: the space's own goal piece, an atom, a boxed atom
    let goals : List (String × PLLFormula) :=
      [ ("z", prop "z"),
        (s!"a{n}", atomAt n),
        (s!"◯a{n}", (atomAt n).somehow),
        ("goalPiece", goalPiece n) ]
    for (cn, C) in goals do
      pl s!"  C = {cn} = {C.toString}"
      let (h1, g1) := branchBoxed "p" S F fl Γ A B C
      run out "BOXED (GammaPairFloorBox)" h1 g1
      let (h2, g2) := branchPlain "p" S F fl Γ A B C
      run out "PLAIN (GammaPairFloorA, control)" h2 g2
  pl ""
  pl "== done =="

end SealProbe

def main : IO Unit := SealProbe.main
