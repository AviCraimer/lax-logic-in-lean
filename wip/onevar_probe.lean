import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Dec

/-!
# One-variable descent probe — with a sound simplifier

The raw interpolants `itpA p S fitp b Γ g` blow up ~10×/budget-step
(mostly `⊥∧_`, `⊤∨_`, `⊤⊃⊥`, `◯(⊤⊃⊥)` junk), too big for the oracle.
`norm` below applies only EQUIVALENCE-PRESERVING rewrites (Heyting
bottom/top laws + nucleus `◯⊤=⊤`, `◯◯=◯`), so `norm X ≡ X` in PLL and the
descent on normal forms decides the descent on the raw interpolants.  We
also oracle-verify `itpA b ≡ norm (itpA b)` on the small cases as a check.
-/

open PLLFormula
namespace PLLND
namespace OnevarProbe

/-! ## oracle -/
def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C
def entails (X Y : PLLFormula) : Bool := provF 4000 [X] Y
def equivO (X Y : PLLFormula) : Bool := entails X Y && entails Y X

/-! ## sound simplifier (each rewrite a PLL-equivalence) -/
def isTop (X : PLLFormula) : Bool := decide (X = truePLL)
def isBot (X : PLLFormula) : Bool := decide (X = falsePLL)

def simp : PLLFormula → PLLFormula
  | .and a b =>
      let a := simp a; let b := simp b
      if isBot a || isBot b then falsePLL
      else if isTop a then b else if isTop b then a
      else if a = b then a else .and a b
  | .or a b =>
      let a := simp a; let b := simp b
      if isTop a || isTop b then truePLL
      else if isBot a then b else if isBot b then a
      else if a = b then a else .or a b
  | .ifThen a b =>
      let a := simp a; let b := simp b
      if a = b then truePLL
      else if isTop a then b
      else if isTop b then truePLL
      else if isBot a then truePLL
      else .ifThen a b
  | .somehow a =>
      let a := simp a
      if isTop a then truePLL
      else match a with
        | .somehow c => .somehow c        -- ◯◯c ≡ ◯c
        | _ => .somehow a
  | X => X

/-- iterate `simp` to a fixpoint (bounded). -/
def norm : Nat → PLLFormula → PLLFormula
  | 0, X => X
  | n + 1, X => let Y := simp X; if Y = X then X else norm n Y
def nf (X : PLLFormula) : PLLFormula := norm 12 X

def op : PLLFormula := prop "p"
def bx (X : PLLFormula) : PLLFormula := X.somehow
def pp : String := "p"
def fitp : Nat := 40
def wcap : Nat := 130

-- distinguished 1-pv / closed formulae
def u : PLLFormula := (bx op).ifThen op        -- ◯p ⊃ p
def uu : PLLFormula := (bx (bx op)).ifThen op  -- ◯◯p ⊃ p
def nu : PLLFormula := u.ifThen op             -- (◯p⊃p) ⊃ p
def bxu : PLLFormula := bx u                   -- ◯(◯p⊃p)
def bb : PLLFormula := bx falsePLL             -- ◯⊥
def nbb : PLLFormula := bb.ifThen falsePLL     -- ¬◯⊥
def On : PLLFormula := bx nbb                  -- ◯(¬◯⊥)

/-- name a value against known RN(◯,{}) elements. -/
def classify (X : PLLFormula) : String :=
  if equivO X falsePLL then "⊥"
  else if equivO X truePLL then "⊤"
  else if equivO X bb then "◯⊥"
  else if equivO X nbb then "¬◯⊥"
  else if equivO X On then "◯(¬◯⊥)"
  else if equivO X (bb.or nbb) then "◯⊥∨¬◯⊥"
  else if equivO X (nbb.ifThen falsePLL) then "¬¬◯⊥"
  else "OTHER"

/-- Track a budget-indexed interpolant family `mk`: normal forms, per-step
descent, class-trajectory vs the b=1 value, and a LOUD flag if it ever
leaves the b=1 class (a "climb" = a stabilisation failure = counterexample
lead). -/
def track (out : IO.FS.Stream) (label : String) (mk : Nat → PLLFormula)
    (maxB : Nat) : IO Unit := do
  let mut Ns : Array PLLFormula := #[]
  for b in List.range (maxB + 1) do Ns := Ns.push (nf (mk b))
  let wts := (List.range (maxB + 1)).map (fun b => Ns[b]!.weight)
  IO.println s!"  {label}: nfW b=0..{maxB} = {wts}"; out.flush
  let base := Ns[1]!
  let mut climbed := false
  for b in List.range maxB do
    let lo := Ns[b]!; let hi := Ns[b + 1]!
    if lo.weight ≤ wcap ∧ hi.weight ≤ wcap then
      let d := entails hi lo               -- descent  mk(b+1) ⊢ mk b
      let inBase := if base.weight ≤ wcap then equivO hi base else true
      if b ≥ 1 ∧ !inBase then climbed := true
      IO.println s!"    b={b}→{b+1}: DESCENT={d}  in-b1-class={inBase}"; out.flush
    else
      IO.println s!"    b={b}→{b+1}: [skipped: nfW {lo.weight},{hi.weight}]"; out.flush
  let top := Ns[maxB]!
  let cls := if top.weight ≤ wcap then classify top else s!"big({top.weight})"
  let mark := if climbed then "   *** CLIMB — LEAVES b1 CLASS ***" else ""
  IO.println s!"    {label} stabilised = {cls}{mark}"
  out.flush

def probeConfig (name : String) (S : Finset PLLFormula) (Γ : List PLLFormula)
    (g : PLLFormula) (maxB : Nat) : IO Unit := do
  let out ← IO.getStdout
  IO.println s!"### {name}   defect={defect S Γ}"; out.flush
  track out "itpA" (fun b => itpA pp S fitp b Γ g) maxB
  track out "itpE" (fun b => itpE pp S fitp b Γ) maxB

/-- equivalence / descent at an explicit fuel (push past the default). -/
def eqAt (f : Nat) (X Y : PLLFormula) : Bool := provF f [X] Y && provF f [Y] X

def main : IO Unit := do
  let out ← IO.getStdout
  -- X9 focused: does the escape climb STRICTLY continue (real counterexample)
  -- or stall into a stable rich value?
  let fp := falsePLL
  let S : Finset PLLFormula := {fp, bb, nbb, op, bx op}   -- {⊥,◯⊥,¬◯⊥,p,◯p}
  let Γ : List PLLFormula := [nbb]                        -- [¬◯⊥]
  let g := bx op                                          -- ◯p
  IO.println s!"X9  S: ⊥ ◯⊥ ¬◯⊥ p ◯p   Γ=[¬◯⊥]  g=◯p   defect={defect S Γ}"
  out.flush
  let mut As : Array PLLFormula := #[]
  for b in List.range 7 do
    let X := nf (itpA pp S fitp b Γ g)
    As := As.push X
    IO.println s!"  itpA b={b}: nfW={X.weight}"; out.flush
  for b in List.range 6 do
    let lo := As[b]!; let hi := As[b+1]!
    if lo.weight ≤ 700 ∧ hi.weight ≤ 700 then
      let eq := eqAt 12000 lo hi
      let dsc := provF 12000 [hi] lo
      let asc := provF 12000 [lo] hi
      IO.println s!"  b={b}→{b+1}: itpA(b)≡itpA(b+1)?={eq}  DESCENT(b+1⊢b)?={dsc}  ascent?={asc}"
      out.flush
    else
      IO.println s!"  b={b}→{b+1}: [oracle skipped nfW {lo.weight},{hi.weight}]"; out.flush

#eval main

end OnevarProbe
end PLLND
