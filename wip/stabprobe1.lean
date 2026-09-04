import LaxLogic.PLLG4UITrunc

/-! Adversarial stabilization probe (falsification attempt for UI).

If PLL failed uniform interpolation in the S4 manner, some context
family should make the approximant chain `interE p f Γ` strictly
descend (⊣⊢) without bound as `f` grows.  Families below iterate the
gap-theorem pattern — the known worst case for this project — and
◯/⊃ alternations.  `(0, 0)` at level `f` = stabilized by `f`
(algebra-zoo evidence); a strictly positive second component that
persists across all tested fuels = the danger signal. -/

open PLLFormula
namespace PLLND

structure AlgModel where
  meet : Nat → Nat → Nat
  join : Nat → Nat → Nat
  imp  : Nat → Nat → Nat
  bot  : Nat
  top  : Nat
  box  : Nat → Nat
  elems : List Nat

def chain3 (j : Nat → Nat) : AlgModel :=
  ⟨min, max, fun x y => if x ≤ y then 2 else y, 0, 2, j, [0,1,2]⟩

def diamond (j : Nat → Nat) : AlgModel :=
  ⟨(· &&& ·), (· ||| ·), fun x y => (3 ^^^ x) ||| y, 0, 3, j, [0,1,2,3]⟩

def zoo : List AlgModel :=
  [chain3 id, chain3 (max · 1), chain3 (fun x => if x = 0 then 0 else 2),
   chain3 (fun _ => 2),
   diamond id, diamond (· ||| 1), diamond (· ||| 2)]

def aeval (M : AlgModel) (v : String → Nat) : PLLFormula → Nat
  | .prop s => v s
  | .falsePLL => M.bot
  | .and A B => M.meet (aeval M v A) (aeval M v B)
  | .or A B => M.join (aeval M v A) (aeval M v B)
  | .ifThen A B => M.imp (aeval M v A) (aeval M v B)
  | .somehow A => M.box (aeval M v A)

def vals (M : AlgModel) : List String → List (String → Nat)
  | [] => [fun _ => M.bot]
  | a :: as =>
      (vals M as).flatMap (fun v =>
        M.elems.map (fun x => fun s => if s = a then x else v s))

def leFails (atoms : List String) (X Y : PLLFormula) : Nat :=
  (zoo.map (fun M =>
    ((vals M atoms).filter (fun v =>
      ¬ (M.meet (aeval M v X) (aeval M v Y) = aeval M v X))).length)).foldl
    (· + ·) 0

def eqFails (atoms : List String) (X Y : PLLFormula) : Nat × Nat :=
  (leFails atoms X Y, leFails atoms Y X)

def fsize : PLLFormula → Nat
  | .prop _ => 1 | .falsePLL => 1
  | .and A B => fsize A + fsize B + 1
  | .or A B => fsize A + fsize B + 1
  | .ifThen A B => fsize A + fsize B + 1
  | .somehow A => fsize A + 1

private def pP := prop "p"
private def rP := prop "r"
private def sP := prop "s"

-- gap tower: χ₁ = (◯p⊃r)⊃◯p; χ₂ iterates the pattern on χ₁
private def chi1 : PLLFormula := ((pP.somehow).ifThen rP).ifThen pP.somehow
private def T1 : List PLLFormula := [chi1.somehow, (pP.somehow).ifThen rP]
private def chi2 : PLLFormula := ((chi1.somehow).ifThen sP).ifThen chi1.somehow
private def T2 : List PLLFormula :=
  [chi2.somehow, (chi1.somehow).ifThen sP, (pP.somehow).ifThen rP]

-- ◯/⊃ alternation
private def alt : PLLFormula :=
  (pP.ifThen ((rP.ifThen (pP.somehow)).somehow)).somehow
private def T3 : List PLLFormula := [alt, pP.somehow.ifThen rP]

-- spaces (piece closures, hand-listed)
private def S1 : Finset PLLFormula :=
  {chi1.somehow, chi1, (pP.somehow).ifThen rP, rP.ifThen pP.somehow,
   pP.somehow, pP, rP}
private def S2 : Finset PLLFormula :=
  {chi2.somehow, chi2, (chi1.somehow).ifThen sP, sP.ifThen chi1.somehow,
   chi1.somehow, chi1, (pP.somehow).ifThen rP, rP.ifThen pP.somehow,
   pP.somehow, pP, sP, rP}
private def S3 : Finset PLLFormula :=
  {alt, pP.ifThen ((rP.ifThen pP.somehow).somehow),
   (rP.ifThen pP.somehow).somehow, rP.ifThen pP.somehow,
   (pP.somehow).ifThen rP, pP.somehow, pP, rP}

-- sizes at budget 2/3 (gate: only proceed if sane)
#eval [fsize (itpE "p" S2 200 2 T2), fsize (itpE "p" S2 200 3 T2),
       fsize (itpE "p" S3 200 2 T3), fsize (itpE "p" S3 200 3 T3)]

-- budget-stability of the tower approximants (the falsification test:
-- persistent strict descent would be the danger signal)
#eval [eqFails ["p","r"] (itpE "p" S1 200 2 T1) (itpE "p" S1 200 3 T1),
       eqFails ["p","r","s"] (itpE "p" S2 200 2 T2) (itpE "p" S2 200 3 T2),
       eqFails ["p","r"] (itpE "p" S3 200 2 T3) (itpE "p" S3 200 3 T3)]
#eval [eqFails ["p","r","s"] (itpA "p" S2 200 2 T2 sP) (itpA "p" S2 200 3 T2 sP),
       eqFails ["p","r"] (itpA "p" S3 200 2 T3 rP.somehow) (itpA "p" S3 200 3 T3 rP.somehow)]

-- v2 direction-consistency at low fuel (cheap)
#eval [eqFails ["p","r","s"] (itpE "p" S2 200 2 T2) (interE "p" 3 T2),
       eqFails ["p","r"] (itpE "p" S3 200 2 T3) (interE "p" 3 T3)]

end PLLND
