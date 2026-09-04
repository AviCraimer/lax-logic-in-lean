import LaxLogic.PLLG4UITrunc

/-! v3.1 probe: the REAL itpE/itpA (guards restored, all same-context
references budget-paying) against the v2 fixpoint. -/

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
private def uP := prop "u"
private def vP := prop "v"
private def chi : PLLFormula := ((pP.somehow).ifThen rP).ifThen pP.somehow

private def G0 : List PLLFormula := [(pP.somehow).ifThen rP]
private def S0 : Finset PLLFormula := {(pP.somehow).ifThen rP, rP, pP.somehow, pP}
private def G1 : List PLLFormula := [(rP.somehow).ifThen sP, (uP.somehow).ifThen vP]
private def S1 : Finset PLLFormula :=
  {(rP.somehow).ifThen sP, (uP.somehow).ifThen vP, sP, vP, rP.somehow, uP.somehow, rP, uP}
private def G2 : List PLLFormula := [(pP.somehow).ifThen sP, (uP.somehow).ifThen pP]
private def S2 : Finset PLLFormula :=
  {(pP.somehow).ifThen sP, (uP.somehow).ifThen pP, sP, pP, pP.somehow, uP.somehow, uP}
private def G3 : List PLLFormula := [chi.somehow, (pP.somehow).ifThen rP]
private def S3 : Finset PLLFormula :=
  {chi.somehow, chi, (pP.somehow).ifThen rP, rP.ifThen pP.somehow, pP.somehow, pP, rP}
private def G6 : List PLLFormula := [pP.ifThen rP, (uP.somehow).ifThen pP]
private def S6 : Finset PLLFormula :=
  {pP.ifThen rP, (uP.somehow).ifThen pP, rP, pP, uP.somehow, uP}

-- sizes at fuel 150 (measure-safe), budgets 2/3
#eval ([fsize (itpE "p" S3 150 2 G3), fsize (itpA "p" S3 150 2 G3 rP)],
       [fsize (itpE "p" S2 150 2 G2), fsize (itpE "p" S2 150 3 G2)])

-- HEADLINE: G3 (self-firing) E-side and sequent form vs v2@5
#eval eqFails ["p","r"] (itpE "p" S3 150 2 G3) (interE "p" 5 G3)
#eval eqFails ["p","r"]
       ((itpE "p" S3 150 2 G3).ifThen (itpA "p" S3 150 2 G3 rP))
       ((interE "p" 5 G3).ifThen (interA "p" 5 G3 rP))

-- regressions: previously-passing instances stay green?
#eval [eqFails ["p","s","u"] (itpA "p" S2 150 3 G2 sP) (interA "p" 4 G2 sP),
       eqFails ["p","s","u"] (itpE "p" S2 150 3 G2) (interE "p" 4 G2)]
#eval [eqFails ["p","r"]
         ((itpE "p" S0 150 3 G0).ifThen (itpA "p" S0 150 3 G0 pP.somehow))
         ((interE "p" 4 G0).ifThen (interA "p" 4 G0 pP.somehow)),
       eqFails ["p","r","u"]
         ((itpE "p" S6 150 3 G6).ifThen (itpA "p" S6 150 3 G6 rP.somehow))
         ((interE "p" 4 G6).ifThen (interA "p" 4 G6 rP.somehow))]
#eval eqFails ["r","s","u","v"]
       ((itpE "q" S1 150 3 G1).ifThen (itpA "q" S1 150 3 G1 uP))
       ((andAll G1).ifThen uP)

-- E1/A1 semantic soundness for v3.1 on G3 and G2
#eval [leFails ["p","r"] (andAll G3) (itpE "p" S3 150 2 G3),
       leFails ["p","s","u"] (andAll G2) (itpE "p" S2 150 3 G2),
       leFails ["p","r"] (andAll (itpA "p" S3 150 2 G3 rP :: G3)) rP]

-- budget stabilization on the small contexts (b2 vs b3)
#eval [eqFails ["p","s","u"] (itpA "p" S2 150 2 G2 sP) (itpA "p" S2 150 3 G2 sP),
       eqFails ["p","s","u"] (itpE "p" S2 150 2 G2) (itpE "p" S2 150 3 G2),
       eqFails ["p","r"] (itpE "p" S0 150 2 G0) (itpE "p" S0 150 3 G0)]

-- budget escalation on G3: sizes first, then the convergence checks
#eval (fsize (itpE "p" S3 150 3 G3), fsize (interE "p" 6 G3))
#eval eqFails ["p","r"] (itpE "p" S3 150 3 G3) (interE "p" 5 G3)
#eval eqFails ["p","r"] (itpE "p" S3 150 2 G3) (itpE "p" S3 150 3 G3)
#eval eqFails ["p","r"] (interE "p" 5 G3) (interE "p" 6 G3)

-- resolution check: v3.1 vs v2@6 (E, A, and sequent form) on G3
#eval eqFails ["p","r"] (itpE "p" S3 150 2 G3) (interE "p" 6 G3)
#eval eqFails ["p","r"] (itpA "p" S3 150 2 G3 rP) (interA "p" 6 G3 rP)
#eval eqFails ["p","r"]
       ((itpE "p" S3 150 2 G3).ifThen (itpA "p" S3 150 2 G3 rP))
       ((interE "p" 6 G3).ifThen (interA "p" 6 G3 rP))
