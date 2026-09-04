import LaxLogic.PLLG4UI

/-!
# v3 probe 2: algebraic differencing

Finite Heyting algebras with a nucleus are sound for PLL, so a
pointwise disagreement between two formulas under some valuation
refutes their interderivability — in time linear in formula size.
Elements are `Nat`; each model packs (meet, join, imp, bot, top, j).

Models:
* 3-chain 0 < 1 < 2, nuclei: `id`, `max · 1`, `0↦0 else 2`, `const 2`;
* diamond = Boolean 2×2 on bits {0,1,2,3}, nuclei `id`, `||| 1`, `||| 2`.
-/

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

def chain3 (j : Nat → Nat) : AlgModel where
  meet := min
  join := max
  imp x y := if x ≤ y then 2 else y
  bot := 0
  top := 2
  box := j
  elems := [0, 1, 2]

def diamond (j : Nat → Nat) : AlgModel where
  meet x y := x &&& y
  join x y := x ||| y
  imp x y := (3 ^^^ x) ||| y
  bot := 0
  top := 3
  box := j
  elems := [0, 1, 2, 3]

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

/-- All valuations of the given atoms into the model. -/
def vals (M : AlgModel) : List String → List (String → Nat)
  | [] => [fun _ => M.bot]
  | a :: as =>
      (vals M as).flatMap (fun v =>
        M.elems.map (fun x => fun s => if s = a then x else v s))

/-- Count of (model, valuation) points where `X ≤ Y` FAILS — i.e.
witnesses against `X ⊢ Y`.  0 = semantically consistent with `X ⊢ Y`. -/
def leFails (atoms : List String) (X Y : PLLFormula) : Nat :=
  (zoo.map (fun M =>
    ((vals M atoms).filter (fun v =>
      ¬ (M.meet (aeval M v X) (aeval M v Y) = aeval M v X))).length)).foldl
    (· + ·) 0

/-- Pair: failures of `X ⊢ Y` and of `Y ⊢ X`. -/
def eqFails (atoms : List String) (X Y : PLLFormula) : Nat × Nat :=
  (leFails atoms X Y, leFails atoms Y X)

/-! ### v3 twin (same as probe 1) -/

mutual

def v3E (p : String) : Nat → Nat → List PLLFormula → PLLFormula
  | 0, _, _ => truePLL
  | fuel + 1, b, Γ =>
      andAll (
        (if falsePLL ∈ Γ then [falsePLL] else [])
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
        ++ Γ.flatMap (fun F => match F with
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then [] else [v3E p fuel b (A :: B :: Γ)]
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else [(v3E p fuel b (A :: Γ)).or (v3E p fuel b (B :: Γ))]
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if PLLFormula.prop q ∈ Γ then [v3E p fuel b (B :: Γ)]
                else if q = p then []
                else [(prop q).ifThen (v3E p fuel b (B :: Γ))]
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else [v3E p fuel b (A.ifThen (B.ifThen D) :: Γ)]
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else [v3E p fuel b (A.ifThen D :: B.ifThen D :: Γ)]
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if B.ifThen D ∈ Γ then
                  match b with
                  | 0 => []
                  | b' + 1 =>
                      [(v3A p fuel b' Γ (A.ifThen B)).ifThen
                        (v3E p fuel b (D :: Γ))]
                else
                  [((v3E p fuel b (B.ifThen D :: Γ)).ifThen
                      (v3A p fuel b (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                    (v3E p fuel b (D :: Γ))]
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else
                  (match b with
                    | 0 => []
                    | b' + 1 =>
                        [(v3A p fuel b' Γ A).ifThen (v3E p fuel b (B :: Γ)),
                         ((v3A p fuel b' Γ A.somehow).somehow).ifThen
                           (v3E p fuel b (B :: Γ))])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ then none
                          else some ((((v3E p fuel b (x :: Γ)).ifThen
                              (v3A p fuel b (x :: Γ) A.somehow)).somehow).ifThen
                            (v3E p fuel b (B :: Γ)))
                      | _ => none)
            | .somehow χ =>
                if χ ∈ Γ then [] else [(v3E p fuel b (χ :: Γ)).somehow]
            | _ => []))

def v3A (p : String) : Nat → Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _, _ => falsePLL
  | fuel + 1, b, Γ, C =>
      let env : List PLLFormula := Γ.flatMap (fun F => match F with
            | .prop q =>
                if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then []
                else [v3A p fuel b (A :: B :: Γ) C]
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else
                  [((v3E p fuel b (A :: Γ)).ifThen
                      (v3A p fuel b (A :: Γ) C)).and
                   ((v3E p fuel b (B :: Γ)).ifThen
                      (v3A p fuel b (B :: Γ) C))]
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if PLLFormula.prop q ∈ Γ then [v3A p fuel b (B :: Γ) C]
                else if q = p then []
                else [(prop q).and (v3A p fuel b (B :: Γ) C)]
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else [v3A p fuel b (A.ifThen (B.ifThen D) :: Γ) C]
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else [v3A p fuel b (A.ifThen D :: B.ifThen D :: Γ) C]
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if B.ifThen D ∈ Γ then
                  match b with
                  | 0 => []
                  | b' + 1 =>
                      [(v3A p fuel b' Γ (A.ifThen B)).and
                        (v3A p fuel b (D :: Γ) C)]
                else
                  [(((v3E p fuel b (B.ifThen D :: Γ)).ifThen
                      (v3A p fuel b (B.ifThen D :: Γ) (A.ifThen B)))).and
                    (v3A p fuel b (D :: Γ) C)]
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else
                  (match b with
                    | 0 => []
                    | b' + 1 =>
                        [(v3A p fuel b' Γ A).and (v3A p fuel b (B :: Γ) C),
                         ((v3A p fuel b' Γ A.somehow).somehow).and
                           (v3A p fuel b (B :: Γ) C)])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ then none
                          else some (((((v3E p fuel b (x :: Γ)).ifThen
                              (v3A p fuel b (x :: Γ) A.somehow)).somehow)).and
                            (v3A p fuel b (B :: Γ) C))
                      | _ => none)
            | .somehow χ => (match C with
                  | .somehow _ =>
                      if χ ∈ Γ then []
                      else
                        [((v3E p fuel b (χ :: Γ)).ifThen
                            (v3A p fuel b (χ :: Γ) C)).somehow]
                  | _ => [])
            | _ => [])
      let goal : List PLLFormula := (match C with
            | .prop q => if q = p then [] else [prop q]
            | .falsePLL => []
            | .and C₁ C₂ =>
                [(v3A p fuel b Γ C₁).and (v3A p fuel b Γ C₂)]
            | .or C₁ C₂ => [v3A p fuel b Γ C₁, v3A p fuel b Γ C₂]
            | .ifThen C₁ C₂ =>
                if C₁ ∈ Γ then [v3A p fuel b (C₁ :: Γ) C₂]
                else
                  [(v3E p fuel b (C₁ :: Γ)).ifThen
                    (v3A p fuel b (C₁ :: Γ) C₂)]
            | .somehow D => [(v3A p fuel b Γ D).somehow])
      let others := goal ++ env
      orAll (match C with
        | .somehow _ =>
            others ++ (if others.isEmpty then [] else [(orAll others).somehow])
        | _ => others)

end

/-! ### Battery -/

private def pP := prop "p"
private def rP := prop "r"
private def sP := prop "s"
private def uP := prop "u"
private def vP := prop "v"

private def G0 : List PLLFormula := [(pP.somehow).ifThen rP]
private def G1 : List PLLFormula := [(rP.somehow).ifThen sP, (uP.somehow).ifThen vP]
private def G2 : List PLLFormula := [(pP.somehow).ifThen sP, (uP.somehow).ifThen pP]
private def G3 : List PLLFormula :=
  [(((pP.somehow).ifThen rP).ifThen pP.somehow).somehow, (pP.somehow).ifThen rP]
private def G5 : List PLLFormula := [pP.somehow, (pP.somehow).ifThen sP]
private def G6 : List PLLFormula := [pP.ifThen rP, (uP.somehow).ifThen pP]

-- control: v2 fuel-stabilization, semantically (expect (0,0) everywhere)
#eval [eqFails ["p","r"] (interA "p" 3 G0 rP) (interA "p" 4 G0 rP),
       eqFails ["p","s","u"] (interA "p" 3 G2 sP) (interA "p" 4 G2 sP),
       eqFails ["p","r"] (interA "p" 3 G3 rP) (interA "p" 4 G3 rP),
       eqFails ["p","s","u"] (interE "p" 3 G2) (interE "p" 4 G2)]

-- v3 budget-stabilization (expect (0,0))
#eval [eqFails ["p","r"] (v3A "p" 40 2 G0 rP) (v3A "p" 40 3 G0 rP),
       eqFails ["p","s","u"] (v3A "p" 40 2 G2 sP) (v3A "p" 40 3 G2 sP),
       eqFails ["p","s","u"] (v3E "p" 40 2 G2) (v3E "p" 40 3 G2)]

-- PRIMARY: v3 vs v2 at stabilized levels (expect (0,0))
#eval [eqFails ["p","r"] (v3A "p" 40 3 G0 rP) (interA "p" 4 G0 rP),
       eqFails ["p","r"] (v3A "p" 40 3 G0 pP.somehow) (interA "p" 4 G0 pP.somehow),
       eqFails ["p","s","u"] (v3A "p" 40 3 G2 sP) (interA "p" 4 G2 sP),
       eqFails ["p","s","u"] (v3A "p" 40 3 G2 uP) (interA "p" 4 G2 uP)]
#eval [eqFails ["p","s","u"] (v3E "p" 40 3 G2) (interE "p" 4 G2),
       eqFails ["p","r"] (v3E "p" 40 3 G0) (interE "p" 4 G0),
       eqFails ["p","s"] (v3E "p" 40 3 G5) (interE "p" 4 G5)]
#eval [eqFails ["p","s"] (v3A "p" 40 3 G5 sP.somehow) (interA "p" 4 G5 sP.somehow),
       eqFails ["p","r","u"] (v3A "p" 40 3 G6 rP.somehow) (interA "p" 4 G6 rP.somehow),
       eqFails ["p","r"] (v3A "p" 40 3 [pP] rP) (interA "p" 4 [pP] rP)]

-- the self-firing context (big values: budget 2 vs v2 fuel 4)
#eval [eqFails ["p","r"] (v3A "p" 40 2 G3 rP) (interA "p" 4 G3 rP),
       eqFails ["p","r"] (v3E "p" 40 2 G3) (interE "p" 4 G3)]

-- fresh-q oracle: sequent-∀ ⊣⊢ ⋀Γ ⊃ C (expect (0,0))
#eval [eqFails ["r","s","u","v"]
         ((v3E "q" 40 3 G1).ifThen (v3A "q" 40 3 G1 uP))
         ((andAll G1).ifThen uP),
       eqFails ["p","r"]
         ((v3E "q" 40 3 [pP]).ifThen (v3A "q" 40 3 [pP] rP))
         ((andAll [pP]).ifThen rP)]

-- p-freeness of v3 (expect [false, false, false])
#eval [decide ("p" ∈ (v3E "p" 40 3 G2).atoms),
       decide ("p" ∈ (v3A "p" 40 3 G2 sP).atoms),
       decide ("p" ∈ (v3A "p" 40 3 G6 rP.somehow).atoms)]

end PLLND

/-! ### Localization -/

namespace PLLND2
open PLLND PLLFormula

/-- Split a right-nested `andAll`/`orAll` spine. -/
def spine : PLLFormula → List PLLFormula
  | .and A B => A :: spine B
  | .or A B => A :: spine B
  | φ => [φ]

-- L1: E1/A1 semantically for v3 (expect 0s = sound)
#eval [leFails ["p","r"] (andAll G3) (v3E "p" 40 2 G3),
       leFails ["p","r"] (andAll G0) (v3E "p" 40 3 G0),
       leFails ["p","s","u"] (andAll G2) (v3E "p" 40 3 G2)]
#eval [leFails ["p","r"] (andAll (v3A "p" 40 3 G0 pP.somehow :: G0)) pP.somehow,
       leFails ["p","r","u"] (andAll (v3A "p" 40 3 G6 rP.somehow :: G6)) rP.somehow,
       leFails ["p","r"] (andAll (v3A "p" 40 2 G3 rP :: G3)) rP]

-- L2: sequent-form comparison on the three misses (expect (0,0) if raw-value
-- mismatch was an artifact of the missing ambient E)
#eval [eqFails ["p","r"]
         ((v3E "p" 40 3 G0).ifThen (v3A "p" 40 3 G0 pP.somehow))
         ((interE "p" 4 G0).ifThen (interA "p" 4 G0 pP.somehow)),
       eqFails ["p","r","u"]
         ((v3E "p" 40 3 G6).ifThen (v3A "p" 40 3 G6 rP.somehow))
         ((interE "p" 4 G6).ifThen (interA "p" 4 G6 rP.somehow)),
       eqFails ["p","r"]
         ((v3E "p" 40 2 G3).ifThen (v3A "p" 40 2 G3 rP))
         ((interE "p" 4 G3).ifThen (interA "p" 4 G3 rP))]

-- L3: which v3E-conjunct on G3 is not Γ-entailed?
#eval ((spine (v3E "p" 40 2 G3)).map (fun c => leFails ["p","r"] (andAll G3) c))

-- L4: which v2-disjunct exceeds v3A on the ◯-goal misses?
#eval ((spine (interA "p" 4 G0 pP.somehow)).map
        (fun d => leFails ["p","r"] d (v3A "p" 40 3 G0 pP.somehow)))
#eval ((spine (interA "p" 4 G6 rP.somehow)).map
        (fun d => leFails ["p","r","u"] d (v3A "p" 40 3 G6 rP.somehow)))

-- L5: and does v2E exceed v3E per-conjunct on G3? (locate E2-content v3 lost)
#eval ((spine (interE "p" 4 G3)).map
        (fun c => leFails ["p","r"] (v3E "p" 40 2 G3) c))

end PLLND2

namespace PLLND3
open PLLND PLLFormula

-- G3 budget escalation: was the anomaly just budget shortfall?
-- (a) budget-stabilization on G3-E: b2 vs b3
#eval eqFails ["p","r"] (v3E "p" 40 2 G3) (v3E "p" 40 3 G3)
-- (b) v3@b3 vs v2@4 on G3-E, raw and sequent form
#eval eqFails ["p","r"] (v3E "p" 40 3 G3) (interE "p" 4 G3)
#eval eqFails ["p","r"]
       ((v3E "p" 40 3 G3).ifThen (v3A "p" 40 3 G3 rP))
       ((interE "p" 4 G3).ifThen (interA "p" 4 G3 rP))
-- (c) extra coverage: jump-cycle-through-p with ◯-goals, sequent form
#eval eqFails ["p","s","u"]
       ((v3E "p" 40 3 G2).ifThen (v3A "p" 40 3 G2 sP.somehow))
       ((interE "p" 4 G2).ifThen (interA "p" 4 G2 sP.somehow))

end PLLND3
