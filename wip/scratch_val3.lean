import LaxLogic.PLLG4UITrunc

open PLLFormula
namespace PLLND

/-- val3 in the 3-chain {0<1<2} with nucleus j = max·1. -/
def val3 : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => min (val3 A) (val3 B)
  | .or A B => max (val3 A) (val3 B)
  | .ifThen A B => if val3 A ≤ val3 B then 2 else val3 B
  | .somehow A => max (val3 A) 1

-- sanity
#eval val3 (somehow falsePLL)              -- ◯⊥ = 1
#eval val3 (somehow (somehow falsePLL))    -- ◯◯⊥ = 1
#eval val3 (somehow truePLL)               -- ◯⊤ = 2
#eval val3 truePLL                         -- ⊤ = 2
#eval val3 (ifThen (somehow falsePLL) falsePLL)  -- ¬◯⊥ = 0 (the escape element!)

private def pA := prop "p"

-- single-variable configs (atoms ⊆ {p})
private def S1 : Finset PLLFormula := {pA.somehow.ifThen pA, pA, pA.somehow}
private def G1a : List PLLFormula := [pA.somehow.ifThen pA]
private def G1b : List PLLFormula := [pA.somehow.ifThen pA, pA.somehow]
private def G1c : List PLLFormula := [pA.somehow]

def fuelBig : Nat := 60

-- val3 of itpA across budgets 0..5
#eval (List.range 6).map (fun b => val3 (itpA "p" S1 fuelBig b G1a pA))
#eval (List.range 6).map (fun b => val3 (itpA "p" S1 fuelBig b G1b pA))
#eval (List.range 6).map (fun b => val3 (itpA "p" S1 fuelBig b G1c (pA.somehow)))
#eval (List.range 6).map (fun b => val3 (itpE "p" S1 fuelBig b G1a))
#eval (List.range 6).map (fun b => val3 (itpE "p" S1 fuelBig b G1b))

-- the actual interpolant shapes at b=1,2,3 for G1b
#eval (itpA "p" S1 fuelBig 1 G1b pA)
#eval (itpA "p" S1 fuelBig 2 G1b pA)
#eval (itpA "p" S1 fuelBig 3 G1b pA)
#eval (itpE "p" S1 fuelBig 1 G1b)
#eval (itpE "p" S1 fuelBig 2 G1b)

-- syntactic equality across budgets?
#eval decide (itpA "p" S1 fuelBig 2 G1b pA = itpA "p" S1 fuelBig 3 G1b pA)
#eval decide (itpA "p" S1 fuelBig 1 G1b pA = itpA "p" S1 fuelBig 2 G1b pA)

/-- val3 = eval in chain3 with nucleus max·1.  Also eval in chain3 with
nucleus = id (both are SOUND PLL models), to expose the incompleteness. -/
def valId : PLLFormula → Nat
  | .prop _ => 0
  | .falsePLL => 0
  | .and A B => min (valId A) (valId B)
  | .or A B => max (valId A) (valId B)
  | .ifThen A B => if valId A ≤ valId B then 2 else valId B
  | .somehow A => valId A          -- nucleus = identity

-- COUNTEREXAMPLE to the completeness bridge `val3 x ≤ val3 y → G4c [x] y`:
--   x = ◯⊥→⊥ (= ¬◯⊥),  y = ⊥.
-- val3 says 0 ≤ 0 (would license G4c [¬◯⊥] ⊥), but the identity-nucleus
-- model gives valId(¬◯⊥)=2 > valId(⊥)=0, so ¬◯⊥ ⊬ ⊥.  A single 3-chain
-- is NOT complete for the closed fragment (¬◯⊥ escapes {⊥,◯⊥,⊤}).
#eval (val3 (ifThen (somehow falsePLL) falsePLL), val3 falsePLL)   -- (0, 0)
#eval (valId (ifThen (somehow falsePLL) falsePLL), valId falsePLL) -- (2, 0)  ← disagreement

end PLLND
