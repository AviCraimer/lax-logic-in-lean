import LaxLogic.PLLG4UITrunc

/-! Minimal-fragment stress probe (Matthew's meta-tactic, scoped).

The {⊥,⇒,◯} fragment IS the project's hard core (jump system, γ-boxes,
cascade); it is piece-closed, so the full quantifiers restricted to
fragment inputs are the fragment quantifiers.  Fragment values are
small, so we can stress the cascade shape much deeper than the full
language allows: jump-chain families of growing length k measure how
the stabilization budget b*(k) grows with premise-1-chain length. -/

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

-- jump chains: Γ_k = [◯a₀⇒a₁, …, ◯a_{k-1}⇒a_k], quantify p := a₀
private def at_ (i : Nat) : PLLFormula := prop s!"a{i}"
private def link (i : Nat) : PLLFormula := ((at_ i).somehow).ifThen (at_ (i+1))
private def chainCtx (k : Nat) : List PLLFormula := (List.range k).map link
private def chainS (k : Nat) : Finset PLLFormula :=
  ((List.range k).flatMap (fun i => [link i, at_ i, (at_ i).somehow])
    ++ [at_ k]).toFinset
private def chainAtoms (k : Nat) : List String := (List.range (k+1)).map (s!"a{·}")

-- budget ladders per chain length: b* = first level with (0,0)
private def ladder (k : Nat) (b : Nat) : Nat × Nat :=
  eqFails (chainAtoms k)
    (itpE "a0" (chainS k) 300 b (chainCtx k))
    (itpE "a0" (chainS k) 300 (b+1) (chainCtx k))

#eval [fsize (itpE "a0" (chainS 3) 300 3 (chainCtx 3)),
       fsize (itpE "a0" (chainS 4) 300 4 (chainCtx 4))]
#eval (ladder 2 1, ladder 2 2, ladder 2 3)
#eval (ladder 3 1, ladder 3 2, ladder 3 3, ladder 3 4)
#eval (ladder 4 1, ladder 4 2, ladder 4 3, ladder 4 4)
-- A-side at the far goal (needs the whole chain to fire)
#eval [eqFails (chainAtoms 3)
        (itpA "a0" (chainS 3) 300 2 (chainCtx 3) (at_ 3))
        (itpA "a0" (chainS 3) 300 3 (chainCtx 3) (at_ 3)),
       eqFails (chainAtoms 4)
        (itpA "a0" (chainS 4) 300 3 (chainCtx 4) (at_ 4))
        (itpA "a0" (chainS 4) 300 4 (chainCtx 4) (at_ 4))]

end PLLND
