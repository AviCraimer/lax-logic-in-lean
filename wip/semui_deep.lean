import LaxLogic.PLLG4Dec

/-!
# Deep battery: the reconstruction sequents at ◯/⊃-alternation depth ≥ 3

The reduction (`LaxLogic/PLLSemUI.lean`): one-variable definability
follows from the two sequent families

    (∀-rec)   M[⊥], M[⊤], lowT p M, sideT p M  ⊢  M
    (∃-rec)   M  ⊢  M[⊥] ∨ M[⊤] ∨ M[◯⊥] ∨ lowT p M ∨ sideT p M

Both hold across the weight-≤5 value table.  The tower picture predicts
they might FAIL at deeper ◯/⊃ alternation (the sideways construction
was forced at depth 2).  This battery tests both sequents, plus the
candidate values and their certificates, on targeted depth-3 formulas.

All generator instances are pre-simplified by `nf` — a normaliser using
only PLL-equivalences (Heyting ⊥/⊤ laws, ◯⊤ ≡ ⊤, ◯◯ ≡ ◯), so oracle
verdicts transfer to the raw sequents by congruence.  A `true` is sound
(a genuine derivation exists); `false` only means not-found within the
fuel/weight budget.

Run with  `lake env lean --run wip/semui_deep.lean`.
-/

open PLLFormula PLLND

namespace SemUIDeep

/-! ## Oracle -/

def FUEL : Nat := 500
def CFUEL : Nat := 200

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF FUEL Γ C
def provC (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF CFUEL Γ C
def entails (X Y : PLLFormula) : Bool := prov [X] Y

def pf (F : PLLFormula) : String := F.toString

/-! ## Transforms (mirrors of `SemUI`) -/

def substP (p : String) (χ : PLLFormula) : PLLFormula → PLLFormula
  | .prop a     => if a = p then χ else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => .and (substP p χ A) (substP p χ B)
  | .or A B     => .or (substP p χ A) (substP p χ B)
  | .ifThen A B => .ifThen (substP p χ A) (substP p χ B)
  | .somehow A  => .somehow (substP p χ A)

def lowT (p : String) : PLLFormula → PLLFormula
  | .prop a     => if a = p then .falsePLL else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => (lowT p A).and (lowT p B)
  | .or A B     => (lowT p A).or (lowT p B)
  | .ifThen A B => ((lowT p A).ifThen (lowT p B)).and
      ((substP p truePLL A).ifThen (substP p truePLL B))
  | .somehow A  => (substP p truePLL A).somehow

def sideT (p : String) : PLLFormula → PLLFormula
  | .prop a     => if a = p then .falsePLL else .prop a
  | .falsePLL   => .falsePLL
  | .and A B    => (sideT p A).and (sideT p B)
  | .or A B     => (sideT p A).or (sideT p B)
  | .ifThen A B => ((sideT p A).ifThen (sideT p B)).and (lowT p (A.ifThen B))
  | .somehow A  => ((sideT p A).somehow).and ((substP p truePLL A).somehow)

/-! ## Normaliser (PLL-equivalences only: `nf X ≡ X`) -/

def isTop : PLLFormula → Bool
  | .ifThen .falsePLL .falsePLL => true
  | _ => false

/-- One constructor-level simplification step (each clause a
PLL-equivalence). -/
def smash : PLLFormula → PLLFormula
  | .and A B =>
      if A == .falsePLL || B == .falsePLL then .falsePLL
      else if isTop A then B else if isTop B then A
      else if A == B then A
      else .and A B
  | .or A B =>
      if isTop A || isTop B then truePLL
      else if A == .falsePLL then B else if B == .falsePLL then A
      else if A == B then A
      else .or A B
  | .ifThen A B =>
      if A == .falsePLL || isTop B then truePLL
      else if isTop A then B
      else if A == B then truePLL
      else .ifThen A B
  | .somehow A =>
      if isTop A then truePLL
      else match A with
        | .somehow B => .somehow B    -- ◯◯B ≡ ◯B
        | _ => .somehow A
  | F => F

def nf : PLLFormula → PLLFormula
  | .and A B    => smash (.and (nf A) (nf B))
  | .or A B     => smash (.or (nf A) (nf B))
  | .ifThen A B => smash (.ifThen (nf A) (nf B))
  | .somehow A  => smash (.somehow (nf A))
  | F => F

/-! ## Targets -/

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def imp (A B : PLLFormula) : PLLFormula := A.ifThen B
def box (A : PLLFormula) : PLLFormula := A.somehow

/-- Löb iterates and depth-3 mixtures. -/
def targets : List (String × PLLFormula) :=
  [ ("L2  = ◯(◯p⊃p)          ", box (imp (box pV) pV))
  , ("L3  = ◯(◯(◯p⊃p)⊃p)     ", box (imp (box (imp (box pV) pV)) pV))
  , ("L3' = ◯(◯p⊃p)⊃p        ", imp (box (imp (box pV) pV)) pV)
  , ("P3  = ◯((◯p⊃p)⊃p)      ", box (imp (imp (box pV) pV) pV))
  , ("E3  = ◯(◯(p∨¬p)⊃p)     ", box (imp (box (pV.or (nF pV))) pV))
  , ("D3  = ◯(◯p⊃p)∨p        ", (box (imp (box pV) pV)).or pV)
  , ("N3  = ¬◯(◯p⊃p)         ", nF (box (imp (box pV) pV)))
  , ("B3  = ◯¬(◯p⊃p)         ", box (nF (imp (box pV) pV)))
  , ("I3  = ◯(◯p⊃p)⊃◯⊥       ", imp (box (imp (box pV) pV)) gB)
  , ("W3  = ¬◯(◯p⊃p)∨◯(◯p⊃p) ", (nF (box (imp (box pV) pV))).or (box (imp (box pV) pV)))
  , ("EM2 = (◯p⊃p)∨¬(◯p⊃p)   ", (imp (box pV) pV).or (nF (imp (box pV) pV)))
  , ("L4  = ◯(◯(◯(◯p⊃p)⊃p)⊃p)", box (imp (box (imp (box (imp (box pV) pV)) pV)) pV))
  , ("G3  = ◯((◯p⊃⊥)⊃◯p)     ", box (imp (imp (box pV) .falsePLL) (box pV)))
  , ("R3  = ◯(¬p∨◯p)         ", box ((nF pV).or (box pV)))
  ]

/-- The closed ladder representatives (weight ≤ 8, from the main probe). -/
def ladder : List PLLFormula :=
  [ .falsePLL, gB, truePLL, nF gB, (nF gB).somehow,
    nF (nF gB), (nF gB).or gB ]

def orAll : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | [x] => x
  | x :: xs => x.or (orAll xs)

def maximals (xs : List PLLFormula) : List PLLFormula :=
  xs.filter (fun x => xs.all (fun y => !(entails x y) || entails y x))

def minimals (xs : List PLLFormula) : List PLLFormula :=
  xs.filter (fun x => xs.all (fun y => !(entails y x) || entails x y))

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== deep battery: reconstruction sequents at depth ≥ 3 =="
  pl s!"fuel {FUEL}/{CFUEL}; generators nf-simplified"
  let p := "p"
  for (name, M) in targets do
    pl s!"-- {name}  (w={M.weight})"
    let g1 := nf (substP p .falsePLL M)
    let g2 := nf (substP p truePLL M)
    let g3 := nf (substP p gB M)
    let gl := nf (lowT p M)
    let gs := nf (sideT p M)
    pl s!"   gens: M[⊥]={pf g1} | M[⊤]={pf g2} | M[◯⊥]={pf g3}"
    pl s!"         lowT={pf gl} | sideT={pf gs}"
    -- candidates over the ladder
    let t0 ← IO.monoMsNow
    let low := ladder.filter (fun ξ => entails ξ M)
    let maxs := maximals low
    let candA := orAll maxs
    let okA := entails candA M
    let up := ladder.filter (fun ξ => entails M ξ)
    let mins := minimals up
    let candE := match mins with
      | [x] => x
      | _ => truePLL
    let okE := entails M candE
    let t1 ← IO.monoMsNow
    pl s!"   ∀p-cand = {pf candA} (sound={okA}, {maxs.length} max)  ∃p-cand = {pf candE} (sound={okE}, {mins.length} min)  ({t1 - t0} ms)"
    -- ∀-reconstruction: [gens] ⊢ M  (success expected fast if true)
    let ctxA := [g1, g2, gl, gs]
    let wA := listWeight (M :: ctxA)
    let t2 ← IO.monoMsNow
    let recA := provC ctxA M
    let t3 ← IO.monoMsNow
    pl s!"   ∀-rec [gens]⊢M (w={wA}): {recA}  ({t3 - t2} ms)"
    -- certificate for candA from the generator basis
    let t4 ← IO.monoMsNow
    let certA := provC ctxA candA
    let t5 ← IO.monoMsNow
    pl s!"   [gens]⊢∀p-cand: {certA}  ({t5 - t4} ms)"
    -- ∃-reconstruction: M ⊢ ⋁ gens
    let disj := nf (g1.or (g2.or (g3.or (gl.or gs))))
    let wE := listWeight (disj :: [M])
    let t6 ← IO.monoMsNow
    let recE := provC [M] disj
    let t7 ← IO.monoMsNow
    pl s!"   ∃-rec M⊢⋁gens (w={wE}): {recE}  ({t7 - t6} ms)"
    -- candE certificate: [candE] ⊢ one generator
    let t8 ← IO.monoMsNow
    let certE := [g1, g2, g3, gl, gs].any (fun g => provC [candE] g)
    let t9 ← IO.monoMsNow
    pl s!"   [∃p-cand]⊢some gen: {certE}  ({t9 - t8} ms)"
  pl "== done =="

end SemUIDeep

def main : IO Unit := SemUIDeep.main
