import LaxLogic.PLLG4Dec

/-!
# Exhaustive sweep: the reconstruction sequents over all small formulas

For EVERY raw one-variable formula M up to a weight cap (no semantic
dedup — raw syntax, thousands of instances), test the two
reconstruction sequents of `LaxLogic/PLLSemUI.lean`:

    (∀-rec)   M[⊥], M[⊤], lowT p M, sideT p M  ⊢  M
    (∃-rec)   M  ⊢  M[⊥] ∨ M[⊤] ∨ M[◯⊥] ∨ lowT p M ∨ sideT p M

with nf-simplified generators (nf uses PLL-equivalences only, so
verdicts transfer).  `true` is oracle-sound.  A `false` is only
"not found within budget" — every false is printed with the instance
for slow re-examination; if the sequents are true everywhere, this
sweep is strong evidence that the four-generator basis saturates at
one variable, i.e. that definability holds with `allCand`/`exCand`
as the uniform quantifier values.

Run with  `lake env lean --run wip/semui_sweep.lean`.
-/

open PLLFormula PLLND

namespace SemUISweep

def CFUEL : Nat := 200

def provF (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def provC (Γ : List PLLFormula) (C : PLLFormula) : Bool := provF CFUEL Γ C

def pf (F : PLLFormula) : String := F.toString

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

def isTop : PLLFormula → Bool
  | .ifThen .falsePLL .falsePLL => true
  | _ => false

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
        | .somehow B => .somehow B
        | _ => .somehow A
  | F => F

def nf : PLLFormula → PLLFormula
  | .and A B    => smash (.and (nf A) (nf B))
  | .or A B     => smash (.or (nf A) (nf B))
  | .ifThen A B => smash (.ifThen (nf A) (nf B))
  | .somehow A  => smash (.somehow (nf A))
  | F => F

def buildTable (leaves : List PLLFormula) (maxW : Nat) :
    Array (List PLLFormula) := Id.run do
  let mut tbl : Array (List PLLFormula) := #[[]]
  for n in List.range maxW do
    let w := n + 1
    let mut acc : List PLLFormula := []
    if w = 1 then
      acc := leaves
    else
      for i in List.range (w - 1) do
        let a := i
        let b := w - 2 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.and y) :: acc
      for i in List.range w do
        let a := i
        let b := w - 1 - a
        if a ≥ 1 ∧ b ≥ 1 ∧ a < tbl.size ∧ b < tbl.size then
          for x in tbl[a]! do
            for y in tbl[b]! do
              acc := (x.or y) :: acc
              acc := (x.ifThen y) :: acc
      if w ≥ 2 ∧ w - 1 < tbl.size then
        for x in tbl[w-1]! do
          acc := x.somehow :: acc
    tbl := tbl.push acc
  return tbl

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow

def MAXW : Nat := 7

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== reconstruction sweep over ALL raw 1-variable formulas =="
  pl s!"weight ≤ {MAXW}; cert fuel {CFUEL}; generators nf-simplified"
  let tbl := buildTable [pV, .falsePLL] MAXW
  let p := "p"
  let mut tested := 0
  let mut failA := 0
  let mut failE := 0
  let mut skipped := 0
  for n in List.range MAXW do
    let w := n + 1
    let t0 ← IO.monoMsNow
    let mut lvlA := 0
    let mut lvlE := 0
    for M in tbl[w]! do
      let g1 := nf (substP p .falsePLL M)
      let g2 := nf (substP p truePLL M)
      let g3 := nf (substP p gB M)
      let gl := nf (lowT p M)
      let gs := nf (sideT p M)
      let ctxA := [g1, g2, gl, gs]
      if listWeight (M :: ctxA) > 90 then
        skipped := skipped + 1
      else
        tested := tested + 1
        let recA := provC ctxA M
        if !recA then
          failA := failA + 1
          lvlA := lvlA + 1
          pl s!"  ∀-REC-FALSE: M = {pf M}"
          pl s!"    gens: {pf g1} | {pf g2} | {pf gl} | {pf gs}"
        let disj := nf (g1.or (g2.or (g3.or (gl.or gs))))
        let recE := provC [M] disj
        if !recE then
          failE := failE + 1
          lvlE := lvlE + 1
          pl s!"  ∃-REC-FALSE: M = {pf M}  disj = {pf disj}"
    let t1 ← IO.monoMsNow
    pl s!"weight {w}: {(tbl[w]!).length} raw formulas; ∀-fails {lvlA}, ∃-fails {lvlE}  ({t1 - t0} ms)"
  pl s!"TOTAL tested {tested} (skipped {skipped}): ∀-rec fails {failA}, ∃-rec fails {failE}"
  pl "== done =="

end SemUISweep

def main : IO Unit := SemUISweep.main
