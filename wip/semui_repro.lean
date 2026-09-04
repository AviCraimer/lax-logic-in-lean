import wip.semui_ctx_core
import LaxLogic.PLLCountermodelEmit

/-!
# Reproduction: the three large-object claims of the harness report

Rebuilds, from explicit ingredients, the three examples cited in the
2026-07-19 harness report and re-times them:

1. the weight-1476 RELATIVE TOWER of the certifier run — the IPC
   ∀p-interpolant table (budget 2) of `(◯(◯p⊃p))^{C_fork}` computed
   relative to the fork's fallibility axioms;
2. the weight-855,029 tower of the pool run — same formula translated
   by the Lemma-7 constraint of the 9-world Löb variant of chain3
   (alphabet c), relative to the joint fallibility theory;
3. the weight-856,153 CERTIFIED SEQUENT of the pool run — the full
   pool conjunction plus the six fallibility axioms against the
   translated value, refuted by the ONE-WORLD countermodel (only `a0`
   true) through the VERIFIED checker `FinCM.checkB`.

All ingredients (models, constraints, the countermodel) are small and
printed; only the towers are large.  Run compiled:
`lake build weightrepro && .lake/build/bin/weightrepro`.
-/

open PLLFormula PLLND PLLND.Ctx CtxRel

namespace Repro

/-! ## Pool-probe ingredients (copied verbatim from wip/semui_pool.lean) -/

def doubleM (m : CtxRel.FinModel) : CtxRel.FinModel where
  n := 2 * m.n
  ri := fun x y =>
    m.ri (x % m.n) (y % m.n) && (decide (x < m.n) || !(decide (y < m.n)))
  rm := fun x y =>
    m.rm (x % m.n) (y % m.n) && (decide (x < m.n) || !(decide (y < m.n)))
  fal := fun x => m.fal (x % m.n)

def lobM (m : CtxRel.FinModel) : CtxRel.FinModel where
  n := 3 * m.n
  ri := fun x y =>
    m.ri (x % m.n) (y % m.n) && decide (x / m.n ≤ y / m.n)
  rm := fun x y =>
    m.rm (x % m.n) (y % m.n) &&
      (decide (x / m.n = y / m.n) ||
        (decide (x / m.n = 1) && decide (y / m.n = 2)))
  fal := fun x => m.fal (x % m.n)

def pname (pre : String) (i : Nat) : PLLFormula := .prop s!"{pre}{i}"

def pc0Of (pre : String) (m : CtxRel.FinModel) : StdCtx :=
  ((CtxRel.worlds m).filter (CtxRel.stable m)).map (fun u =>
    (pname pre u, Ctx.bigOr (((CtxRel.worlds m).filter (CtxRel.iSuccB m u)).map (pname pre))))

def pfalAx (pre : String) (m : CtxRel.FinModel) : List PLLFormula :=
  ((CtxRel.worlds m).filter m.fal).map (fun w => (pname pre w).ifThen .falsePLL)

def bigAnd : List PLLFormula → PLLFormula
  | [] => truePLL
  | [x] => x
  | x :: xs => x.and (bigAnd xs)

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def MLob : PLLFormula := ((pV.somehow).ifThen pV).somehow   -- ◯(◯p⊃p)

def pf (F : PLLFormula) : String := F.toString

def head (s : String) (n : Nat) : String := (s.take n).toString

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== reproduction of the three large-object claims =="

  -- (1) certifier: fork, ◯(◯p⊃p), relative tower, budget 2
  let Cf := c0Of mFork
  let Θf := falAxioms mFork
  pl s!"(1) fork constraint C = {Cf.map (fun kl => (pf kl.1, pf kl.2))}"
  pl s!"    Θ = {Θf.map pf}"
  let Tf := nf (subC Cf MLob)
  pl s!"    translation (◯(◯p⊃p))^C: weight {Tf.weight}"
  -- NOTE: weights are computed INSIDE the brackets — `.weight` forces
  -- the whole tree, defeating the compiler's let-inlining that made
  -- the original probes print spurious "0 ms" for these stages.
  let t0 ← IO.monoMsNow
  let Apl := nf (itpA "p" (pieceClosure Tf) TFUEL 2 [] Tf)
  pl s!"    plain tower w={Apl.weight}"
  let Arel := towerARel Θf Tf 2
  pl s!"    RELATIVE TOWER w={Arel.weight}"
  let t1 ← IO.monoMsNow
  pl s!"    (both towers, IO-forced: {t1 - t0} ms)"
  pl s!"    head of the relative tower: {head (pf Arel) 100} …"

  -- (2)+(3) pool: chain3, alphabets a/b/c, the big c-tower and the
  -- certified pool sequent
  let variants := [("a", mChain3), ("b", doubleM mChain3), ("c", lobM mChain3)]
  let Cs := variants.map (fun pv => (pv.1, pc0Of pv.1 pv.2))
  let Θpool := variants.flatMap (fun pv => pfalAx pv.1 pv.2)
  pl s!"(2) chain3 pool: C_a = {(Cs.getD 0 default).2.map (fun kl => (pf kl.1, pf kl.2))}"
  pl s!"    C_c (Löb variant, 9 worlds) = {(Cs.getD 2 default).2.map (fun kl => (pf kl.1, pf kl.2))}"
  pl s!"    Θpool = {Θpool.map pf}"
  let mut As : List (String × PLLFormula) := []
  for pc in Cs do
    let t2 ← IO.monoMsNow
    let raw := itpA "p" (spaceOf Θpool (nf (subC pc.2 MLob))) TFUEL 2
      Θpool (nf (subC pc.2 MLob))
    pl s!"    tower {pc.1}: raw weight {raw.weight}"
    let t3 ← IO.monoMsNow
    let A := nf raw
    pl s!"      nf weight {A.weight}"
    let t4 ← IO.monoMsNow
    pl s!"      (construct+weigh {t3 - t2} ms, nf+weigh {t4 - t3} ms)"
    As := As ++ [(pc.1, A)]

  let t5 ← IO.monoMsNow
  let poolF := nf (bigAnd (As.map (·.2)))
  let wPool := poolF.weight
  pl s!"    (pool conjunction forced: weight {wPool})"
  let t6 ← IO.monoMsNow
  let target := nf (subC (Cs.getD 0 default).2 gB)
  pl s!"(3) pool conjunction weight {wPool} ({t6 - t5} ms, forced); target (◯⊥)^C_a = {pf target}"
  let cm : FinCM := ⟨1, [], [], [], [(0, "a0")]⟩
  let seq := poolF :: Θpool
  let t7 ← IO.monoMsNow
  let ok := FinCM.checkB cm 0 seq target
  let t8 ← IO.monoMsNow
  pl s!"    one-world countermodel (only a0 true): checkB on the weight-{wPool + Θpool.length * 3 + target.weight} sequent = {ok}  ({t8 - t7} ms; inputs pre-forced)"
  pl "== done =="

end Repro

def main : IO Unit := Repro.main
