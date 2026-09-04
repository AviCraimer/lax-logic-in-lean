import wip.oracle2
import wip.semui_ctx_core

/-!
# Probe: the constraint-POOL experiment (variant saturations)

Question (route doc §0(p) endgame): the model-level dichotomy shows a
SINGLE Lemma-7 constraint cannot reach `∀p.M` on the frame-changing
rows when the model has a non-fallible Rₘ-stable world.  Does a POOL
of constraints — the model's own `c0Of` together with the `c0Of` of
its DOUBLING and its 3-level LÖB variant, on disjoint alphabets —
close the gap?  Candidate value = the meet `A_a ∧ A_b ∧ A_c` of the
per-constraint relative tower values; target = the translated PLL
value; verdicts by the two-sided oracle (battery restricted to the
non-Θ-negated atoms; positive side `G4cTm.find`, weight-gated).

Attribution: pools {a}, {a,b}, {a,c}, {a,b,c} are all tested — {a}
is the certified-failing baseline; any flip to PROVED names the
variant that does the work.

Register: PROVED verdicts are find-terms (sound); REFUTED verdicts
are checkB-gated countermodels (sound); UNKNOWN is honest (battery
≤ 4 worlds; find gated).  Run: `lake build poolprobe && .lake/build/bin/poolprobe`.
-/

open PLLFormula PLLND PLLND.Ctx

namespace PoolProbe

/-! ## Variant models on tables -/

/-- The doubling: two stacked copies, both relations monotone into the
upper copy (the frame of `PLLSemUI.double`). -/
def doubleM (m : CtxRel.FinModel) : CtxRel.FinModel where
  n := 2 * m.n
  ri := fun x y =>
    m.ri (x % m.n) (y % m.n) && (decide (x < m.n) || !(decide (y < m.n)))
  rm := fun x y =>
    m.rm (x % m.n) (y % m.n) && (decide (x < m.n) || !(decide (y < m.n)))
  fal := fun x => m.fal (x % m.n)

/-- The 3-level Löb variant: `Rᵢ` level-monotone, `Rₘ` level-rigid
except the single step 1 → 2 (the frame of `PLLSemUI.lobModel`,
truncated at the provably-homogeneous level 2). -/
def lobM (m : CtxRel.FinModel) : CtxRel.FinModel where
  n := 3 * m.n
  ri := fun x y =>
    m.ri (x % m.n) (y % m.n) && decide (x / m.n ≤ y / m.n)
  rm := fun x y =>
    m.rm (x % m.n) (y % m.n) &&
      (decide (x / m.n = y / m.n) ||
        (decide (x / m.n = 1) && decide (y / m.n = 2)))
  fal := fun x => m.fal (x % m.n)

/-! ## Prefixed naming, c0Of, fallibility axioms -/

def pname (pre : String) (i : Nat) : PLLFormula := .prop s!"{pre}{i}"

def pc0Of (pre : String) (m : CtxRel.FinModel) : StdCtx :=
  ((CtxRel.worlds m).filter (CtxRel.stable m)).map (fun u =>
    (pname pre u, Ctx.bigOr (((CtxRel.worlds m).filter (CtxRel.iSuccB m u)).map (pname pre))))

def pfalAx (pre : String) (m : CtxRel.FinModel) : List PLLFormula :=
  ((CtxRel.worlds m).filter m.fal).map (fun w => (pname pre w).ifThen .falsePLL)

/-! ## The pool oracle: certified two-sided, atoms restricted -/

/-- Battery sweep over an EXPLICIT atom list (the pool sequents carry
~18 atoms, but only the non-Θ-negated guard names matter for
countermodels; the verified `checkB` gate keeps wrong guesses out
regardless). -/
def sweepAts (ats : List String) (Γ : List PLLFormula) (C : PLLFormula) :
    Option (FinCM × Nat) :=
  Oracle2.frames.findSome? fun f =>
    let adm := Oracle2.admissible f
    if adm.length ^ ats.length > 200000 then none
    else
      (Oracle2.assigns ats adm).findSome? fun asgn =>
        let M := Oracle2.toFinCM f asgn
        let vΓ := Γ.map (Oracle2.forceV M)
        let vC := Oracle2.forceV M C
        (List.range f.n).findSome? fun w =>
          if vΓ.all (fun v => v.getD w false) && !(vC.getD w false) &&
              FinCM.checkB M w Γ C then
            some (M, w)
          else none

def FIND_WCAP : Nat := 600

def decide2P (Θnames : List String) (Γ : List PLLFormula) (C : PLLFormula) :
    Oracle2.Verdict :=
  let ats := (Oracle2.atomsOf (C :: Γ)).filter (fun a => !(Θnames.contains a))
  match sweepAts ats Γ C with
  | some (M, w) => .refuted M w
  | none =>
      if listWeight (C :: Γ) ≤ FIND_WCAP then
        if (G4cTm.find Γ C).isSome then .proved else .unknown
      else .unknown

def showV : Oracle2.Verdict → String
  | .proved => "PROVED"
  | .refuted M w => s!"REFUTED (n={M.n} fall={M.fall} val={M.val} @w{w})"
  | .unknown => "UNKNOWN"

/-! ## Targets and models -/

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow

def bigAnd : List PLLFormula → PLLFormula
  | [] => truePLL
  | [x] => x
  | x :: xs => x.and (bigAnd xs)

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== constraint-POOL experiment (variant saturations) =="
  for (mname, m) in
      [("chain2 (control)", CtxRel.mChain2), ("chain3", CtxRel.mChain3),
       ("fork", CtxRel.mFork)] do
    let variants := [("a", m), ("b", doubleM m), ("c", lobM m)]
    let Cs := variants.map (fun pv => (pv.1, pc0Of pv.1 pv.2))
    let Θpool := variants.flatMap (fun pv => pfalAx pv.1 pv.2)
    let Θnames := Θpool.filterMap (fun ψ =>
      match ψ with | .ifThen (.prop a) _ => some a | _ => none)
    pl s!"-- {mname}: |C_a|={(Cs.getD 0 default).2.length} |C_b|={(Cs.getD 1 default).2.length} |C_c|={(Cs.getD 2 default).2.length} |Θ|={Θpool.length}"
    for (rname, M, targf) in
        [("◯p⊃p (value ⊥)", (pV.somehow).ifThen pV,
          fun (_ : StdCtx) => PLLFormula.falsePLL),
         ("◯(◯p⊃p) (value ◯⊥)", ((pV.somehow).ifThen pV).somehow,
          fun (Ca : StdCtx) => CtxRel.nf (subC Ca gB))] do
      let t0 ← IO.monoMsNow
      let As := Cs.map (fun pc =>
        (pc.1, CtxRel.towerARel Θpool (CtxRel.nf (subC pc.2 M)) 2))
      let t1 ← IO.monoMsNow
      let ws := As.map (fun pa => (pa.1, pa.2.weight))
      pl s!"   {rname}: towers {ws} ({t1 - t0} ms)"
      let target := targf (Cs.getD 0 default).2
      for sel in [["a"], ["a", "b"], ["a", "c"], ["a", "b", "c"]] do
        let P := (As.filter (fun pa => sel.contains pa.1)).map (·.2)
        let poolF := CtxRel.nf (bigAnd P)
        let t2 ← IO.monoMsNow
        let v := decide2P Θnames (poolF :: Θpool) target
        let t3 ← IO.monoMsNow
        pl s!"      pool {sel}: {showV v}  (w={poolF.weight}, {t3 - t2} ms)"
  pl "== done =="

end PoolProbe

def main : IO Unit := PoolProbe.main
