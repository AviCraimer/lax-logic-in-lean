import round5refute
import Plausible

/-! # Calibration scratch for the frontier sampler (not part of the deliverable)

Two questions, answered by measurement before any harness is written:

1. does `import Plausible` co-exist with the tower stack, and does its `Gen`
   run PURELY and REPRODUCIBLY from an explicit seed?
2. what does a countermodel-ONLY triage (`refute?` with `emitClosureCap := 0`,
   i.e. the certified battery and nothing else) cost per cell, at the sizes
   the sampler will generate?
-/

open PLLFormula PLLND PLLND.Search Plausible

namespace PLLND
namespace FrontierCalib

/-- Pure, seeded, reproducible run of a Plausible generator. -/
def runSeeded {α : Type} (seed size : Nat) (g : Gen α) : Option α :=
  ((runRandWith seed g : ReaderT (ULift Nat) (Except GenError) α).run
    ⟨size⟩).toOption

/-- A toy formula generator, to check `Gen` composes with `PLLFormula`. -/
partial def genF : Nat → Gen PLLFormula
  | 0 => do
      let i ← Gen.choose Nat 0 2 (by omega)
      pure (prop (["a", "b", "c"].getD i.val "a"))
  | (d + 1) => do
      let k ← Gen.choose Nat 0 3 (by omega)
      match k.val with
      | 0 => genF 0
      | 1 => do let A ← genF d; pure A.somehow
      | 2 => do let A ← genF d; let B ← genF d; pure (A.ifThen B)
      | _ => do let A ← genF d; let B ← genF d; pure (A.or B)

#eval (runSeeded 3 4 (genF 3)).map reprStr
#eval (runSeeded 3 4 (genF 3)).map reprStr   -- must be identical
#eval (runSeeded 4 4 (genF 3)).map reprStr   -- must differ

/-! ## Triage cost -/

/-- Countermodel-only configuration: the battery, with the exponential
closure emitter OFF and no positive stage at all. -/
def cfg0 : Config :=
  { frames := Round5Refute.xFrames ++ defaultFrames, emitClosureCap := 0 }

def timeCell (nm : String) (Γ : List PLLFormula) (C : PLLFormula) : IO Unit := do
  let t0 ← IO.monoMsNow
  let n ← IO.lazyPure (fun _ => (Γ.map TowerKit.sz).sum + TowerKit.sz C)
  let a ← IO.lazyPure (fun _ => (atomsOf (C :: Γ)).length)
  let v ← IO.lazyPure (fun _ => (refute? cfg0 Γ C).isSome)
  let t1 ← IO.monoMsNow
  IO.println s!"{nm}: refuted={v} |Γ+C|={n} atoms={a} ({t1 - t0} ms)"

/-! Live-fire control: the round-4 unboxed instance, known refutable. -/
#eval timeCell "CTRL unboxed (expect refuted=true)"
  [Round4Probe3.srcU, Round4Probe3.ambB] Round4Probe3.tgtU

/-! The boxed form at the same instance: known NOT refuted by these models. -/
#eval timeCell "CTRL boxed (expect refuted=false)"
  [Round4Probe3.srcB, Round4Probe3.ambB] Round4Probe3.tgtB

/-! A small `J = 0` cell at its own room. -/
#eval timeCell "BB/miss-e b=2 f=(4,4)"
  [Round5Refute.srcOf Round5Refute.i31 4 2, Round5Refute.ambOf Round5Refute.i31 4 2]
  (Round5Refute.tgtOf Round5Refute.i31 4 2)

/-! The `S3`-shaped nested-box residue cell of PROGRESS §62/§63.

Lean trap: a `/-- … -/` docstring may not precede `#eval`; use `/-! … -/`. -/
#eval timeCell "JB2/miss-c b=3 f=(5,5)"
  [Round5Refute.srcOf Round5Refute.i21 5 3, Round5Refute.ambOf Round5Refute.i21 5 3]
  (Round5Refute.tgtOf Round5Refute.i21 5 3)

end FrontierCalib
end PLLND
