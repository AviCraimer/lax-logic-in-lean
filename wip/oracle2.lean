import LaxLogic.PLLCountermodelEmit
import LaxLogic.PLLG4Dec
import LaxLogic.PLLG4Term
import LaxLogic.PLLSemUI

/-!
# oracle2 — the packaged two-sided decision TOOL (countermodel-first)

Matthew's resource directive (2026-07-19): a failing proof search must
try every route, so its cost is chaotic; a decision tool should attempt
CHEAP COUNTERMODELS first/instead, because checking a proposed
countermodel is cheap (the tools-vs-proofs discipline: the tool may be
fallible, its accepted outputs are verified).

The library already has both sides (belief session, 2026-07-18):
`search` (sound-on-true, fueled), `G4cTm.find` (fuel-free terms),
`CounterEmit.emit` + verified `FinCM.checkB` + `not_provable_of_check`
(certified refutations).  What was missing — and what bit the
semantic-UI probes — is the CHEAP negative stage and the staging
policy.  This file packages:

* a battery of ≤4-world frames (the shapes that refuted everything the
  UI programme met: chains, rigid chains, the fork, the doubling);
* `sweep` — enumerate hereditary decorations of the battery frames
  over the sequent's atoms and gate each candidate through the
  VERIFIED checker `FinCM.checkB` (a wrong guess cannot certify);
* `decide2` — the staged verdict, COUNTERMODELS FIRST and FUEL
  DEMOTED (v3):
    0. `nf` both sides (the built simplification measures; scanning
       and search run on nf-forms, certificates are re-gated against
       the ORIGINAL sequent);
    1. `sweep` (cheap certified negative);
    2. `G4cTm.find` (the fuel-free term search — complete positive
       engine, no hand-tuned fuel; returns a kernel-checkable term);
    3. `CounterEmit.emit`, gated by closure size (complete-flavoured
       negative, exponential);
    4. unknown.
  Residual exposure: an unprovable sequent that escapes the battery
  makes `find` grind (it terminates, but exponentially) — that is the
  case `emit` exists for, and the benchmark's job is to show the
  battery does not miss.

TRUST: `.refuted` verdicts carry a `(FinCM, world)` pair that passed
`checkB`; `not_provable_of_check` upgrades any such pair to a
machine-checked `¬ Nonempty (LaxND Γ C)` by `decide` when a paper-grade
certificate is wanted.  `.proved` verdicts are `search`/`find`
successes (kernel-grade via their soundness theorems).  `unknown` is
honest.

Run: `lake env lean --run wip/oracle2.lean` (benchmark harness in
`main`; compares against the plain one-sided oracle).
-/

open PLLFormula PLLND PLLND.SemUI

namespace Oracle2

/-! ## The normaliser (PLL-equivalences; the built simplification measures)

Heyting ⊥/⊤ laws + `◯⊤ ≡ ⊤` + `◯◯ ≡ ◯` — every rewrite is a PLL
equivalence, hence valid on all constraint models: a model refutes the
nf-form iff it refutes the original, and provability transfers both
ways.  Scanning and searching run on nf-forms (smaller); the verified
`checkB` gate is applied to the ORIGINAL sequent, so certificates are
about what was asked. -/

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

/-! ## Frames and hereditary decorations -/

structure Frame where
  n : Nat
  ri : List (Nat × Nat)    -- strict part, transitively closed
  rm : List (Nat × Nat)    -- ⊆ ri
  fall : List Nat

/-- The battery: every shape that refuted something in the UI
programme, smallest first.  (1) classical point, (2) fallible point,
(3) chain2 Rm=Ri, (4) chain2 rigid, (5) chain2 no-F, (6) chain3 rigid
except 1→2 (the Löb shape), (7) chain3 full, (8) the fork (C4 shape),
(9) the V (C3 shape), (10) doubled chain2. -/
def frames : List Frame :=
  [ ⟨1, [], [], []⟩
  , ⟨1, [], [], [0]⟩
  , ⟨2, [(0,1)], [(0,1)], [1]⟩
  , ⟨2, [(0,1)], [], [1]⟩
  , ⟨2, [(0,1)], [(0,1)], []⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [2]⟩
  , ⟨3, [(0,1),(1,2),(0,2)], [(0,1),(1,2),(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(2,3),(0,3)], [(2,3)], [3]⟩
  , ⟨3, [(0,1),(0,2)], [(0,2)], [2]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,3),(2,3)], [(1,3),(2,3)], [3]⟩
  , ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3]⟩ ]

def riStep (f : Frame) (w v : Nat) : Bool := (w, v) ∈ f.ri

/-! ## Fast untrusted evaluation: bottom-up world vectors

`FinCM.forceB` recomputes subformulas once per visited world, so its
cost is `n^depth` — minutes on weight-40 sequents.  The scan below
evaluates each subformula ONCE as a vector over all worlds (`weight ×
n²` total), and only candidates that pass the fast scan are handed to
the VERIFIED `FinCM.checkB` (one call, on a hit).  The tool may be
wrong only by MISSING countermodels, never by accepting one. -/

def riR (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.ri) || decide (w = v)
def rmR (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.rm) || decide (w = v)

def forceV (M : FinCM) : PLLFormula → Array Bool
  | .prop a => (Array.range M.n).map fun w =>
      decide ((w, a) ∈ M.val) || decide (w ∈ M.fall)
  | .falsePLL => (Array.range M.n).map fun w => decide (w ∈ M.fall)
  | .and A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false && vB.getD w false
  | .or A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w => vA.getD w false || vB.getD w false
  | .ifThen A B =>
      let vA := forceV M A; let vB := forceV M B
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) || !(vA.getD v false) || vB.getD v false
  | .somehow A =>
      let vA := forceV M A
      (Array.range M.n).map fun w =>
        (List.range M.n).all fun v =>
          !(riR M w v) ||
            (List.range M.n).any fun u => rmR M v u && vA.getD u false

def fastCheck (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Bool :=
  Γ.all (fun F => (forceV M F).getD w false) && !((forceV M C).getD w false)

/-- Truth-sets as bitmasks: hereditary along `ri` and full on `fall`. -/
def admissible (f : Frame) : List Nat :=
  (List.range (2 ^ f.n)).filter fun m =>
    ((List.range f.n).all fun w =>
      !(m.testBit w) ||
        (List.range f.n).all fun v => !(riStep f w v) || m.testBit v) &&
    (f.fall.all fun w => m.testBit w)

def assigns : List String → List Nat → List (List (String × Nat))
  | [], _ => [[]]
  | a :: as, adm =>
      (assigns as adm).flatMap fun rest => adm.map fun m => (a, m) :: rest

def toFinCM (f : Frame) (asgn : List (String × Nat)) : FinCM :=
  { n := f.n, ri := f.ri, rm := f.rm, fall := f.fall
    val := asgn.flatMap fun am =>
      (List.range f.n).filterMap fun w =>
        if am.2.testBit w then some (w, am.1) else none }

def atomList : PLLFormula → List String
  | .prop a => [a]
  | .falsePLL => []
  | .and A B | .or A B | .ifThen A B => atomList A ++ atomList B
  | .somehow A => atomList A

def atomsOf (l : List PLLFormula) : List String :=
  (l.flatMap atomList).eraseDups

/-- Cheap certified negative: scan the battery with the fast vector
evaluator ON THE NF-FORMS, gate every hit through the VERIFIED
`FinCM.checkB` ON THE ORIGINAL sequent (nf is model-equivalence, so
the same model refutes both; the certificate is about what was
asked). -/
def sweep (Γ' : List PLLFormula) (C' : PLLFormula)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (FinCM × Nat) :=
  let ats := atomsOf (C' :: Γ')
  frames.findSome? fun f =>
    let adm := admissible f
    if adm.length ^ ats.length > 100000 then none
    else
      (assigns ats adm).findSome? fun asgn =>
        let M := toFinCM f asgn
        let vΓ := Γ'.map (forceV M)
        let vC := forceV M C'
        (List.range f.n).findSome? fun w =>
          if vΓ.all (fun v => v.getD w false) && !(vC.getD w false) &&
              FinCM.checkB M w Γ C then
            some (M, w)
          else none

/-! ## The staged verdict -/

inductive Verdict where
  | proved : Verdict
  | refuted : FinCM → Nat → Verdict
  | unknown : Verdict

def searchAt (fuel : Nat) (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  search (listWeight (C :: Γ)) (listAtoms (C :: Γ)) fuel ∅ Γ C

def EMIT_CLOSURE_CAP : Nat := 12

/-- v3 staging, fuel demoted: nf-preprocess; battery countermodels
first; the fuel-free term search `G4cTm.find` as THE positive engine
(complete, no hand-tuning — the belief-session tool, previously left
on the shelf); a single cheap fueled probe only as a pre-step to the
exponential `emit`, never as the arbiter. -/
def decide2 (Γ : List PLLFormula) (C : PLLFormula) : Verdict :=
  let Γ' := Γ.map nf
  let C' := nf C
  match sweep Γ' C' Γ C with
  | some (M, w) => .refuted M w
  | none =>
    if (G4cTm.find Γ' C').isSome then .proved
    else if (CounterEmit.closureOf Γ' C').length ≤ EMIT_CLOSURE_CAP then
      match CounterEmit.emit Γ' C' with
      | some (M, w) =>
          -- emit certified the nf-sequent; re-gate the original
          if FinCM.checkB M w Γ C then .refuted M w else .unknown
      | none => .unknown
    else .unknown

/-! ## Benchmark harness -/

def pf (F : PLLFormula) : String := F.toString

def showVerdict : Verdict → String
  | .proved => "PROVED"
  | .refuted M w =>
      s!"REFUTED (n={M.n} fall={M.fall} val={M.val} @w{w})"
  | .unknown => "UNKNOWN"

def pV : PLLFormula := .prop "p"
def qV : PLLFormula := .prop "q"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def peirceF : PLLFormula := (gB.ifThen pV).ifThen pV

/-- (name, Γ, C, expected: some true = provable). -/
def cases : List (String × List PLLFormula × PLLFormula × Option Bool) :=
  [ ("T1  ⊢ p⊃p",            [], pV.ifThen pV, some true)
  , ("T2  ◯◯p ⊢ ◯p",         [pV.somehow.somehow], pV.somehow, some true)
  , ("T3  ◯⊥ ⊢ ◯p",          [gB], pV.somehow, some true)
  , ("T4  allCand(◯p⊃p) ⊢ ◯p⊃p",
      [allCand "p" ((pV.somehow).ifThen pV)], (pV.somehow).ifThen pV, some true)
  , ("T5  p⊃q, ◯p ⊢ ◯q",     [pV.ifThen qV, pV.somehow], qV.somehow, some true)
  , ("U1  ¬¬◯⊥ ⊢ ◯⊥",        [nF (nF gB)], gB, some false)
  , ("U2  allCand(peirce) ⊢ peirce",
      [allCand "p" peirceF], peirceF, some false)
  , ("U3  ⊢ ◯p⊃p",           [], (pV.somehow).ifThen pV, some false)
  , ("U4  ◯(◯p⊃p) ⊢ ◯⊥",     [((pV.somehow).ifThen pV).somehow], gB, some false)
  , ("U5  (◯⊥⊃p)⊃p ⊢ ◯⊥",    [peirceF], gB, some false)
  ]

def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  let findOnly := args.contains "find"
  let mode := if findOnly then " [find-only mode]" else ""
  pl s!"== oracle2 v3: nf → battery → find → emit{mode} =="
  for (name, Γ, C, exp) in cases do
    if findOnly then
      -- raw fuel-free term search, no battery (run timeboxed from outside)
      let t0 ← IO.monoMsNow
      let r := (G4cTm.find (Γ.map nf) (nf C)).isSome
      let t1 ← IO.monoMsNow
      pl s!"{name}: find={r}  ({t1 - t0} ms)"
    else
      let t0 ← IO.monoMsNow
      let v := decide2 Γ C
      let t1 ← IO.monoMsNow
      let ok := match v, exp with
        | .proved, some true => "✓"
        | .refuted _ _, some false => "✓"
        | .unknown, _ => "?"
        | _, _ => "✗ MISMATCH"
      pl s!"{name}: {showVerdict v}  {ok}  ({t1 - t0} ms)"
  pl "== done =="

end Oracle2

