import LaxLogic.PLLCtxCompleteness
import LaxLogic.PLLG4UITrunc
import LaxLogic.PLLG4Dec
import LaxLogic.PLLG4Term

/-!
# Probe: the constraint-commutation conjecture (Matthew, 2026-07-19)

Conjecture under test: for each one-variable M there is a standard
constraint C (built from M, à la Lemma 7) such that

    ∀ᴵᴾᶜ p.(M^C)  ≡ᴵᴾᶜ  (∀p.M)^C        (dually for ∃p)

where `M^C = subC C M` is the mechanised constraint substitution
(each ◯ψ ↦ C[ψ^C]), the right-hand ∀p.M is the KNOWN PLL-value from
the value table (spec-verified), and ∀ᴵᴾᶜ is computed by the box-free
tower interpolants `itpA`/`itpE` (adequate for IPC by the mechanised
IPC crown).

Constraints tested: `c0Of` implements Lemma 7's recipe on concrete
finite models — pairs `(α_u, ⋁{α_v : v covers u})` over the Rₘ-stable
worlds u, with fresh atoms `a0, a1, …` naming worlds.

Method notes: all formulas nf-simplified (Heyting ⊥/⊤ laws only fire
on the box-free side, all PLL-equivalences); tower values computed at
budgets b = 1,2,3 with hand fuel, stabilisation and fuel-indifference
oracle-checked; `true` verdicts are sound, `false` = not-found within
budget.  Run with `lake env lean --run wip/semui_ctx_probe.lean`.
-/

open PLLFormula PLLND PLLND.Ctx

namespace CtxProbe

/-! ## Oracle -/

/-- Fuel-free oracle (2026-07-19 upgrade): `G4cTm.find` — loop-checked
term search, fails fast on the shapes that made the fueled `search`
chaotic.  Sound on `true` (a term exists); `false` is tool-grade. -/
def prov (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  (G4cTm.find Γ C).isSome
def equivO (X Y : PLLFormula) : Bool := prov [X] Y && prov [Y] X

def pf (F : PLLFormula) : String := F.toString

/-! ## Normaliser (PLL-equivalences; on box-free formulas pure Heyting) -/

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

/-! ## Piece closure (verbatim from wip/packaging.lean) -/

def pieceClosure : PLLFormula → Finset PLLFormula
  | .prop a => {PLLFormula.prop a}
  | .falsePLL => {falsePLL}
  | .and A B => insert (A.and B) (pieceClosure A ∪ pieceClosure B)
  | .or A B => insert (A.or B) (pieceClosure A ∪ pieceClosure B)
  | .ifThen (.prop a) D =>
      insert ((PLLFormula.prop a).ifThen D)
        (pieceClosure (PLLFormula.prop a) ∪ pieceClosure D)
  | .ifThen .falsePLL D =>
      insert (falsePLL.ifThen D) (pieceClosure falsePLL ∪ pieceClosure D)
  | .ifThen (.and A B) D =>
      insert ((A.and B).ifThen D)
        (pieceClosure (A.and B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen (B.ifThen D)))
  | .ifThen (.or A B) D =>
      insert ((A.or B).ifThen D)
        (pieceClosure (A.or B) ∪ pieceClosure D
          ∪ pieceClosure (A.ifThen D) ∪ pieceClosure (B.ifThen D))
  | .ifThen (.ifThen A B) D =>
      insert ((A.ifThen B).ifThen D)
        (pieceClosure (A.ifThen B) ∪ pieceClosure D
          ∪ pieceClosure (B.ifThen D))
  | .ifThen (.somehow X) D =>
      insert ((somehow X).ifThen D)
        (pieceClosure (somehow X) ∪ pieceClosure D)
  | .somehow χ => insert χ.somehow (pieceClosure χ)
termination_by φ => φ.weight
decreasing_by all_goals (simp only [PLLFormula.weight]; omega)

/-! ## Finite models as tables, and Lemma 7's constraint -/

structure FinModel where
  n : Nat
  ri : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  fal : Nat → Bool

def worlds (m : FinModel) : List Nat := List.range m.n

def name (i : Nat) : PLLFormula := .prop s!"a{i}"

def stable (m : FinModel) (u : Nat) : Bool :=
  (worlds m).all (fun t => !(m.rm u t) || m.rm t u)

def iSuccB (m : FinModel) (u v : Nat) : Bool :=
  m.ri u v && !(m.ri v u) &&
    (worlds m).all (fun t => !(m.ri u t) || !(m.ri t v) || (m.ri t u || m.ri v t))

/-- Lemma 7's constraint: `(α_u, ⋁{α_v : v covers u})` over stable u. -/
def c0Of (m : FinModel) : StdCtx :=
  ((worlds m).filter (stable m)).map (fun u =>
    (name u, Ctx.bigOr (((worlds m).filter (iSuccB m u)).map name)))

/-! ## Test models -/

/-- Two-chain 0 < 1, top fallible, Rₘ = Rᵢ. -/
def mChain2 : FinModel where
  n := 2
  ri := fun a b => a ≤ b
  rm := fun a b => a ≤ b
  fal := fun a => a == 1

/-- Three-chain 0 < 1 < 2, top fallible, Rₘ rigid except 1 → 2. -/
def mChain3 : FinModel where
  n := 3
  ri := fun a b => a ≤ b
  rm := fun a b => a == b || (a == 1 && b == 2)
  fal := fun a => a == 2

/-- The fork: 0 < 1 (terminal), 0 < 2 < 3 (fallible), Rₘ rigid except
2 → 3 — the shape of the ∃-side countermodel C4. -/
def mFork : FinModel where
  n := 4
  ri := fun a b => a == b || (a == 0) || (a == 2 && b == 3)
  rm := fun a b => a == b || (a == 2 && b == 3)
  fal := fun a => a == 3

/-! ## Targets: (name, M, known ∀p-value, known ∃p-value) -/

def pV : PLLFormula := .prop "p"
def gB : PLLFormula := PLLFormula.falsePLL.somehow
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL

def targets : List (String × PLLFormula × PLLFormula × PLLFormula) :=
  [ ("p∨¬p (no ◯: pure IPC calib)", pV.or (nF pV), .falsePLL, truePLL)
  , ("◯p          ", pV.somehow, gB, truePLL)
  , ("◯p⊃p        ", (pV.somehow).ifThen pV, .falsePLL, truePLL)
  , ("¬p          ", nF pV, .falsePLL, truePLL)
  , ("◯⊥⊃p        ", gB.ifThen pV, nF gB, truePLL)
  , ("(◯⊥⊃p)⊃p    ", (gB.ifThen pV).ifThen pV, gB, truePLL)
  , ("¬◯p         ", nF (pV.somehow), .falsePLL, nF gB)
  , ("◯⊥∧p        ", gB.and pV, .falsePLL, gB)
  , ("◯(◯p⊃p)     ", ((pV.somehow).ifThen pV).somehow, gB, truePLL)
  ]

/-! ## The tower quantifiers, probe-side -/

def WCAP : Nat := 120

def TFUEL : Nat := 120

def towerA (T : PLLFormula) (b : Nat) : PLLFormula :=
  nf (itpA "p" (pieceClosure T) TFUEL b [] T)

def towerE (T : PLLFormula) (b : Nat) : PLLFormula :=
  nf (itpE "p" (pieceClosure T) TFUEL b [T])

def main : IO Unit := do
  let out ← IO.getStdout
  let pl (s : String) : IO Unit := do out.putStrLn s; out.flush
  pl "== constraint-commutation probe =="
  for (mname, m) in [("chain2", mChain2), ("chain3", mChain3), ("fork", mFork)] do
    let C := c0Of m
    pl s!"-- model {mname}: C = {C.map (fun kl => (pf kl.1, pf kl.2))}"
    for (tname, M, vA, vE) in targets do
      let T := nf (subC C M)
      let vA' := nf (subC C vA)
      let vE' := nf (subC C vE)
      if T.weight > WCAP || (pieceClosure T).card > 30 then
        pl s!"   {tname}: T-SKIPPED (w={T.weight}, |S|={(pieceClosure T).card})"
      else
        let t0 ← IO.monoMsNow
        -- sanity: the translated value is below/above the translated M
        let sane := prov [vA'] T
        -- tower ∀: budgets 1,2 + stabilisation
        let A2 := towerA T 1
        let A3 := towerA T 2
        let stabA := if A2.weight + A3.weight ≤ 2*WCAP then equivO A2 A3 else false
        let commA := if A3.weight + vA'.weight ≤ 2*WCAP then equivO A3 vA' else false
        -- tower ∃
        let E2 := towerE T 1
        let E3 := towerE T 2
        let stabE := if E2.weight + E3.weight ≤ 2*WCAP then equivO E2 E3 else false
        let commE := if E3.weight + vE'.weight ≤ 2*WCAP then equivO E3 vE' else false
        let t1 ← IO.monoMsNow
        pl s!"   {tname}: Tw={T.weight} sane={sane} | ∀: stab={stabA} comm={commA} (A2={pf A3}, vA'={pf vA'}) | ∃: stab={stabE} comm={commE} (E2={pf E3}, vE'={pf vE'})  ({t1 - t0} ms)"
  pl "== done =="

end CtxProbe

def main : IO Unit := CtxProbe.main
