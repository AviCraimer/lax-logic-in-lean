import wip.confl_core

/-!
# Backward audit: which finite gadgets are mutually confluent?

Branch `ui-confluence`, task 5.  Every load-bearing FINITE
construction/countermodel of the semantic-UI development is run
through `confluentB` (the decidable form of `PLLND.MutuallyConfluent`
on the probe representation, reflexive closures built in).  A
countermodel certificate counts against CONFLUENT PLL only if the
model passes; non-confluent members are VOID for extension
refutations.

Also here (task 6): `decideU`, the oracle for the extension —
derivability in confluent PLL = the existing certified G4c search with
the finitely many relevant `distF` instances added to Γ (that is
`DerivU` verbatim, `PLLConfluentComplete.lean`); a refutation
certificate counts ONLY if the emitted countermodel passes
`confluentB`.

Run: `lake build conflaudit && .lake/build/bin/conflaudit`.
-/

open PLLFormula PLLND PLLND.Search ConflCore

namespace ConflAudit

def frameCM (f : Frame) : FinCM := ⟨f.n, f.ri, f.rm, f.fall, []⟩

def report (nm : String) (M : FinCM) : IO Unit :=
  IO.println s!"  {if confluentB M then "CONFLUENT    " else "NOT-CONFLUENT"}  {nm}  (n={M.n} ri={M.ri} rm={M.rm} fall={M.fall})"

/-- The named abstract models of the development, as `FinCM` data
(world numbering documented per line). -/
def named : List (String × FinCM) :=
  [ -- PLLSemUI.oneW: the one-world classical model (em_p_no_certificate)
    ("oneW (one-world classical)", ⟨1, [], [], [], []⟩),
    -- PLLFrames.modelOrSplit: r=0 below a=1, b=2; Rm = Ri
    ("modelOrSplit (F&M Fig.3 middle)", ⟨3, [(0,1),(0,2)], [(0,1),(0,2)], [], []⟩),
    -- PLLFrames.modelFallible: 0 ≤ 1 both relations, 1 fallible
    ("modelFallible (F&M Fig.3 left)", ⟨2, [(0,1)], [(0,1)], [1], []⟩),
    -- PLLFrames.modelNoImpDist: chain r=0 ≤ a=1 ≤ b=2, Rm refl + a→b
    ("modelNoImpDist (F&M Fig.3 right)", ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], []⟩),
    -- PLLSemUILayered.chainF: 0 ≤ 1, Rm = identity, top fallible
    ("chainF (fall-zigzag refuter)", ⟨2, [(0,1)], [], [1], []⟩),
    -- PLLSemUILayered.chainFM: 0 ≤ 1, Rm = Ri, top fallible
    ("chainFM (weak-escape refuter)", ⟨2, [(0,1)], [(0,1)], [1], []⟩),
    -- PLLSemUILayered.forkF: none=0, some false=1, some true=2;
    -- Ri: 0→1, 0→2; Rm: 0→2; 2 fallible
    ("forkF (pair-escape refuter)", ⟨3, [(0,1),(0,2)], [(0,2)], [2], []⟩),
    -- battery fork (mission hand-check: NOT confluent) = defaultFrames[8]
    ("battery fork ⟨3,[01,02],[02],[2]⟩", ⟨3, [(0,1),(0,2)], [(0,2)], [2], []⟩),
    -- frontier 4-chain (mission hand-check: IS confluent) = defaultFrames[10]
    ("frontier 4-chain ⟨4,…,[23],[3]⟩",
      ⟨4, [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)], [(2,3)], [3], []⟩),
    -- F-free gadget frames (task 5 list)
    ("gadget ⟨3,[01,12,02],[12],[]⟩", ⟨3, [(0,1),(1,2),(0,2)], [(1,2)], [], []⟩),
    ("gadget ⟨4,…,[23],[]⟩",
      ⟨4, [(0,1),(1,2),(2,3),(0,2),(0,3),(1,3)], [(2,3)], [], []⟩),
    -- PLLSemUIAdjoin.lobTowerBase instantiated over oneW
    -- (adjoin_reaches_lob): z=0, ⋆₁=1, ⋆₂=2; Ri: 0→1, 0→2, 2→1;
    -- Rm: 2→1 (the sideways promise)
    ("lobTower over oneW (adjoin_reaches_lob)",
      ⟨3, [(0,1),(0,2),(2,1)], [(2,1)], [], []⟩) ]

/-! ## Task 6: the oracle for the extension -/

/-- `distF A B` as concrete formula data (mirrors
`PLLND.ConfluentU.distF`). -/
def distF (A B : PLLFormula) : PLLFormula :=
  (somehow (A.or B)).ifThen ((somehow A).or (somehow B))

/-- Extension-aware answer: as `Search.Answer` but a refutation is
retained ONLY when the countermodel is mutually confluent (otherwise
the certificate is VOID for the extension and the verdict degrades to
`unknown`). -/
def decideU (dists : List (PLLFormula × PLLFormula))
    (Γ : List PLLFormula) (C : PLLFormula) (cfg : Config := {}) :
    String :=
  let Γ' := (dists.map fun p => distF p.1 p.2) ++ Γ
  match Search.decide cfg Γ' C with
  | .proved _ => "PROVED-in-extension"
  | .refuted M w _ =>
      if confluentB M then
        s!"REFUTED-in-extension (confluent countermodel n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} at w={w})"
      else
        s!"unknown (countermodel found but NOT confluent — VOID for the extension: n={M.n} ri={M.ri} rm={M.rm} fall={M.fall} val={M.val} at w={w})"
  | .unknown => "unknown"

def p : PLLFormula := .prop "p"
def q : PLLFormula := .prop "q"
def nF (A : PLLFormula) : PLLFormula := A.ifThen .falsePLL
def bx (A : PLLFormula) : PLLFormula := A.somehow

/-- Value re-checks in the extension (task 5, value-bearing rows).
Each `∀p.M = v` value splits into `⊢ instances` (holds-half, values
are PLL-formulas so the holds-half derivations transfer to the
extension outright) and per-instance failure certificates
(fails-half).  We test the two decisive fails-half instances per
value with the confluence-gated oracle: substituting the candidate
GREATER value's defining instance.  `distF` instances offered: the
ones over the atoms/boxes in play. -/
def valueChecks : List (String × List (PLLFormula × PLLFormula) ×
    List PLLFormula × PLLFormula) :=
  [ -- ∀p.(p ∨ ¬p): candidate value ⊥; fails-half needs ⊬ instances
    -- above ⊥, e.g. the q-instance and the ◯⊥-closure instance.
    ("em: ⊢? (q ∨ ¬q)", [(q, nF q)], [], q.or (nF q)),
    ("em: ⊢? (◯⊥ ∨ ¬◯⊥)", [(bx .falsePLL, nF (bx .falsePLL))], [],
      (bx .falsePLL).or (nF (bx .falsePLL))),
    -- ∀p.(◯p ⊃ p): candidate ⊥
    ("box-imp: ⊢? (◯q ⊃ q)", [(q, q)], [], (bx q).ifThen q),
    ("box-imp: ⊢? (◯◯⊥ ⊃ ◯⊥)", [(bx .falsePLL, bx .falsePLL)], [],
      (bx (bx .falsePLL)).ifThen (bx .falsePLL)),
    -- ∀p.◯(◯p ⊃ p): candidate ◯⊥ — fails-half: ◯(◯q⊃q) ⊬ ◯⊥ and
    -- ⊬ ◯(◯q⊃q); holds-half: ◯⊥ ⊢ ◯(◯q⊃q).
    ("lob: ◯(◯q⊃q) ⊢? ◯⊥", [(q, .falsePLL), (bx q, q)],
      [bx ((bx q).ifThen q)], bx .falsePLL),
    ("lob: ⊢? ◯(◯q⊃q)", [(q, .falsePLL), (bx q, q)], [],
      bx ((bx q).ifThen q)),
    ("lob holds-half: ◯⊥ ⊢? ◯(◯q⊃q)", [], [bx .falsePLL],
      bx ((bx q).ifThen q)),
    -- the frontier row ∀p.(((p⊃◯⊥)⊃p)⊃p): candidate ◯⊥ —
    -- fails-half: ((q⊃◯⊥)⊃q)⊃q ⊬ ◯⊥ and ⊬ the row itself.
    ("frontier: (((q⊃◯⊥)⊃q)⊃q) ⊢? ◯⊥", [(q, bx .falsePLL)],
      [((q.ifThen (bx .falsePLL)).ifThen q).ifThen q], bx .falsePLL),
    ("frontier: ⊢? (((q⊃◯⊥)⊃q)⊃q)", [(q, bx .falsePLL)], [],
      ((q.ifThen (bx .falsePLL)).ifThen q).ifThen q) ]

def mainLoop : IO Unit := do
  IO.println "## defaultFrames (Search battery, in order):"
  let mut i := 0
  for f in defaultFrames do
    report s!"defaultFrames[{i}]" (frameCM f)
    i := i + 1
  IO.println "## named gadgets:"
  for (nm, M) in named do
    report nm M
  IO.println "## extension oracle value re-checks (confluence-gated):"
  for (nm, ds, Γ, C) in valueChecks do
    IO.println s!"  {nm}  →  {decideU ds Γ C {findBudget := some 40000}}"

end ConflAudit

def main : IO Unit := ConflAudit.mainLoop
