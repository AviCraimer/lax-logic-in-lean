import FrontierSampler.Core

/-!
# A complete worked instantiation, with no dependencies

The property under test: over a tiny modal-ish formula language, is
`⊨ boxed φ → boxed (φ ∨ ψ)` decided the same way by two evaluators — a
direct one and a normalising one?  The point is not the property; it is the
SHAPE of the campaign, which is the same shape the PLL instantiation uses:

* **strata** by nesting depth (0, 1, 2, 3), one level beyond where the two
  evaluators are known to agree;
* an **admissibility gate** — the instance must be in normal form and must
  mention at least two distinct atoms; an ungated generator produces mostly
  degenerate instances and a run of those proves nothing;
* **countermodel-only triage** — a `hit` is a concrete disagreement, and
  everything else is `quiet`, never "passed";
* a **corpus** line per cell, replayable against a different property later.

Generation here uses the dependency-free `Splitmix` fallback so that the
package builds and this file runs with no packages installed.  In practice
use `Plausible.Gen` and the one-line adapter in the README.
-/

namespace FrontierSampler
namespace Example

/-! ## The object language -/

inductive Fml where
  | atom : Nat → Fml
  | disj : Fml → Fml → Fml
  | box : Fml → Fml
  deriving DecidableEq, Repr, Inhabited

def Fml.render : Fml → String
  | .atom n => s!"p{n}"
  | .disj a b => s!"({a.render} ∨ {b.render})"
  | .box a => s!"□{a.render}"

def Fml.depth : Fml → Nat
  | .atom _ => 0
  | .disj a b => 1 + max a.depth b.depth
  | .box a => 1 + a.depth

def Fml.atoms : Fml → List Nat
  | .atom n => [n]
  | .disj a b => (a.atoms ++ b.atoms).eraseDups
  | .box a => a.atoms

/-- Normal form: no `□` immediately under `□`. -/
def Fml.normal : Fml → Bool
  | .atom _ => true
  | .disj a b => a.normal && b.normal
  | .box (.box _) => false
  | .box a => a.normal

/-! ## The generator: seeded, pure, one instance per seed -/

/-- Generate a formula of depth at most `d`. -/
partial def gen (d : Nat) (s : UInt64) : Fml × UInt64 :=
  match d with
  | 0 => let (n, s') := Splitmix.draw s 3; (.atom n, s')
  | d + 1 =>
    let (k, s₁) := Splitmix.draw s 3
    match k with
    | 0 => let (n, s₂) := Splitmix.draw s₁ 3; (.atom n, s₂)
    | 1 => let (a, s₂) := gen d s₁; (.box a, s₂)
    | _ => let (a, s₂) := gen d s₁
           let (b, s₃) := gen d s₂
           (.disj a b, s₃)

/-- A cell: the instance plus the stratum's depth bound, so the corpus line
is readable on its own. -/
structure Cell where
  d : Nat
  f : Fml
  deriving Inhabited

/-- The `SeedGen`.  Pure in `(seed, size)`; `size` is used as extra entropy so
that the same seed at a different size is a different instance. -/
def genCell (d : Nat) : SeedGen Cell := fun seed size =>
  some { d, f := (gen d (Splitmix.mk (seed * 31 + size))).1 }

/-! ## The gate -/

def gateNormal : Gate Cell := { name := "normal-form", check := fun c => c.f.normal }

def gateTwoAtoms : Gate Cell :=
  { name := "two-atoms", check := fun c => 2 ≤ c.f.atoms.length }

def gates : List (Gate Cell) := [gateNormal, gateTwoAtoms]

/-! ## The two evaluators, and the triage that compares them -/

/-- Direct evaluation at a valuation given as a list of true atoms. -/
def evalD (v : List Nat) : Fml → Bool
  | .atom n => v.contains n
  | .disj a b => evalD v a || evalD v b
  | .box a => evalD v a

/-- Evaluation after a (deliberately slightly wrong) normalisation: `□(a ∨ b)`
is rewritten to `□a ∨ □b`, which is sound here but is exactly the kind of
step a real development gets wrong one nesting level beyond where it was
tested. -/
def push : Fml → Fml
  | .atom n => .atom n
  | .disj a b => .disj (push a) (push b)
  | .box (.disj a b) => .disj (push (.box a)) (push (.box b))
  | .box a => .box (push a)

def evalN (v : List Nat) (f : Fml) : Bool := evalD v (push f)

/-- All valuations over `{0,1,2}`. -/
def valuations : List (List Nat) :=
  [[], [0], [1], [2], [0,1], [0,2], [1,2], [0,1,2]]

/-- Countermodel-only triage: hunt for a valuation on which the two
evaluators disagree.  A `hit` records it; nothing else is claimed. -/
def triage (c : Cell) : IO Outcome := do
  match valuations.find? (fun v => evalD v c.f != evalN v c.f) with
  | some v => pure { triage := .hit, cert := s!"v={v}" }
  | none => pure { triage := .quiet }

def cols (c : Cell) : List (String × String) :=
  [("f", c.f.render), ("depth", toString c.f.depth), ("bound", toString c.d)]

/-! ## The campaign -/

def strata : List (Stratum Cell) :=
  [ { name := "depth0", gen := genCell 0, samples := 20, seed0 := 100
    , note := "atoms only" }
  , { name := "depth1", gen := genCell 1, samples := 20, seed0 := 200
    , note := "one connective" }
  , { name := "depth2", gen := genCell 2, samples := 20, seed0 := 300
    , note := "the tested region" }
  , { name := "depth3", gen := genCell 3, samples := 20, seed0 := 400
    , note := "ONE LEVEL BEYOND the tested region" } ]

def stratumByName (nm : String) : Option (Stratum Cell) :=
  strata.find? (fun s => s.name == nm)

def regen (nm : String) (seed size : Nat) : Option Cell :=
  (stratumByName nm).bind (fun s => s.gen seed size)

def demoLedger : Ledger := { path := "frontier_example_corpus.txt" }

def run : IO Unit := do
  let t ← runCampaign demoLedger "example" strata gates cols triage
  IO.println t.render

/-- Replay: the same corpus, a DIFFERENT property.  Here: does the formula
survive `push` unchanged?  A corpus gathered for one question answers the
next one with no regeneration and no search. -/
def replayIdempotent : IO Unit := do
  let r ← replay demoLedger regen (fun c _ => pure
    { triage := if push c.f == c.f then Triage.quiet else Triage.hit
    , cert := (push c.f).render })
  IO.println r.render
  for n in r.notes.take 5 do IO.println s!"  {n}"

end Example
end FrontierSampler
