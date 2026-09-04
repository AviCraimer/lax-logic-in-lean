import LaxLogic.PLLSearch
import LaxLogic.PLLAxiom

/-!
# `PLLSearch` exercised: the Hilbert axioms of PLL

For every Hilbert axiom of PLL (the four ◯-axioms and the nine IPC
axioms, instantiated at atoms p, q, r): first the ANSWERS produced by
`Search.decide`, then the DECISIONS computed from those answers, and
finally a sample kernel-checked extraction of a derivability theorem.
-/

open PLLFormula PLLND PLLND.Search

namespace PLLND.SearchEx

def pV : PLLFormula := .prop "p"
def qV : PLLFormula := .prop "q"
def rV : PLLFormula := .prop "r"

/-- The thirteen Hilbert axioms, instantiated. -/
def hilbert : List PLLAxiom :=
  [.somehowR pV, .somehowM pV, .somehowS pV qV, .somehowBind pV qV,
   .impK pV qV, .impS pV qV rV, .andElim1 pV qV, .andElim2 pV qV,
   .andIntro pV qV, .orIntro1 pV qV, .orIntro2 pV qV,
   .orElim pV qV rV, .explosion pV]

/-! ## 1. The answers -/

/-- The `Search.decide` answer for an axiom. -/
def ans (a : PLLAxiom) : Answer [] a.get := decide {} [] a.get

def isProved {Γ C} : Answer Γ C → Bool
  | .proved _ => true
  | _ => false

-- Every Hilbert axiom comes back `.proved` (checked at compile time).
#guard hilbert.all fun a => isProved (ans a)

/-! ## 2. The decisions, computed from the answers -/

/-- The certified decision extracted from the answer. -/
def dec (a : PLLAxiom) : Decision [] a.get := (ans a).toDecision

def isDerivable {Γ C} : Decision Γ C → Bool
  | .derivable _ => true
  | _ => false

-- Every decision is `.derivable` — i.e. carries the theorem
-- `Nonempty (LaxND [] axiom)` extracted from the proof term.
#guard hilbert.all fun a => isDerivable (dec a)
#eval hilbert.all fun a => isDerivable (dec a)

/-! ## 3. Extraction

Holding an answer, ONE lemma converts a `.proved` verdict into the
derivability theorem: -/

theorem derivable_of_isProved {Γ : List PLLFormula} {C : PLLFormula} :
    ∀ a : Answer Γ C, isProved a = true → Nonempty (LaxND Γ C)
  | .proved t, _ => proved_sound t

/-! A limitation worth knowing: the search functions are defined by
well-founded recursion, so a closed `decide {} Γ C` does NOT reduce in
the kernel — `by decide`/`rfl` cannot evaluate it inside a proof term.
Compile-time verification therefore runs through `#guard` (the
evaluator), as above; certificate EXTRACTION happens by matching on a
computed answer (`match ans a with | .proved t => proved_sound t …`)
wherever the answer is a runtime value, or by pretty-printing the found
`G4cTm` term and transcribing it. -/

end PLLND.SearchEx
