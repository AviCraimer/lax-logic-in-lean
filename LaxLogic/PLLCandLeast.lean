import LaxLogic.PLLCandOr

/-!
# The least candidate — the second-order object, and initiality

Matthew's question (2026-08-08 evening): *are the candidates a strictly
second-order notion?  They'd need to be.*  Yes, and the convergence theorem is
the proof: `extremal_iff_forallp` shows a **formula-indexed** candidate family
(`Cθ`) collapses back to the propositional quantifier `∀p` — first-order
candidates re-pose the lattice question, chains and all.  The Girardian move
is candidates as arbitrary **predicates on sequents**, and the interpolant
built from the least of them.

## What is here

* `LC p` — **the least interpolation candidate**, as a Lean inductive
  predicate: the thirteen closure clauses of `Cand p` are its *constructors*.
  Its existence is free (a least fixed point), which is exactly the
  second-order advantage: no extremal formula is required for the object to
  exist.
* `LC.toCand` — `LC p` satisfies all thirteen clauses, so it IS a candidate.
* `LC.initial` — **initiality**: `LC p` is contained in every candidate.  One
  structural induction, constructor to clause.
* `LC.le_budget` — instantiating initiality at the consequence candidates:
  whenever `LC p` accepts a sequent, EVERY budget accepts it — in particular
  (via `cθ_iff_entails`) the sequent formula is derivable outright from any
  `θ` whatsoever, e.g. `⊤`.  So `LC`-membership is a *strong* property: it
  marks the sequents whose `p`-part is irrelevant.

## Where uniform interpolation now lives

Existence of the least candidate is free; what is NOT free is
**definability**: whether, for a given antecedent, the second-order object
`LC p` is the trace of a formula.  UI holds at a sequent exactly when it is.
The chains of `PLLUIChains.lean` are the instruments for refuting
definability; the phase recursion over `PLLFocused` is the instrument for
proving it.  That recursion — interpolant by recursion on focusing phases,
verified against `LC` by initiality — is the remaining constructive content
of the programme, and the next build.
-/

namespace PLLND
namespace Candidate

open Polar Focused

/-- **The least interpolation candidate**: the inductive predicate whose
constructors are the thirteen closure clauses.  A second-order object — a
least fixed point over predicates on inversion sequents — whose existence
needs no extremal formula. -/
inductive LC (p : String) : List Neg → List Pos → JD → Neg → Prop
  | impR {Γ Ω Q N} : LC p Γ (Q :: Ω) .tru N → LC p Γ Ω .tru (.imp Q N)
  | andR {Γ Ω M N} : LC p Γ Ω .tru M → LC p Γ Ω .tru N → LC p Γ Ω .tru (.and M N)
  | circR {Γ Ω j P} : LC p Γ Ω .lax (.up P) → LC p Γ Ω j (.circ P)
  | orL {Γ Ω P Q j N} :
      LC p Γ (P :: Ω) j N → LC p Γ (Q :: Ω) j N → LC p Γ (.or P Q :: Ω) j N
  | fls {Γ Ω j N} : LC p Γ (.fls :: Ω) j N
  | downL {Γ Ω M j N} : LC p (M :: Γ) Ω j N → LC p Γ (.down M :: Ω) j N
  | atomL {Γ Ω a j N} :
      LC p (.up (.atom a) :: Γ) Ω j N → LC p Γ (.atom a :: Ω) j N
  | init {Γ j a} : Neg.up (Pos.atom a) ∈ Γ → a ≠ p → LC p Γ [] j (.up (.atom a))
  | orR {Γ j P Q} : LC p Γ [] j (.up P) → LC p Γ [] j (.up (.or P Q))
  | rel {Γ j N} : LC p Γ [] j N → LC p Γ [] j (.up (.down N))
  | impL {Γ j Q N P} : Neg.imp Q N ∈ Γ → LC p Γ [] .tru (.up Q) →
      LC p (N :: Γ) [] j (.up P) → LC p Γ [] j (.up P)
  | andL {Γ j M N P} : Neg.and M N ∈ Γ → LC p (M :: Γ) [] j (.up P) →
      LC p Γ [] j (.up P)
  | andL' {Γ j M N P} : Neg.and M N ∈ Γ → LC p (N :: Γ) [] j (.up P) →
      LC p Γ [] j (.up P)
  | circL {Γ Q P} : Neg.circ Q ∈ Γ → LC p Γ [Q] .lax (.up P) →
      LC p Γ [] .lax (.up P)

namespace LC

/-- `LC p` satisfies the thirteen clauses: it is itself a candidate. -/
def toCand (p : String) : Cand p where
  C := LC p
  cl_impR := .impR
  cl_andR := .andR
  cl_circR := .circR
  cl_orL := .orL
  cl_fls := .fls
  cl_downL := .downL
  cl_atomL := .atomL
  cl_init := .init
  cl_orR := .orR
  cl_rel := .rel
  cl_impL := .impL
  cl_andL := .andL
  cl_andL' := .andL'
  cl_circL := .circL

/-- **Initiality**: the least candidate is contained in every candidate.
One structural induction; each constructor maps to its clause. -/
theorem initial {p : String} (K : Cand p) :
    ∀ {Γ Ω j N}, LC p Γ Ω j N → K.C Γ Ω j N := by
  intro Γ Ω j N h
  induction h with
  | impR _ ih => exact K.cl_impR ih
  | andR _ _ ih₁ ih₂ => exact K.cl_andR ih₁ ih₂
  | circR _ ih => exact K.cl_circR ih
  | orL _ _ ih₁ ih₂ => exact K.cl_orL ih₁ ih₂
  | fls => exact K.cl_fls
  | downL _ ih => exact K.cl_downL ih
  | atomL _ ih => exact K.cl_atomL ih
  | init hm hne => exact K.cl_init hm hne
  | orR _ ih => exact K.cl_orR ih
  | rel _ ih => exact K.cl_rel ih
  | impL hm _ _ ih₁ ih₂ => exact K.cl_impL hm ih₁ ih₂
  | andL hm _ ih => exact K.cl_andL hm ih
  | andL' hm _ ih => exact K.cl_andL' hm ih
  | circL hm _ ih => exact K.cl_circL hm ih

/-- Initiality at the consequence candidates: `LC`-membership makes the
sequent derivable from **every** budget — in particular from `⊤`.  So `LC`
marks the sequents whose `p`-content is irrelevant, which is exactly what the
interpolant recursion must compute a formula-level witness FOR. -/
theorem le_budget {p : String} {θ : PLLFormula} {Γ Ω j N}
    (h : LC p Γ Ω j N) : CandOr.Cθ θ Γ Ω j N :=
  initial (CandOr.candOf p θ) h

end LC
end Candidate
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.Candidate.LC.initial' does not depend on any axioms -/
#guard_msgs in
#print axioms PLLND.Candidate.LC.initial

/-- info: 'PLLND.Candidate.LC.le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Candidate.LC.le_budget
