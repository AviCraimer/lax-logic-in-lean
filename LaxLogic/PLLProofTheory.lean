-- Meta-theorems about Lax Logic Proofs
import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom
import LaxLogic.PLLProof
import Mathlib.Tactic

namespace PLLProof

def proofToConditional (proof: PLLProof ): PLLProof :=
match proof with
| emptyProof =>

theorem deduction (proof: PLLProof)(h1: proof.isValid)(h2: ¬proof.isEmpty ∧ ¬ proof.undoStep.isEmpty): conclusion ⟨ proof, h2.1⟩    := by
