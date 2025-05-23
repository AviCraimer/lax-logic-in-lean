import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

open PLLFormula

/-
-- # Minimal Lax Logic Proof Theory Exploration

This file is dedicated to exploring how to formalize proof theory in Lean 4 using inductive types.
The main focus is on representing proofs as inductive predicates and investigating how to perform
induction on such proofs, which is a common technique in proof theory for establishing results like
cut-elimination and conservativity of proof translations.

In traditional proof theory, many meta-theorems are proved by induction on the structure of proofs.
However, in Lean 4, working with induction principles or recursors for inductively defined proof
predicates can be challenging. This file provides a minimal example, based on minimal lax logic,
to illustrate these challenges and to serve as a basis for discussion with the Lean community
(e.g., on the Lean Zulip chat).

The example here is inspired by, and aims to be a minimal extraction from, the more extensive
`PLLNDexperiment.lean` file. The goal is to keep the logic as simple as possible while still
capturing the essential difficulties encountered when reasoning inductively about proofs in Lean 4.

Feel free to use this file as a reference or starting point for further questions and explorations
regarding proof-theoretic formalization in Lean 4.
-/


#eval falsePLL
