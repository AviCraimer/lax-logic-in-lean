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

inductive LaxMin: (List PLLFormula)→ PLLFormula → Type -- ND for Minimal Lax logic, proof terms
  | iden : (Γ Δ : List PLLFormula) → (φ : PLLFormula) → LaxMin (Γ ++ φ :: Δ) φ
  | falsoElim : {Γ : List PLLFormula} → (φ : PLLFormula) → LaxMin Γ falsePLL → LaxMin Γ φ
  | impIntro : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxMin (Γ ++ φ :: Δ) ψ → LaxMin (Γ ++ Δ) (ifThen φ ψ)
  | impElim : {Γ : List PLLFormula} → {φ ψ : PLLFormula} → LaxMin Γ (ifThen φ ψ) →
      LaxMin Γ φ → LaxMin Γ ψ
  | laxIntro : {Γ : List PLLFormula} → {φ : PLLFormula} → LaxMin Γ φ → LaxMin Γ (somehow φ)
  | laxElim : {Γ Δ : List PLLFormula} → {φ ψ : PLLFormula} →
      LaxMin (Γ ++ Δ) (somehow φ) → LaxMin (Γ ++ φ :: Δ) (somehow ψ) → LaxMin (Γ ++ Δ) (somehow ψ)

open LaxMin

def Oimp (φ ψ : PLLFormula) : LaxMin [] (ifThen (somehow (φ.ifThen ψ)) ((somehow φ).ifThen (somehow ψ))) := by
  apply @impIntro []; simp
  apply @impIntro []; simp
  apply @laxElim [φ.somehow, (φ.ifThen ψ).somehow] [] φ ψ; simp
  apply iden [] [(φ.ifThen ψ).somehow] φ.somehow; simp
  apply @laxElim [φ.somehow, (φ.ifThen ψ).somehow, φ] [] φ ; simp
  apply iden [] [(φ.ifThen ψ).somehow, φ] φ.somehow; simp
  apply @laxElim [φ.somehow, (φ.ifThen ψ).somehow, φ, φ] [] (φ.ifThen ψ); simp
  apply iden [φ.somehow] [φ, φ]; simp
  apply laxIntro
  apply @impElim [φ.somehow, (φ.ifThen ψ).somehow, φ, φ, φ.ifThen ψ] φ ψ
  apply iden [φ.somehow, (φ.ifThen ψ).somehow, φ, φ] [] (φ.ifThen ψ)
  apply iden [φ.somehow, (φ.ifThen ψ).somehow, φ] [φ.ifThen ψ] φ

#check {φ ψ : PLLFormula} -> LaxMin [φ.somehow, (φ.ifThen ψ).somehow, φ, φ, φ.ifThen ψ] φ
