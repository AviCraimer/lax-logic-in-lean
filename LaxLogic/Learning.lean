import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import LaxLogic.PLLFormula
import LaxLogic.PLLAxiom

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


open Lean Meta Elab Tactic
open PLLFormula

section Tactics

elab "finset_ext" : tactic => do
  try
    evalTactic (← `(tactic| ext x : 1; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; itauto))
  catch _ =>
    throwError "finset_ext tactic failed: goal is not a Finset equality or tactic did not succeed."
elab "finset_ext_old" : tactic => do
  evalTactic (← `(tactic| ext x : 1; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; itauto))

/- the following tactic is a long way from being effective; written between CoPilot and me:
  neither of us know what we are doing but it was fun...
-/

partial def collectFinset (e : Lean.Expr) : MetaM (Array Expr × Array Expr) := do
  if e.isAppOfArity `Union.union 2 then
    let args := e.getAppArgs
    let a := args[0]!
    let b := args[1]!
    let (varsA, elemsA) ← collectFinset a
    let (varsB, elemsB) ← collectFinset b
    pure (varsA ++ varsB, elemsA ++ elemsB)
  else if e.isAppOfArity `Singleton.singleton 1 then
    pure (#[], #[e.getArg! 0])
  else
    pure (#[(← instantiateMVars e)], #[])

/--
  `norm_finset [g]` normalizes the goal (or hypothesis) so that the Finset expression is
  written as a union of variables and a single set of all singleton elements, with `{g}` last.
  If `[g]` is omitted, just flattens and sorts the singletons.
-/
elab "norm_finset" g:(ppSpace colGt term)? : tactic => do
let gOpt ← match g with
  | some stx => do
      let e ← elabTerm stx none
      pure (some e)
  | none => pure none
  let goal ← getMainGoal
  let tgt ← goal.getType
  -- Only handle goals of the form `A = B` where A, B are Finsets
  let (fn, args) := tgt.getAppFnArgs
  if fn != ``Eq then throwError "norm_finset: goal is not an equality"
  let lhs := args[0]!
  let rhs := args[1]!
    -- use lhs and rhs

  let (vars, elems) ← collectFinset lhs
  -- Optionally, bring out g as the last element
  let elems :=
    match gOpt with
    | some g =>
      let idx := elems.findIdx? (· == g)
      match idx with
      | some i => (elems.eraseIdx! i).push g
      | none => elems
    | none => elems
  -- Rebuild the normalized lhs
  let lhsNorm :=
    vars.foldl (fun acc v => mkApp2 (mkConst `Union.union) acc v) (mkApp (mkConst `Finset.empty) (← inferType lhs))
  let singletons := elems.foldl (fun acc e => mkApp2 (mkConst `Insert.insert) e acc) (mkApp (mkConst `Finset.empty) (← inferType lhs))
  let newLhs := mkApp2 (mkConst `Union.union) lhsNorm singletons
  -- Replace lhs in the goal
  let eqProof ← mkEqRefl rhs
  liftMetaTactic fun goal => do
    let newGoal ← goal.change (← mkEq newLhs rhs)
    pure [newGoal]
  -- evalTactic (← `(tactic| finset_ext))

end Tactics

open PLLFormula

-- Use Finset as the Cxt
def Cxt := Finset PLLFormula
open Finset

-- Ensure all the right typeclass instances for Cxt
instance : Membership PLLFormula Cxt := inferInstanceAs (Membership PLLFormula (Finset PLLFormula))
instance : Insert PLLFormula Cxt := inferInstanceAs (Insert PLLFormula (Finset PLLFormula))
instance : Union Cxt := inferInstanceAs (Union (Finset PLLFormula))
instance : Singleton PLLFormula Cxt := inferInstanceAs (Singleton PLLFormula (Finset PLLFormula))
instance : EmptyCollection Cxt := inferInstanceAs (EmptyCollection (Finset PLLFormula))

#check {a b : Cxt} →  (a ∪ b) = b ∪ a

/- #check HUnion.hUnion ({} : Finset ℕ) ({} : Finset ℕ)
#check Finset.insert
#check Finset.union
#check Finset.singleton
 -/
#check Union.union ({} : Finset ℕ) ({} : Finset ℕ)
#check Insert.insert (1 : ℕ) ({} : Finset ℕ)
#check Singleton.singleton (1 : ℕ)

#check Finset.empty
#check Finset.add
#check Finset.min
#check Finset.attach
#check Finset.Nonempty
#check Finset.disjiUnion
#check Finset.pi
#check Finset.univ
#check Finset.biUnion

-- Minimal Lax Logic ND system with Finset Cxt
inductive LaxMin : Cxt → PLLFormula → Type
  | iden (Γ : Cxt) (φ : PLLFormula) : LaxMin (Γ ∪ {φ}) φ
  | falsoElim {Γ : Cxt} (φ : PLLFormula) (p : LaxMin Γ falsePLL) : LaxMin Γ φ
  | impIntro {Γ : Cxt} {φ ψ : PLLFormula} (p : LaxMin (Γ ∪ {φ}) ψ) : LaxMin Γ (ifThen φ ψ)
  | impElim {Γ : Cxt} {φ ψ : PLLFormula} (p1 : LaxMin Γ (ifThen φ ψ)) (p2 : LaxMin Γ φ) : LaxMin Γ ψ
  | laxIntro {Γ : Cxt} {φ : PLLFormula} (p : LaxMin Γ φ) : LaxMin Γ (somehow φ)
  | laxElim {Γ : Cxt} {ψ : PLLFormula} (φ : PLLFormula) -- note the order of arguments!
      (p1 : LaxMin Γ (somehow φ)) (p2 : LaxMin (Γ ∪ {φ}) (somehow ψ)) : LaxMin Γ (somehow ψ)

open LaxMin
-- filepath: /Users/matthew/Lean/Sources/lax-logic-in-lean/LaxLogic/Learning.lean
def isIPLFormula : PLLFormula → Prop
  | PLLFormula.prop _  => true
  | falsePLL    => true
  | ifThen φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.and φ ψ => isIPLFormula φ ∧ isIPLFormula ψ
  | PLLFormula.or φ ψ  => isIPLFormula φ ∧ isIPLFormula ψ
  | somehow _   => false
@[simp]

def isIPLProof : {Γ : Cxt} → {φ : PLLFormula} → (prf : LaxMin Γ φ) → Prop
  | _, _, iden Γ φ         => isIPLFormula φ
  | _, _, falsoElim _ prf  => isIPLProof prf
  | _, _, impIntro prf     => isIPLProof prf
  | _, _, impElim prf1 prf2 => isIPLProof prf1 ∧ isIPLProof prf2
  | _, _, laxIntro _       => False
  | _, _, laxElim _ _  _   => False

section Casting

-- 0) good this checks; can we use it?
def congrArg2 {α β γ : Sort*} (f : α → β → γ) {a₁ a₂ : α} {b₁ b₂ : β}
  (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ :=
by cases ha; cases hb; rfl

-- 1) checks but is useless
lemma cast_congrArg_Cxt_id
  {Γ₁ Γ₂ : Cxt} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxMin Γ₁ φ) :
  cast (congrArg (fun Γ => LaxMin Γ φ) h) x = (cast (congrArg (fun Γ => LaxMin Γ φ) h) x : LaxMin Γ₂ φ) :=
rfl

/- -- 1) nope
lemma cast_congrArg_Cxt_inv
  {Γ₁ Γ₂ : Cxt} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxND Γ₁ φ) :
  cast (congrArg (fun Γ => LaxND Γ φ) h) x = (cast h x : LaxND Γ₂ φ) :=
by cases h; rfl

-- 2) nope
lemma cast_congrArg_formula_inv
  {Γ : Cxt} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxND Γ φ₁) :
  cast (congrArg (fun φ => LaxND Γ φ) h) x = (cast h x : LaxND Γ φ₂) :=
by cases h; rfl
 -/

-- 3) good this works
lemma cast_congrArg_Cxt_cancel
  {Γ₁ Γ₂ : Cxt} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxMin Γ₁ φ) :
  cast (congrArg (fun Γ => LaxMin Γ φ) (h.symm)) (cast (congrArg (fun Γ => LaxMin Γ φ) h) x) = x :=
by cases h; rfl

-- 4) fixed
lemma cast_congrArg_formula_cancel
  {Γ : Cxt} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxMin Γ φ₁) :
  cast (congrArg (fun φ => LaxMin Γ φ) h.symm) (cast (congrArg (fun φ => LaxMin Γ φ) h) x) = x :=
by cases h; rfl

-- 6) good this works
lemma cast_congrArg2_cancel_left
  {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂)
  (x : LaxMin Γ₁ φ₁) :
  cast (congrArg2 LaxMin hΓ.symm hφ.symm) (cast (congrArg2 LaxMin hΓ hφ) x) = x :=
by cases hΓ; cases hφ; rfl
-- and conversely:
lemma cast_congrArg2_cancel_right
  {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxMin Γ₂ φ₂) :
  cast (congrArg2 LaxMin hΓ hφ) (cast (congrArg2 LaxMin hΓ.symm hφ.symm) x) = x :=
by cases hΓ; cases hφ; rfl

-- 5a) good this works
lemma isIPLProof_cast_eq {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula}
  {prf : LaxMin Γ₁ φ₁} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) :
  isIPLProof (cast (congrArg2 LaxMin hΓ hφ) prf) = isIPLProof prf :=
by cases hΓ; cases hφ; rfl


-- Some basic cast helpers for working with Cxt and formula equalities
def cast_ctx {Γ₁ Γ₂ : Cxt} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxMin Γ₁ φ) : LaxMin Γ₂ φ :=
  cast (congrArg (fun Γ => LaxMin Γ φ) h) x

def cast_formula {Γ : Cxt} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxMin Γ φ₁) : LaxMin Γ φ₂ :=
  cast (congrArg (fun φ => LaxMin Γ φ) h) x

def cast_both {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula} (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxMin Γ₁ φ₁) : LaxMin Γ₂ φ₂ :=
  cast (congrArg2 LaxMin hΓ hφ) x

@[simp]
lemma cast_ctx_cancel {Γ₁ Γ₂ : Cxt} {φ : PLLFormula} (h : Γ₁ = Γ₂) (x : LaxMin Γ₁ φ) :
  cast_ctx h.symm (cast_ctx h x) = x :=
by cases h; rfl

@[simp]
lemma cast_formula_cancel {Γ : Cxt} {φ₁ φ₂ : PLLFormula} (h : φ₁ = φ₂) (x : LaxMin Γ φ₁) :
  cast_formula h.symm (cast_formula h x) = x :=
by cases h; rfl

@[simp]
lemma cast_both_cancel_left {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxMin Γ₁ φ₁) :
  cast_both hΓ.symm hφ.symm (cast_both hΓ hφ x) = x :=
by cases hΓ; cases hφ; rfl

@[simp]
lemma cast_both_cancel_right {Γ₁ Γ₂ : Cxt} {φ₁ φ₂ : PLLFormula}
  (hΓ : Γ₁ = Γ₂) (hφ : φ₁ = φ₂) (x : LaxMin Γ₂ φ₂) :
  cast_both hΓ hφ (cast_both hΓ.symm hφ.symm x) = x :=
by cases hΓ; cases hφ; rfl

end Casting

section FinsetLemmas

lemma merge_singletons (Γ : Cxt) (a b : PLLFormula) : (Γ ∪ {a} ∪ {b} : Finset PLLFormula) = Γ ∪ {a, b} := by
  aesop
--  norm_finset
--  finset_ext

example (a b c : PLLFormula) : ({a} ∪ {b} ∪ {c} : Finset PLLFormula) = {c, b, a} := by
  finset_ext

-- simp [union_insert, insert_eq, union_assoc, union_comm, Finset.union_assoc]
lemma drop_empty (Γ : Cxt) : ({} : Cxt) ∪ Γ = Γ := by
  rw [union_comm, union_empty]

lemma move_singletons (Γ : Finset PLLFormula) (φ ψ : PLLFormula) :
  Γ ∪ {φ} ∪ {ψ} = Γ ∪ {ψ} ∪ {φ} := by
  apply union_right_comm
lemma shift_singletons (Γ : Finset PLLFormula) (φ : PLLFormula) :
  Γ ∪ {φ} = {φ} ∪ Γ := by
  apply union_comm

--@[simp] -- breaks results below
lemma union_singleton_assoc (Γ : Cxt) (φ ψ : PLLFormula) :
  (Γ ∪ {φ}) ∪ {ψ} = Γ ∪ {φ, ψ} :=by
  trans Γ ∪ ({φ} ∪ {ψ})
  · exact union_assoc _ _ _
  · aesop -- rw[merge_singletons]

#print union_singleton_assoc

example (a b c : PLLFormula) : ({a} ∪ {b} ∪ {c} : Finset PLLFormula) = {c, b, a} := by
  finset_ext

end FinsetLemmas

-- Example: a minimal proof
def Oimp (φ ψ : PLLFormula) : LaxMin ∅ (ifThen (somehow (ifThen φ ψ)) (ifThen (somehow φ) (somehow ψ))) := by
  apply impIntro
  apply impIntro
  apply laxElim
  apply iden --∅ (ifThen φ ψ)
  apply laxElim (φ.ifThen ψ)
  simp[drop_empty]
  -- change of proof from previous version
  simp[union_comm {(φ.ifThen ψ).somehow}]
  simp[move_singletons {φ.somehow} (φ.ifThen ψ).somehow φ, ←union_assoc]
  apply iden
  apply laxIntro
  apply @impElim _ φ ψ
  simp[drop_empty]
  apply iden
  simp[drop_empty]
  simp[move_singletons ({(φ.ifThen ψ).somehow} ∪ {φ.somehow}) φ, ←union_assoc]
  apply iden

-- Example: induction principle
def LaxMin_rec_on {Γ : Cxt} {φ : PLLFormula} (p : LaxMin Γ φ)
  (H_iden : ∀ Γ φ, (LaxMin (Γ ∪ {φ}) φ) → Prop)
  (H_falsoElim : ∀ Γ (p : LaxMin Γ falsePLL), Prop)
  (H_impIntro : ∀ Γ φ ψ (p : LaxMin (Γ ∪ {φ}) ψ), Prop)
  (H_impElim : ∀ Γ φ ψ (p1 : LaxMin Γ (ifThen φ ψ)) (p2 : LaxMin Γ φ), Prop)
  (H_laxIntro : ∀ Γ φ (p : LaxMin Γ φ), Prop)
  (H_laxElim : ∀ Γ φ ψ (p1 : LaxMin Γ (somehow φ)) (p2 : LaxMin (Γ ∪ {φ}) (somehow ψ)), Prop)
  : Prop :=
  match p with
  | iden Γ φ => H_iden Γ φ (iden Γ φ)
  | falsoElim φ pf => H_falsoElim Γ pf
  | @impIntro Γ φ ψ pf => H_impIntro Γ φ ψ pf
  | @impElim Γ φ ψ pf1 pf2 => H_impElim Γ φ ψ pf1 pf2
  | @laxIntro Γ φ pf => H_laxIntro Γ φ pf
  | @laxElim Γ ψ φ pf1 pf2 => H_laxElim Γ φ ψ pf1 pf2

-- You can now experiment with this file, try induction, and see how casts behave.


def OimpC (Γ : Cxt)(φ ψ : PLLFormula) : LaxMin Γ (ifThen (somehow (ifThen φ ψ)) (ifThen (somehow φ) (somehow ψ))) := by
  apply impIntro
  apply impIntro
  apply laxElim
  apply iden --∅ (ifThen φ ψ)
  apply laxElim (φ.ifThen ψ)
  -- simp[drop_empty]
  -- change of proof from previous version
  simp[union_comm (Γ ∪ {(φ.ifThen ψ).somehow})]
  simp[move_singletons {φ.somehow} (φ.ifThen ψ).somehow φ, ←union_assoc]
  apply iden
  apply laxIntro
  apply @impElim _ φ ψ
  simp[drop_empty]
  apply iden
  simp[drop_empty]
  simp[move_singletons ({(φ.ifThen ψ).somehow} ∪ {φ.somehow}) φ, ←union_assoc]
  apply iden

#check {φ ψ : PLLFormula} -> LaxMin {φ.somehow, (φ.ifThen ψ).somehow, φ, φ, φ.ifThen ψ} φ
