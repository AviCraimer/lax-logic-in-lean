import LaxLogic.PLLTopTop
import LaxLogic.PLLG4Term

/-!
# Running the mechanisation: the normaliser as a program, and a
derivability tactic

Lean has no separate extraction step: every `def` *is* the program, and
`#eval` runs it through the compiler.  The `Prop`/`Type` boundary plays
the role of Coq's extraction erasure — propositions (such as the
strong-normalisation certificate driving `Tm.normalize`'s
`termination_by`) vanish at runtime, so the compiled normaliser is
literally "iterate `Tm.step?` until `none`", with
`Tm.normalize_spec : Steps t t.normalize ∧ Nf t.normalize` as its
mechanised warranty.  This file adds the missing I/O — a compact
pretty-printer — plus build-time demos, and packages backward proof
search in the repaired calculus G4iLL″ as a derivability tactic
`pll_g4c` for concrete PLL claims.

`pll_g4c` replaces the retired `pll_g4`, which ran the *naive* Iemhoff
calculus `G4` — proved incomplete for PLL in `PLLG4Gap.lean` — under
`native_decide`: its failures proved nothing, and its successes trusted
the compiled evaluator (a per-use `native_decide` axiom, the
`Lean.ofReduceBool` family).  The new tactic is complete and adds no
such axiom, by *certificate splicing*: at elaboration time it runs the
fuel-free searcher `G4cTm.find` (`PLLG4Term.lean`) as untrusted code,
then re-elaborates the found derivation as an explicit `G4cTm` proof
term, which the kernel checks and the mechanised equivalences
(`G4cTm.toTm`, `G4c.equiv_sc`, `G4c.equiv_nd`) transport to the goal.
Trust therefore reduces to the transport lemmas — clean-classical
(`propext`, `Classical.choice`, `Quot.sound`) for `Tm`/`LaxND`/`SC`
goals, *no axioms at all* for a bare `G4cTm` certificate — and by
completeness of G4iLL″ (`G4c.equiv_tm`) a search failure refutes
derivability instead of proving nothing.
-/

open PLLFormula

namespace PLLND

/-! ### Displaying proof terms -/

/-- de Bruijn index of a variable. -/
def Var.idx : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Var Γ φ → Nat
  | _, _, .here => 0
  | _, _, .there v => v.idx + 1

/-- Compact λ-syntax for proof terms: de Bruijn variables `#n`,
`val`/`let val` for the `◯`-monad. -/
def Tm.pretty : ∀ {Γ : List PLLFormula} {φ : PLLFormula}, Tm Γ φ → String
  | _, _, .var v => s!"#{v.idx}"
  | _, _, .abort _ t => s!"abort {t.pretty}"
  | _, _, .lam b => s!"(λ. {b.pretty})"
  | _, _, .app f a => s!"({f.pretty} {a.pretty})"
  | _, _, .pair a b => s!"⟨{a.pretty}, {b.pretty}⟩"
  | _, _, .fst t => s!"{t.pretty}.1"
  | _, _, .snd t => s!"{t.pretty}.2"
  | _, _, .inl t => s!"(inl {t.pretty})"
  | _, _, .inr t => s!"(inr {t.pretty})"
  | _, _, .case t u v => s!"(case {t.pretty} of {u.pretty} | {v.pretty})"
  | _, _, .val t => s!"val {t.pretty}"
  | _, _, .bind t u => s!"(let val• := {t.pretty} in {u.pretty})"

/-! ### The normaliser, running

Build-time demos: `Tm.normalize` executed by `#eval`, verdicts pinned
by `#guard_msgs`. -/

private def A₀ : PLLFormula := prop "A"

-- β: (λ. #0) #0 ⟶ #0
/-- info: "#0" -/
#guard_msgs in
#eval (Tm.app (.lam (.var .here)) (.var .here) : Tm [A₀] A₀).normalize.pretty

-- ◯-monad β: let val• := val #0 in val #0 ⟶ val #0
/-- info: "val #0" -/
#guard_msgs in
#eval (Tm.bind (.val (.var .here)) (.val (.var .here))
  : Tm [A₀] A₀.somehow).normalize.pretty

-- let-assoc then β: let val• := (let val• := val #0 in val #0) in val #0
/-- info: "val #0" -/
#guard_msgs in
#eval (Tm.bind (.bind (.val (.var .here)) (.val (.var .here)))
    (.val (.var .here)) : Tm [A₀] A₀.somehow).normalize.pretty

-- a *neutral* bind is already normal: let val• := #0 in val #0
/-- info: "(let val• := #0 in val #0)" -/
#guard_msgs in
#eval (Tm.bind (.var .here) (.val (.var .here))
  : Tm [A₀.somehow] A₀.somehow).normalize.pretty

/-! ### A derivability tactic, by certificate splicing

The searcher runs at elaboration time, but the tactic does not trust
it: the goal is closed by the derivation it emits, re-elaborated and
kernel-checked.  `memSyntax`/`certSyntax` quote a runtime `G4cTm` value
back into surface syntax — membership side conditions become explicit
`List.Mem` constructor chains, so the kernel checks them by unfolding
alone, with no decision procedure and no axioms — and `pll_g4c`
dispatches on the goal form and transports the certificate along the
mechanised equivalences. -/

section CertificateSplicing

open Lean Elab Tactic Meta

/-- Quote a list-membership fact as a `List.Mem` constructor chain,
the position read off the (runtime) context. -/
private def memSyntax (A : PLLFormula) : List PLLFormula → TacticM Term
  | [] => throwError "pll_g4c: internal error — the certificate cites a \
      formula that is not in the context"
  | B :: Γ =>
    if A = B then `(List.Mem.head _)
    else do `(List.Mem.tail _ $(← memSyntax A Γ))

/-- Quote a `G4cTm` certificate back into surface syntax.  The quoted
membership proofs pin the principal formulas of the left rules, so
every implicit argument is determined by unification against the
goal. -/
private def certSyntax : {Γ : List PLLFormula} → {C : PLLFormula} →
    G4cTm Γ C → TacticM Term
  | Γ, _, @G4cTm.init _ a _ => do
      `(G4cTm.init $(← memSyntax (.prop a) Γ))
  | Γ, _, .botL _ => do
      `(G4cTm.botL $(← memSyntax .falsePLL Γ))
  | _, _, .andR a b => do
      `(G4cTm.andR $(← certSyntax a) $(← certSyntax b))
  | _, _, .orR1 a => do `(G4cTm.orR1 $(← certSyntax a))
  | _, _, .orR2 a => do `(G4cTm.orR2 $(← certSyntax a))
  | _, _, .impR a => do `(G4cTm.impR $(← certSyntax a))
  | _, _, .laxR a => do `(G4cTm.laxR $(← certSyntax a))
  | Γ, _, @G4cTm.laxL _ A _ _ a => do
      `(G4cTm.laxL $(← memSyntax (.somehow A) Γ) $(← certSyntax a))
  | Γ, _, @G4cTm.andL _ A B _ _ a => do
      `(G4cTm.andL $(← memSyntax (.and A B) Γ) $(← certSyntax a))
  | Γ, _, @G4cTm.orL _ A B _ _ a b => do
      `(G4cTm.orL $(← memSyntax (.or A B) Γ)
        $(← certSyntax a) $(← certSyntax b))
  | Γ, _, @G4cTm.impLProp _ a B _ _ _ t => do
      `(G4cTm.impLProp $(← memSyntax (.ifThen (.prop a) B) Γ)
        $(← memSyntax (.prop a) Γ) $(← certSyntax t))
  | Γ, _, @G4cTm.impLAnd _ A B D _ _ t => do
      `(G4cTm.impLAnd $(← memSyntax (.ifThen (.and A B) D) Γ)
        $(← certSyntax t))
  | Γ, _, @G4cTm.impLOr _ A B D _ _ t => do
      `(G4cTm.impLOr $(← memSyntax (.ifThen (.or A B) D) Γ)
        $(← certSyntax t))
  | Γ, _, @G4cTm.impLImp _ A B D _ _ t₁ t₂ => do
      `(G4cTm.impLImp $(← memSyntax (.ifThen (.ifThen A B) D) Γ)
        $(← certSyntax t₁) $(← certSyntax t₂))
  | Γ, _, @G4cTm.impLLax _ A B _ _ t₁ t₂ => do
      `(G4cTm.impLLax $(← memSyntax (.ifThen (.somehow A) B) Γ)
        $(← certSyntax t₁) $(← certSyntax t₂))
  | Γ, _, @G4cTm.impLLaxLax _ A B X _ _ _ t₁ t₂ => do
      `(G4cTm.impLLaxLax $(← memSyntax (.ifThen (.somehow A) B) Γ)
        $(← memSyntax (.somehow X) Γ)
        $(← certSyntax t₁) $(← certSyntax t₂))

/-- Read a concrete `PLLFormula` off the goal (definitions are
unfolded). -/
private partial def reifyFormula (e : Expr) : MetaM PLLFormula := do
  let e ← whnf e
  if e.isAppOfArity ``PLLFormula.prop 1 then
    let s ← whnf e.appArg!
    match s with
    | .lit (.strVal a) => return .prop a
    | _ => throwError "pll_g4c: cannot read off the atom name{indentExpr s}"
  else if e.isConstOf ``PLLFormula.falsePLL then
    return .falsePLL
  else if e.isAppOfArity ``PLLFormula.and 2 then
    return .and (← reifyFormula (e.appFn!.appArg!)) (← reifyFormula e.appArg!)
  else if e.isAppOfArity ``PLLFormula.or 2 then
    return .or (← reifyFormula (e.appFn!.appArg!)) (← reifyFormula e.appArg!)
  else if e.isAppOfArity ``PLLFormula.ifThen 2 then
    return .ifThen (← reifyFormula (e.appFn!.appArg!))
      (← reifyFormula e.appArg!)
  else if e.isAppOfArity ``PLLFormula.somehow 1 then
    return .somehow (← reifyFormula e.appArg!)
  else
    throwError "pll_g4c: the sequent must be concrete; cannot read off \
      the formula{indentExpr e}"

/-- Read a concrete context off the goal. -/
private partial def reifyContext (e : Expr) : MetaM (List PLLFormula) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    return []
  else if e.isAppOfArity ``List.cons 3 then
    return (← reifyFormula (e.appFn!.appArg!)) :: (← reifyContext e.appArg!)
  else
    throwError "pll_g4c: the sequent must be concrete; cannot read off \
      the context{indentExpr e}"

/-- `pll_g4c` — automation for concrete PLL derivability claims:
backward proof search in the complete repaired calculus G4iLL″
(`G4cTm.find`), the found derivation spliced in as a kernel-checked
`G4cTm` certificate and transported along the mechanised equivalences.
Closes goals of the forms

* `Nonempty (Tm Γ C)`
* `Nonempty (LaxND Γ C)`
* `SC Γ C`
* `G4c Γ C`
* `G4cTm Γ C` and `Nonempty (G4cTm Γ C)`

for concrete `Γ` and `C`.  **Sound and complete** (`G4c.equiv_tm`),
unlike the retired `pll_g4` (naive `G4`, incomplete: `PLLG4Gap`).  A
positive verdict adds no compiled-evaluator axiom — the trust base is
exactly that of the transport lemmas (clean-classical; empty for a
bare `G4cTm` goal) — and failure refutes derivability. -/
elab "pll_g4c" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let ty := (← instantiateMVars (← g.getType)).consumeMData
    let close (wrap : Term → TacticM Term) (ΓE CE : Expr) : TacticM Unit := do
      let Γ ← reifyContext ΓE
      let C ← reifyFormula CE
      match G4cTm.find Γ C with
      | some t => do
          let prf ← wrap (← certSyntax t)
          evalTactic (← `(tactic| exact $prf))
      | none =>
          throwError "pll_g4c: backward proof search in G4iLL″ found no \
            derivation; the calculus is complete (`G4c.equiv_tm`), so the \
            sequent is not PLL-derivable:{indentExpr ty}"
    if ty.isAppOfArity ``Nonempty 1 then
      let α := ty.appArg!.consumeMData
      if α.isAppOfArity ``Tm 2 then
        close (fun c => `(G4cTm.toTm $c)) (α.appFn!.appArg!) α.appArg!
      else if α.isAppOfArity ``LaxND 2 then
        close (fun c => `(G4c.equiv_nd.mp (G4cTm.toG4c $c)))
          (α.appFn!.appArg!) α.appArg!
      else if α.isAppOfArity ``G4cTm 2 then
        close (fun c => `(Nonempty.intro $c)) (α.appFn!.appArg!) α.appArg!
      else
        throwError "pll_g4c: unsupported goal form{indentExpr ty}"
    else if ty.isAppOfArity ``SC 2 then
      close (fun c => `(G4c.equiv_sc.mp (G4cTm.toG4c $c)))
        (ty.appFn!.appArg!) ty.appArg!
    else if ty.isAppOfArity ``G4c 2 then
      close (fun c => `(G4cTm.toG4c $c)) (ty.appFn!.appArg!) ty.appArg!
    else if ty.isAppOfArity ``G4cTm 2 then
      close pure (ty.appFn!.appArg!) ty.appArg!
    else
      throwError "pll_g4c: the goal must be a PLL derivability claim — \
        one of `Nonempty (Tm Γ C)`, `Nonempty (LaxND Γ C)`, `SC Γ C`, \
        `G4c Γ C`, `G4cTm Γ C`, `Nonempty (G4cTm Γ C)` —{indentExpr ty}"

end CertificateSplicing

/-! ### The tactic, running

The demos of the retired `pll_g4`, re-proved under the complete
calculus, plus the sequent that separates the calculi. -/

-- ◯-unit, as a natural-deduction claim
example : Nonempty (LaxND [] (A₀.ifThen A₀.somehow)) := by pll_g4c

-- ◯-multiplication, at the proof-term level
example : Nonempty (Tm [] (A₀.somehow.somehow.ifThen A₀.somehow)) := by
  pll_g4c

-- Howe's duplication sequent, in the cut-free sequent calculus
example : SC [((prop "B").ifThen ((prop "A").somehow.ifThen (prop "C"))).ifThen
      (prop "A").somehow,
    (prop "A").somehow.ifThen (prop "C"), (prop "B").somehow] (prop "C") := by
  pll_g4c

-- and a raw G4iLL″ goal
example : G4c [] (A₀.somehow.somehow.ifThen A₀.somehow) := by pll_g4c

/-! ### The gap sequent, closed

`◯((◯p → r) → ◯p), ◯p → r ⊢ r` is PLL-derivable but underivable in the
naive calculus (`PLLG4Gap.sc_but_not_G4`) — the sequent on which the
retired tactic could only fail.  The complete tactic closes it. -/

/-- `F = ◯p → r`, the minor premiss of the gap sequent. -/
private def Fgap : PLLFormula := (prop "p").somehow.ifThen (prop "r")

/-- `G = (◯p → r) → ◯p`; the gap sequent is `◯G, F ⊢ r`. -/
private def Ggap : PLLFormula := Fgap.ifThen (prop "p").somehow

example : SC [Ggap.somehow, Fgap] (prop "r") := by pll_g4c

/-- The gap-sequent derivation, spliced in as a bare G4iLL″ proof
term (for the axiom audit below). -/
def gap_certificate : G4cTm [Ggap.somehow, Fgap] (prop "r") := by pll_g4c

-- the same certificate, displayed as its rule tree
/-- info: some "(→L◯◯ (→L→ (→R (→L◯◯ (◯R init) init)) (◯L (◯R init))) init)" -/
#guard_msgs in
#eval (G4cTm.find [Ggap.somehow, Fgap] (prop "r")).map (·.pretty)

/-! ### The trust base, pinned honestly

The searcher ran as untrusted elaboration-time code, so no
compiled-evaluator axiom appears: a `pll_g4c` proof depends on exactly
the axioms of the transport lemmas (contrast the retired `pll_g4`,
whose every use added a per-declaration `native_decide` axiom).  A
bare `G4cTm` certificate is checked by the kernel outright and depends
on no axioms at all. -/

/-- A named specimen of a `pll_g4c`-produced natural-deduction proof,
for the axiom audit. -/
theorem unit_nd : Nonempty (LaxND [] (A₀.ifThen A₀.somehow)) := by pll_g4c

/-- info: 'PLLND.unit_nd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms unit_nd

/-- info: 'PLLND.gap_certificate' does not depend on any axioms -/
#guard_msgs in
#print axioms gap_certificate

/-! Completeness makes failure informative: on an underivable sequent
the tactic refutes rather than merely gives up (the retired incomplete
tactic could not tell the two apart).  `◯` admits no escape: -/

/--
error: pll_g4c: backward proof search in G4iLL″ found no derivation; the calculus is complete (`G4c.equiv_tm`), so the sequent is not PLL-derivable:
  SC [A₀.somehow] A₀
-/
#guard_msgs in
example : SC [A₀.somehow] A₀ := by pll_g4c

end PLLND
