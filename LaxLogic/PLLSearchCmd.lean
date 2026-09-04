import LaxLogic.PLLSearch
import LaxLogic.PLLSearchConf

/-!
# `#search`, `#refute`, `#refuteConf` — the search API as commands

`LaxLogic/PLLSearch.lean` returns dependent data (`Answer`, `Verdict`,
`Witness`), which is right for programs and wrong for a first look at a
sequent: every example in the manual used to wrap the call in the same
`match … with | .proved _ => "…"` boilerplate.  This module removes that.

```lean
import LaxLogic.PLLSearchCmd
open PLLFormula PLLND PLLND.Search

#search [] ⊢ (prop "p").ifThen ((prop "p").somehow)
#refute [] ⊢ ((prop "p").somehow).ifThen (prop "p")
```

Each command prints, in one block:

* the sequent, in the usual notation;
* the verdict — `PROVED`, `REFUTED` or `UNKNOWN`, the last one carrying the
  reason (which knob to turn) rather than just the word;
* for a refutation, a **scope** line: whether the model is mutually
  confluent, and so whether it refutes PCLL as well as PLL (`scopeLines`);
* the evidence: the G4iLL″ rule tree, or the countermodel in the compact
  `renderCM` form (worlds, cover edges of `Rᵢ`, `Rₘ` successors, forced
  atoms), rather than a raw `FinCM` record — simplified, by default, to the
  worlds and edges the refutation actually uses (`Config.simplify`);
* the **pinning snippet**: paste-ready Lean source for the theorem that
  records the finding, `#print axioms` line included.

A configuration may be given after `with`:

```lean
#search [] ⊢ someGoal with { findBudget := none }
```

Without one, the commands use `Search.budgetedConfig` — the standard search
with the node budget **on** at `defaultFindBudget` (200000 visited sequents).
That is a deliberate difference from `decide {} Γ C` / `settle {} Γ C`, whose
default is still no budget; see §10 of `PLLSearch.lean`.

Nothing here is trusted: the commands only display what the search returned,
and the snippets they print are re-checked by the kernel when pasted.
-/

open PLLFormula

namespace PLLND.Search

/-! ## 1. Reports -/

/-- A sequent in the usual notation, using `PLLFormula`'s `Repr`. -/
def seqStr (Γ : List PLLFormula) (C : PLLFormula) : String :=
  (if Γ.isEmpty then ""
   else String.intercalate ", " (Γ.map fun F => s!"{repr F}") ++ " ") ++
  s!"⊢ {repr C}"

/-- **How far a countermodel reaches**: the `scope` line of a refutation
report.

A finite countermodel refutes `LaxND` (PLL) always, and `ConfluentU.DerivU`
(PCLL, PLL + `◯(A ∨ B) ⊃ ◯A ∨ ◯B`) only when it is mutually confluent.  The
distinction is invisible in the model picture and easy to forget, and using a
non-confluent model against a PCLL claim is simply a wrong proof — so every
refutation report states which of the two it has, and names the command to
use when the answer is the narrow one.

`RNC.confB` is the same Boolean test `#refuteConf` filters by, so this line
is a fact about the model returned, not a guess. -/
def scopeLines (M : FinCM) : List String :=
  if RNC.confB M then
    [ "scope    PLL and PCLL: the model is mutually confluent, so it also",
      "         refutes ConfluentU.DerivU (RNC.not_derivU_of_checkConf)" ]
  else
    [ "scope    PLL only: the model is NOT mutually confluent, so it refutes",
      "         LaxND and says nothing about PCLL — use #refuteConf there" ]

/-- The block printed by `#search`: sequent, verdict, evidence, pinning
snippet. -/
def searchReport (cfg : Config) (Γ : List PLLFormula) (C : PLLFormula)
    (name : String := "found") : String :=
  let v := settleWhy cfg Γ C
  let body : List String :=
    match v with
    | .proved t =>
        [ "", "proof term (G4iLL″):", s!"  {t.pretty}",
          "", "pin it:", t.snippet name ]
    | .refuted M w h =>
        scopeLines M ++
        [ "", "countermodel:", renderCM M (some w),
          "", "pin it:", Witness.snippet (Γ := Γ) (C := C) name ⟨M, w, h⟩ ]
    | .unknown _ =>
        [ "", "no certificate: the verdict line says which bound bit." ]
  String.intercalate "\n"
    ([ s!"sequent  {seqStr Γ C}", s!"verdict  {v.summary}" ] ++ body)

/-- The block printed by `#refute`: the negative engines only (battery, then
the closure emitter), the model rendered compactly, and the pinning
snippet. -/
def refuteReport (cfg : Config) (Γ : List PLLFormula) (C : PLLFormula)
    (name : String := "underivable") : String :=
  match countermodel Γ C cfg with
  | some wit =>
      String.intercalate "\n"
        ([ s!"sequent  {seqStr Γ C}",
           s!"verdict  REFUTED  {summaryCM wit.1 wit.2.1}" ] ++
         scopeLines wit.1 ++
         [ "", "countermodel:", renderCM wit.1 (some wit.2.1),
           "", "pin it:", wit.snippet name ])
  | none =>
      String.intercalate "\n"
        [ s!"sequent  {seqStr Γ C}",
          "verdict  NO COUNTERMODEL FOUND",
          "",
          "This asserts nothing about the sequent: the battery and the \
closure emitter",
          "are both incomplete.  Widen Config.frames, or raise \
Config.emitClosureCap." ]

end PLLND.Search

namespace PLLND.RNC

/-- The block printed by `#refuteConf`: as `#refute`, but only mutually
confluent models are accepted, so the witness refutes `ConfluentU.DerivU`
(PCLL) and not merely `LaxND`. -/
def refuteConfReport (cfg : Search.Config) (Γ : List PLLFormula)
    (C : PLLFormula) (name : String := "underivable_pcll") : String :=
  match refuteConf? cfg Γ C with
  | some wit =>
      String.intercalate "\n"
        ([ s!"sequent  {Search.seqStr Γ C}  (PCLL)",
           s!"verdict  REFUTED  {Search.summaryCM wit.1 wit.2.1}" ] ++
         Search.scopeLines wit.1 ++
         [ "", "countermodel:", Search.renderCM wit.1 (some wit.2.1),
           "", "pin it:", wit.snippet name ])
  | none =>
      String.intercalate "\n"
        [ s!"sequent  {Search.seqStr Γ C}  (PCLL)",
          "verdict  NO CONFLUENT COUNTERMODEL FOUND",
          "",
          "This asserts nothing.  Note that a countermodel found by \
#refute is NOT",
          "usable here unless it is mutually confluent — that is exactly \
what this",
          "command enforces." ]

end PLLND.RNC

/-! ## 2. Smoke tests

Each report is exercised on a tiny sequent, so a regression in the renderers
or the snippet emitters fails the build. -/

namespace PLLND.Search

/-- Does `s` contain `sub`? -/
private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

#guard
  let r := searchReport budgetedConfig []
    ((PLLFormula.prop "p").ifThen ((PLLFormula.prop "p").somehow))
  has r "PROVED" && has r "proved_sound" && has r "#print axioms"

#guard
  let r := searchReport budgetedConfig []
    (((PLLFormula.prop "p").somehow).ifThen (PLLFormula.prop "p"))
  has r "REFUTED" && has r "not_provable_of_check" && has r "⊑>"

#guard
  let r := refuteReport budgetedConfig [(PLLFormula.prop "p").somehow]
    (PLLFormula.prop "p")
  has r "REFUTED" && has r "fallible"

-- The PCLL trap, as a test: the distribution axiom is PLL-refutable but has
-- no *confluent* countermodel, so `#refuteConf` must decline it — and the
-- `#refute` report on the same sequent must say, in the scope line, that
-- what it found is good for PLL only.
#guard
  let Γ := [((PLLFormula.prop "p").or (PLLFormula.prop "q")).somehow]
  let C := ((PLLFormula.prop "p").somehow).or ((PLLFormula.prop "q").somehow)
  has (RNC.refuteConfReport budgetedConfig Γ C) "NO CONFLUENT COUNTERMODEL"
    && has (refuteReport budgetedConfig Γ C) "REFUTED"
    && has (refuteReport budgetedConfig Γ C) "PLL only"

-- …and the scope line is not stuck on that answer: `◯p ⊢ p` is refuted by a
-- confluent model, and the report says so.
#guard
  has (refuteReport budgetedConfig [(PLLFormula.prop "p").somehow]
    (PLLFormula.prop "p")) "PLL and PCLL"

end PLLND.Search

/-! ## 3. The commands

Each is a macro expanding to an `#eval` of the corresponding report, so the
sequent's `Γ` and `C` elaborate in the user's own scope, with the user's
`open`s and abbreviations. -/

/-- `#search Γ ⊢ C` — run the two-sided procedure and print the verdict, the
proof term or countermodel, and the paste-ready pinning snippet.  Append
`with cfg` to supply a `Search.Config`; the default is
`Search.budgetedConfig` (node budget on). -/
macro "#search " Γ:term " ⊢ " C:term : command =>
  `(command| #eval (IO.println
      (PLLND.Search.searchReport PLLND.Search.budgetedConfig $Γ $C) : IO Unit))

@[inherit_doc «command#search_⊢_»]
macro "#search " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval (IO.println
      (PLLND.Search.searchReport $cfg $Γ $C) : IO Unit))

/-- `#refute Γ ⊢ C` — run the countermodel engines only and print the model
compactly together with the paste-ready underivability theorem. -/
macro "#refute " Γ:term " ⊢ " C:term : command =>
  `(command| #eval (IO.println
      (PLLND.Search.refuteReport PLLND.Search.budgetedConfig $Γ $C) : IO Unit))

@[inherit_doc «command#refute_⊢_»]
macro "#refute " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval (IO.println
      (PLLND.Search.refuteReport $cfg $Γ $C) : IO Unit))

/-- `#refuteConf Γ ⊢ C` — the PCLL version of `#refute`: only mutually
confluent countermodels are accepted, so the printed theorem refutes
`ConfluentU.DerivU`. -/
macro "#refuteConf " Γ:term " ⊢ " C:term : command =>
  `(command| #eval (IO.println
      (PLLND.RNC.refuteConfReport PLLND.Search.budgetedConfig $Γ $C) : IO Unit))

@[inherit_doc «command#refuteConf_⊢_»]
macro "#refuteConf " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval (IO.println
      (PLLND.RNC.refuteConfReport $cfg $Γ $C) : IO Unit))
