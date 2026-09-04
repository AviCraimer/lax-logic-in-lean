import LaxLogic.PLLNoFall
import LaxLogic.PLLSearchCmd

/-!
# `#searchNF`, `#refuteNF` — search and certificates for PCLL + `¬◯⊥`

The system is `NoFall.DerivUNoFall` of `PLLNoFall.lean`: PCLL extended by the
single axiom `¬◯⊥` ("NF" = *no fallible worlds*, its semantic counterpart —
the system is sound and complete for mutually confluent constraint models with
`F = ∅`, `NoFall.derivUNoFall_iff_infallible_valid`).

The adaptation of the two search directions:

* **Countermodels.**  A finite countermodel refutes `DerivUNoFall` when it is
  mutually confluent (`RNC.confB`, as for PCLL) **and has no fallible worlds**
  (`infB`).  `refuteNoFall?` filters the battery by both checks before the
  verified gate; `not_derivUNoFall_of_check` is the certificate theorem.  Note
  the checked context is `Γ` itself — the axiom needs no checking, because an
  infallible model forces `¬◯⊥` everywhere (`NoFall.force_nobot`).

* **Proofs.**  The positive engine is the PLL searcher on the extended context
  `¬◯⊥ :: Γ` — a found term certifies `DerivUNoFall Γ C` through
  `derivUNoFall_of_nd`.  As with PCLL, the searcher does not use the
  distribution scheme on its own; add `ConfluentU.distF` instances to the
  context when distribution is needed (`derivUNoFall_of_proved` consumes
  them).

Both `#searchNF` and `#refuteNF` print the usual block: sequent, verdict,
evidence, paste-ready pinning snippet.  Nothing here is trusted; the snippets
are re-checked by the kernel when pasted.
-/

open PLLFormula

namespace PLLND
namespace NoFall

/-! ## 1. Infallibility as a Boolean check -/

/-- No fallible worlds. -/
def infB (M : FinCM) : Bool := M.fall.isEmpty

theorem infallible_of_infB {M : FinCM} (hwf : M.WellFormed)
    (h : infB M = true) : Infallible (M.toModel hwf) := by
  have hf : M.fall = [] := by simpa [infB] using h
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  intro w hw
  simp only [FinCM.toModel, Set.mem_setOf_eq, FinCM.fallB, hf] at hw
  simp at hw

/-! ## 2. The certificate theorems -/

/-- **The PCLL + `¬◯⊥` refutation certificate theorem**: a checked finite
countermodel that is mutually confluent and infallible refutes
`DerivUNoFall`.  All three hypotheses are Boolean facts about concrete data,
so all three discharge by `decide`. -/
theorem not_derivUNoFall_of_check {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {C : PLLFormula}
    (hcf : RNC.confB M = true) (hinf : infB M = true)
    (h : FinCM.checkB M w Γ C = true) : ¬ DerivUNoFall Γ C := by
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := h
  have hwf := FinCM.wellFormed_of_wellB hwb
  intro hd
  have hval := sound hd (RNC.mutuallyConfluent_of_confB hwf hcf)
    (infallible_of_infB hwf hinf) ⟨w, hlt⟩
    (fun ψ hψ => (M.force_iff hwf ψ ⟨w, hlt⟩).mpr (hΓ ψ hψ))
  rw [M.force_iff hwf C ⟨w, hlt⟩, hC] at hval
  exact Bool.false_ne_true hval

/-- The positive bridge: a PLL proof over the extended context `¬◯⊥ :: Γ` is
a `DerivUNoFall` certificate. -/
theorem derivUNoFall_of_nd {Γ : List PLLFormula} {C : PLLFormula}
    (h : Nonempty (LaxND (nobot :: Γ) C)) : DerivUNoFall Γ C :=
  ⟨[], ConfluentU.DistList.nil, h⟩

/-- The positive bridge with distribution instances, matching
`RNC.derivU_of_proved`. -/
theorem derivUNoFall_of_proved (ps : List (PLLFormula × PLLFormula))
    {Γ : List PLLFormula} {C : PLLFormula}
    (h : Nonempty (LaxND
      ((ps.map fun p => ConfluentU.distF p.1 p.2) ++ nobot :: Γ) C)) :
    DerivUNoFall Γ C :=
  RNC.derivU_of_proved ps h

/-- **The extension is proper**: `¬◯⊥` is not PCLL-derivable.  The pinned
countermodel is `0 ⊳ 1` with `1` fallible (mutually confluent), where `◯⊥`
holds at `0` but `⊥` does not. -/
theorem pcll_not_nobot : ¬ ConfluentU.DerivU [] nobot :=
  RNC.not_derivU_of_checkConf (M := ⟨2, [(0, 1)], [(0, 1)], [1], []⟩)
    (w := 0) (by decide) (by decide)

/-! ## 3. Search -/

/-- The PCLL + `¬◯⊥` search configuration: candidate countermodels must be
mutually confluent and infallible. -/
def nfConfig (cfg : Search.Config := Search.budgetedConfig) : Search.Config :=
  { cfg with accept := fun M => RNC.confB M && infB M }

/-- A certified PCLL + `¬◯⊥` countermodel witness: a finite model, a world,
and the three Boolean facts `not_derivUNoFall_of_check` consumes. -/
abbrev WitnessNF (Γ : List PLLFormula) (C : PLLFormula) : Type :=
  (M : FinCM) × (w : Nat) ×'
    (RNC.confB M = true ∧ infB M = true ∧ FinCM.checkB M w Γ C = true)

/-- Confluent-infallible countermodel refutation.  `none` proves nothing, as
always. -/
def refuteNoFall? (cfg : Search.Config := Search.budgetedConfig)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (WitnessNF Γ C) :=
  match Search.refute? (nfConfig cfg) Γ C with
  | some ⟨M, w, h⟩ =>
      if hc : RNC.confB M = true then
        if hi : infB M = true then some ⟨M, w, hc, hi, h⟩ else none
      else none
  | none => none

/-- A `WitnessNF` yields PCLL + `¬◯⊥` underivability in one application. -/
theorem refutedNF_sound {Γ : List PLLFormula} {C : PLLFormula}
    (wit : WitnessNF Γ C) : ¬ DerivUNoFall Γ C :=
  not_derivUNoFall_of_check wit.2.2.1 wit.2.2.2.1 wit.2.2.2.2

/-! ## 4. Pinning snippets and reports -/

/-- The paste-ready underivability theorem certified by this witness. -/
def WitnessNF.snippet {Γ : List PLLFormula} {C : PLLFormula}
    (name : String := "underivable_nofall") (wit : WitnessNF Γ C) : String :=
  let ⟨M, w, _⟩ := wit
  String.intercalate "\n"
    [ s!"theorem {name} :",
      s!"    ¬ PLLND.NoFall.DerivUNoFall {Search.srcOfCtx Γ} \
{Search.srcOf C} :=",
      "  PLLND.NoFall.not_derivUNoFall_of_check",
      s!"    (M := {Search.srcOfCM M}) (w := {w}) (by decide) (by decide) \
(by decide)",
      "",
      s!"#print axioms {name}" ]

/-- The paste-ready derivability theorem for a proof term found over the
extended context `¬◯⊥ :: Γ`. -/
def provedNFSnippet {Γ : List PLLFormula} {C : PLLFormula}
    (name : String := "derivable_nofall") (t : G4cTm (nobot :: Γ) C) :
    String :=
  String.intercalate "\n"
    [ s!"theorem {name} :",
      s!"    PLLND.NoFall.DerivUNoFall {Search.srcOfCtx Γ} \
{Search.srcOf C} :=",
      "  PLLND.NoFall.derivUNoFall_of_nd (PLLND.Search.proved_sound",
      s!"    {t.src})",
      "",
      s!"#print axioms {name}" ]

/-- The block printed by `#searchNF`: refutation first (confluent infallible
countermodels only), then the positive searcher on `¬◯⊥ :: Γ`. -/
def searchNFReport (cfg : Search.Config) (Γ : List PLLFormula)
    (C : PLLFormula) (name : String := "found_nofall") : String :=
  match refuteNoFall? cfg Γ C with
  | some wit =>
      String.intercalate "\n"
        [ s!"sequent  {Search.seqStr Γ C}  (PCLL+¬◯⊥)",
          s!"verdict  REFUTED  {Search.summaryCM wit.1 wit.2.1} \
(confluent, infallible)",
          "", "countermodel:", Search.renderCM wit.1 (some wit.2.1),
          "", "pin it:", wit.snippet name ]
  | none =>
    let res :=
      match cfg.findBudget with
      | none => G4cTm.find (nobot :: Γ) C
      | some b => (G4cTm.findBounded b (nobot :: Γ) C).1
    match res with
    | some t =>
        String.intercalate "\n"
          [ s!"sequent  {Search.seqStr Γ C}  (PCLL+¬◯⊥)",
            s!"verdict  PROVED   {t.pretty}",
            "", "proof term (G4iLL″, over the axiom `¬◯⊥` as hypothesis):",
            s!"  {t.pretty}",
            "", "pin it:", provedNFSnippet name t ]
    | none =>
        String.intercalate "\n"
          [ s!"sequent  {Search.seqStr Γ C}  (PCLL+¬◯⊥)",
            "verdict  UNKNOWN",
            "",
            "No confluent infallible countermodel found, and the positive \
search did not",
            "close.  The positive engine does not use the distribution \
scheme on its own:",
            "add `ConfluentU.distF` instances to the context if PCLL \
distribution is needed." ]

/-- The block printed by `#refuteNF`: the countermodel engines only. -/
def refuteNFReport (cfg : Search.Config) (Γ : List PLLFormula)
    (C : PLLFormula) (name : String := "underivable_nofall") : String :=
  match refuteNoFall? cfg Γ C with
  | some wit =>
      String.intercalate "\n"
        [ s!"sequent  {Search.seqStr Γ C}  (PCLL+¬◯⊥)",
          s!"verdict  REFUTED  {Search.summaryCM wit.1 wit.2.1} \
(confluent, infallible)",
          "", "countermodel:", Search.renderCM wit.1 (some wit.2.1),
          "", "pin it:", wit.snippet name ]
  | none =>
      String.intercalate "\n"
        [ s!"sequent  {Search.seqStr Γ C}  (PCLL+¬◯⊥)",
          "verdict  NO CONFLUENT INFALLIBLE COUNTERMODEL FOUND",
          "",
          "This asserts nothing.  A countermodel found by #refute or \
#refuteConf is NOT",
          "usable here unless it also has no fallible worlds — that is \
exactly what this",
          "command enforces." ]

end NoFall
end PLLND

/-! ## 5. Smoke tests and axiom audit -/

namespace PLLND.NoFall

private def has (s sub : String) : Bool := (s.splitOn sub).length > 1

-- The axiom itself is derivable, and pinnable.
#guard
  let r := searchNFReport Search.budgetedConfig [] nobot
  has r "PROVED" && has r "derivUNoFall_of_nd" && has r "#print axioms"

-- `◯p ⊢ p` still fails without fallible worlds, and the witness is
-- infallible by construction.
#guard
  let r := searchNFReport Search.budgetedConfig
    [(PLLFormula.prop "p").somehow] (PLLFormula.prop "p")
  has r "REFUTED" && has r "not_derivUNoFall_of_check"

-- **The collapse showcase**: `◯⊥ ⊢ ⊥` is PLL-refutable (fallible top), but
-- PCLL+¬◯⊥ proves it — the fallible countermodel is exactly what `infB`
-- excludes.
#guard
  let Γ := [(PLLFormula.falsePLL).somehow]
  let C := PLLFormula.falsePLL
  has (Search.refuteReport Search.budgetedConfig Γ C) "REFUTED"
    && has (searchNFReport Search.budgetedConfig Γ C) "PROVED"

-- `#refuteNF` declines what only fallible models can refute.
#guard
  let r := refuteNFReport Search.budgetedConfig
    [(PLLFormula.falsePLL).somehow] PLLFormula.falsePLL
  has r "NO CONFLUENT INFALLIBLE COUNTERMODEL"

/-- info: 'PLLND.NoFall.not_derivUNoFall_of_check' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_derivUNoFall_of_check

/-- info: 'PLLND.NoFall.derivUNoFall_of_nd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms derivUNoFall_of_nd

/-- info: 'PLLND.NoFall.pcll_not_nobot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms pcll_not_nobot

end PLLND.NoFall

/-! ## 6. The commands -/

/-- `#searchNF Γ ⊢ C` — the PCLL + `¬◯⊥` two-sided search: confluent
infallible countermodels, positive search over the axiom as hypothesis.
Append `with cfg` to supply a `Search.Config`. -/
macro "#searchNF " Γ:term " ⊢ " C:term : command =>
  `(command| #eval (IO.println
      (PLLND.NoFall.searchNFReport PLLND.Search.budgetedConfig $Γ $C) :
      IO Unit))

@[inherit_doc «command#searchNF_⊢_»]
macro "#searchNF " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval (IO.println
      (PLLND.NoFall.searchNFReport $cfg $Γ $C) : IO Unit))

/-- `#refuteNF Γ ⊢ C` — the PCLL + `¬◯⊥` version of `#refute`: only mutually
confluent models with no fallible worlds are accepted, so the printed theorem
refutes `NoFall.DerivUNoFall`. -/
macro "#refuteNF " Γ:term " ⊢ " C:term : command =>
  `(command| #eval (IO.println
      (PLLND.NoFall.refuteNFReport PLLND.Search.budgetedConfig $Γ $C) :
      IO Unit))

@[inherit_doc «command#refuteNF_⊢_»]
macro "#refuteNF " Γ:term " ⊢ " C:term " with " cfg:term : command =>
  `(command| #eval (IO.println
      (PLLND.NoFall.refuteNFReport $cfg $Γ $C) : IO Unit))
