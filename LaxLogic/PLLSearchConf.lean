import LaxLogic.PLLSearch
import LaxLogic.PLLConfluentComplete

/-!
# `PLLND.RNC` — search and certificates for PCLL

PCLL is PLL plus the distribution scheme `◯(A ∨ B) ⊃ (◯A ∨ ◯B)`; derivability
from premises is `ConfluentU.DerivU Γ C`, i.e. natural deduction from `Γ`
together with finitely many instances of the scheme.

This module is the PCLL half of the search API.  It exists because the PLL
countermodel search has a **trap** for PCLL users: a model returned by
`Search.refute?` refutes `LaxND`, but refutes `DerivU` only if it is
*mutually confluent*.  Most of the default battery happens to be confluent
and the closure emitter is not, so reusing a PLL countermodel against
`DerivU` is a real correctness hazard.  `refuteConf?` removes it by
construction: it filters the candidate models by `confB` **before** the
verified gate, and returns a witness whose type carries both facts.

Everything here was previously in `wip/rnc_probe.lean`; it is promoted
unchanged (same namespace `PLLND.RNC`, same statements), so a PCLL user no
longer has to `import wip.…`, and the probe files that used the old location
keep working through the import.

## What is verified

* `not_derivU_of_checkConf : confB M = true → FinCM.checkB M w Γ C = true →
  ¬ ConfluentU.DerivU Γ C` — the negative certificate theorem.  Both
  hypotheses are Boolean facts about concrete data, so both discharge by
  `decide` inside the kernel.
* `derivU_of_proved` — the positive bridge: a PLL proof from *any* list of
  distribution instances is a `DerivU` certificate.

`refuteConf?` itself is untrusted search, like everything in
`PLLSearch.lean`: narrowing the battery by `confB` can only cause misses.
-/

open PLLFormula

namespace PLLND
namespace RNC

/-! ## 1. Mutual confluence as a Boolean check -/

/-- Mutual confluence of a `FinCM` (on the reflexive closures, matching
`toModel`): `Rₘ x w → Rᵢ x v → ∃ u, Rᵢ w u ∧ Rₘ v u`. -/
def confB (M : FinCM) : Bool :=
  (List.range M.n).all fun x => (List.range M.n).all fun w =>
    (List.range M.n).all fun v =>
      !(M.rmB x w) || !(M.riB x v) ||
        ((List.range M.n).any fun u => M.riB w u && M.rmB v u)

theorem mutuallyConfluent_of_confB {M : FinCM} (hwf : M.WellFormed)
    (h : confB M = true) : MutuallyConfluent (M.toModel hwf) := by
  unfold MutuallyConfluent
  intro x w v hm hi
  simp only [confB, List.all_eq_true, List.mem_range] at h
  have hx := h x.1 x.2 w.1 w.2 v.1 v.2
  have hm' : M.rmB x.1 w.1 = true := hm
  have hi' : M.riB x.1 v.1 = true := hi
  rw [hm', hi'] at hx
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true,
    List.mem_range] at hx
  obtain ⟨u, hu, hb⟩ := hx
  rw [Bool.and_eq_true] at hb
  exact ⟨⟨u, hu⟩, hb.1, hb.2⟩

/-! ## 2. The certificate theorems -/

/-- **The PCLL refutation certificate theorem**: a checked finite
countermodel that is mutually confluent refutes `DerivU` (PLL + the
distribution scheme), not merely `LaxND`. -/
theorem not_derivU_of_checkConf {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {C : PLLFormula}
    (hcf : confB M = true) (h : FinCM.checkB M w Γ C = true) :
    ¬ ConfluentU.DerivU Γ C := by
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := h
  have hwf := FinCM.wellFormed_of_wellB hwb
  intro hd
  have hval := ConfluentU.derivU_sound hd
    (mutuallyConfluent_of_confB hwf hcf) ⟨w, hlt⟩
    (fun ψ hψ => (M.force_iff hwf ψ ⟨w, hlt⟩).mpr (hΓ ψ hψ))
  rw [M.force_iff hwf C ⟨w, hlt⟩, hC] at hval
  exact Bool.false_ne_true hval

/-- The positive bridge: a PLL proof from a list of distribution
instances is a `DerivU` certificate, whatever the instances were. -/
theorem derivU_of_proved {Γ : List PLLFormula} {C : PLLFormula}
    (ps : List (PLLFormula × PLLFormula))
    (h : Nonempty (LaxND ((ps.map fun p => ConfluentU.distF p.1 p.2) ++ Γ) C)) :
    ConfluentU.DerivU Γ C := by
  refine ⟨ps.map fun p => ConfluentU.distF p.1 p.2, ?_, h⟩
  intro θ hθ
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hθ
  exact ⟨p.1, p.2, rfl⟩

/-- Variant of `derivU_of_proved` matching the probe's premise order
(`X` before the instances). -/
theorem derivU_of_proved' (ps : List (PLLFormula × PLLFormula))
    {X C : PLLFormula}
    (h : Nonempty (LaxND (X :: ps.map fun p => ConfluentU.distF p.1 p.2) C)) :
    ConfluentU.DerivU [X] C := by
  obtain ⟨p⟩ := h
  refine ⟨ps.map fun p => ConfluentU.distF p.1 p.2, ?_, ⟨p.rename ?_⟩⟩
  · intro θ hθ
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hθ
    exact ⟨q.1, q.2, rfl⟩
  · intro ψ hmem
    simp only [List.mem_cons, List.mem_append] at hmem ⊢
    tauto

/-! ## 3. Confluent countermodel search

`Search.Config.accept` is the untrusted pre-filter on candidate models.
Setting it to `confB` makes both refutation stages skip non-confluent
candidates instead of stopping at the first one, which is what turns
"`refute?` sometimes returns something usable for PCLL" into "`refuteConf?`
returns only things usable for PCLL". -/

/-- The standard PCLL search configuration: the sequent-first default
(`Search.budgetedConfig`, node budget on) restricted to mutually confluent
candidate models. -/
def confluentConfig (cfg : Search.Config := Search.budgetedConfig) :
    Search.Config :=
  { cfg with accept := confB }

/-- A certified **PCLL** countermodel witness: a finite model `M`, a world
`w`, and proofs that `M` is mutually confluent and that the verified checker
accepts it for the sequent.  Exactly what `not_derivU_of_checkConf`
consumes. -/
abbrev WitnessConf (Γ : List PLLFormula) (C : PLLFormula) : Type :=
  (M : FinCM) × (w : Nat) ×'
    (confB M = true ∧ FinCM.checkB M w Γ C = true)

/-- **Confluent-countermodel refutation.**  Runs the ordinary battery and
emitter with `Config.accept` set to `confB`, then re-derives the confluence
fact as a proof, so the witness carries both halves of the PCLL certificate.

`none` proves nothing, as always. -/
def refuteConf? (cfg : Search.Config := Search.budgetedConfig)
    (Γ : List PLLFormula) (C : PLLFormula) : Option (WitnessConf Γ C) :=
  match Search.refute? (confluentConfig cfg) Γ C with
  | some ⟨M, w, h⟩ =>
      if hc : confB M = true then some ⟨M, w, hc, h⟩ else none
  | none => none

/-- Sequent-first `refuteConf?`, matching `Search.countermodel`. -/
def countermodelConf (Γ : List PLLFormula) (C : PLLFormula)
    (cfg : Search.Config := Search.budgetedConfig) : Option (WitnessConf Γ C) :=
  refuteConf? cfg Γ C

/-- A `WitnessConf` yields PCLL underivability in one application. -/
theorem refutedU_sound {Γ : List PLLFormula} {C : PLLFormula}
    (wit : WitnessConf Γ C) : ¬ ConfluentU.DerivU Γ C :=
  not_derivU_of_checkConf wit.2.2.1 wit.2.2.2

/-- The witness's model, rendered compactly, refuting world marked. -/
def WitnessConf.render {Γ : List PLLFormula} {C : PLLFormula}
    (wit : WitnessConf Γ C) : String :=
  Search.renderCM wit.1 (some wit.2.1)

/-- The paste-ready PCLL underivability theorem certified by this witness,
with the `#print axioms` audit line.  Both side conditions are Boolean facts
about concrete data, hence `by decide`. -/
def WitnessConf.snippet {Γ : List PLLFormula} {C : PLLFormula}
    (name : String := "underivable_pcll") (wit : WitnessConf Γ C) : String :=
  let ⟨M, w, _⟩ := wit
  String.intercalate "\n"
    [ s!"theorem {name} :",
      s!"    ¬ ConfluentU.DerivU {Search.srcOfCtx Γ} {Search.srcOf C} :=",
      "  PLLND.RNC.not_derivU_of_checkConf",
      s!"    (M := {Search.srcOfCM M}) (w := {w}) (by decide) (by decide)",
      "",
      s!"#print axioms {name}" ]

/-! ## 4. Smoke tests and axiom audit -/

-- `◯p ⊢ p` is refuted in PCLL too: the battery's confluent frames suffice.
#guard (refuteConf? {} [(PLLFormula.prop "p").somehow] (PLLFormula.prop "p")).isSome

-- The distribution axiom itself: PLL refutes `◯(p∨q) ⊢ ◯p ∨ ◯q`, so every
-- countermodel to it must be non-confluent — `refuteConf?` finds none, while
-- the unfiltered `refute?` does return one (which is exactly the trap).
#guard
  let Γ := [((PLLFormula.prop "p").or (PLLFormula.prop "q")).somehow]
  let C := ((PLLFormula.prop "p").somehow).or ((PLLFormula.prop "q").somehow)
  (refuteConf? {} Γ C).isNone && (Search.refute? {} Γ C).isSome

/-- info: 'PLLND.RNC.not_derivU_of_checkConf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms not_derivU_of_checkConf

/-- info: 'PLLND.RNC.derivU_of_proved' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms derivU_of_proved

end RNC
end PLLND
