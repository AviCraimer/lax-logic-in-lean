import LaxLogic.PLLNoFallNF
import LaxLogic.PLLSearchNoFall

/-!
# PCLL + `¬◯⊥` and PLL + `¬◯⊥` diverge on ◯-normalised sequents

The normalisation of `PLLNoFallNF.lean` compiles the `◯∨`- and `◯⊥`-cases
away, so one could hope that over `¬◯⊥` the distribution scheme has no
residual content — that on ◯-normal sequents, PLL + `¬◯⊥` and PCLL + `¬◯⊥`
agree, and the repaired terminating calculus G4iLL″ (with the axiom as a
persistent hypothesis) would already be complete for the confluent system.

**It is not so.**  The ◯-normal sequent

    ◯(a ⊃ (b ∨ c)), ◯a  ⊢  ◯b ∨ ◯c

is derivable in PCLL + `¬◯⊥` (`sep_derivable`: merge the two hypotheses by
the strong-monad laws, distribute) but not in PLL + `¬◯⊥`
(`sep_not_pll_nofall`: a five-world infallible countermodel under the `∀∃`
clause — two `Rᵢ`-branches over the root whose `Rₘ`-witnesses settle `b ∨ c`
differently, so neither `◯b` nor `◯c` holds at the root; the model is not
mutually confluent, as by soundness it cannot be).

Consequently **distribution is not admissible from `¬◯⊥`, even on
◯-normalised sequents**: a terminating calculus for PCLL + `¬◯⊥` must carry
a genuinely distribution-aware `◯`-rule (e.g. a `laxL` whose conclusion may
be a disjunction of `◯`-formulas and `⊥`), and the Pitts-style interpolant
computations for the two systems will differ exactly there.  Both facts are
kernel-checked below by `decide`.
-/

open PLLFormula

namespace PLLND
namespace NoFall

/-- Derivability in **PLL + `¬◯⊥`** (no distribution): `LaxND` with the
axiom as a persistent hypothesis, the same convention as `DerivUNoFall`. -/
def DerivPllNoFall (Γ : List PLLFormula) (C : PLLFormula) : Prop :=
  Nonempty (LaxND (nobot :: Γ) C)

theorem DerivUNoFall.of_pll {Γ : List PLLFormula} {C : PLLFormula}
    (h : DerivPllNoFall Γ C) : DerivUNoFall Γ C :=
  ⟨[], ConfluentU.DistList.nil, h⟩

/-! ## The separating sequent -/

def sepHyp₁ : PLLFormula :=
  ((prop "a").ifThen ((prop "b").or (prop "c"))).somehow
def sepHyp₂ : PLLFormula := (prop "a").somehow
def sepGoal : PLLFormula :=
  ((prop "b").somehow).or ((prop "c").somehow)

/-- The sequent is ◯-normal: every `◯` sits on an atom or an
implication. -/
theorem sep_obNormal :
    ObNormal sepHyp₁ ∧ ObNormal sepHyp₂ ∧ ObNormal sepGoal :=
  ⟨⟨trivial, trivial, trivial⟩, trivial, ⟨trivial, trivial⟩⟩

/-- **PCLL + `¬◯⊥` derives the separator** (one distribution instance,
`distF b c`; proof term found by `#search` and kernel-rechecked). -/
theorem sep_derivable : DerivUNoFall [sepHyp₁, sepHyp₂] sepGoal :=
  derivUNoFall_of_proved [(prop "b", prop "c")] (PLLND.Search.proved_sound
    (.impLLaxLax (A := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
      (B := (((PLLFormula.prop "b").somehow).or ((PLLFormula.prop "c").somehow)))
      (X := ((PLLFormula.prop "a").ifThen ((PLLFormula.prop "b").or (PLLFormula.prop "c"))))
      (by decide) (by decide)
      (.laxL (A := (PLLFormula.prop "a")) (by decide)
        (.laxR (.impLProp (a := "a")
          (B := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
          (by decide) (by decide)
          (.orL (A := (PLLFormula.prop "b")) (B := (PLLFormula.prop "c"))
            (by decide) (.orR1 (.init (by decide)))
            (.orR2 (.init (by decide)))))))
      (.orL (A := ((PLLFormula.prop "b").somehow))
        (B := ((PLLFormula.prop "c").somehow)) (by decide)
        (.orR1 (.laxL (A := (PLLFormula.prop "b")) (by decide)
          (.laxR (.init (by decide)))))
        (.orR2 (.laxL (A := (PLLFormula.prop "c")) (by decide)
          (.laxR (.init (by decide))))))))

/-- The five-world infallible `∀∃`-countermodel: `0 ⊑ 1, 2`;
`1 ⊳ 3 (a, b)`, `2 ⊳ 4 (a, c)`, `0 ⊳ 3`. -/
def sepCM : FinCM :=
  ⟨5, [(0, 1), (0, 2), (1, 3), (2, 4), (0, 3), (0, 4)],
   [(1, 3), (2, 4), (0, 3)], [],
   [(3, "a"), (4, "a"), (3, "b"), (4, "c")]⟩

/-- **PLL + `¬◯⊥` does not derive the separator.** -/
theorem sep_not_pll_nofall : ¬ DerivPllNoFall [sepHyp₁, sepHyp₂] sepGoal :=
  FinCM.not_provable_of_check (M := sepCM) (w := 0) (by decide)

/-- The countermodel is not mutually confluent — by soundness it cannot
be. -/
theorem sepCM_not_confluent : RNC.confB sepCM = false := by decide

/-! ## The cut-necessity sequent

A second, sharper separator.  For the calculus design one might hope that
widening `laxL`'s conclusion to disjunctions of `◯`-formulas (and `⊥`)
suffices for a **single-succedent** cut-free calculus for PCLL + `¬◯⊥`.  The
sequent

    ◯(a ⊃ (b ∨ c)), ◯a, ◯b ⊃ p, ◯c ⊃ p  ⊢  p

refutes that hope: it is PCLL + `¬◯⊥`-derivable (`cutNeed_derivable`,
through the intermediary `◯b ∨ ◯c` — a cut), but any cut-free
single-succedent derivation would have to commit to the goal `◯b` or `◯c`
*before* opening the box in which `b ∨ c` is decided, and the other branch
strands.  (It is not PLL + `¬◯⊥`-derivable at all, `cutNeed_not_pll` —
distribution is where the intermediary comes from.)  The calculus for
PCLL + `¬◯⊥` must therefore carry a **multi-succedent** `◯`-rule: from
`Γ, X ⊢ ◯B₁, …, ◯Bₖ` infer `Γ, ◯X ⊢ ◯B₁, …, ◯Bₖ, Δ` — the succedent of
`◯`-formulas travels through the implication eliminations together.
PLL + `¬◯⊥` never needs this (no distribution), which is why the
single-succedent format of G4iLL″ suffices there. -/

def cutHyp₃ : PLLFormula := ((prop "b").somehow).ifThen (prop "p")
def cutHyp₄ : PLLFormula := ((prop "c").somehow).ifThen (prop "p")

/-- **PCLL + `¬◯⊥` derives the cut-necessity sequent** (through
`◯b ∨ ◯c`). -/
theorem cutNeed_derivable :
    DerivUNoFall [sepHyp₁, sepHyp₂, cutHyp₃, cutHyp₄] (prop "p") :=
  derivUNoFall_of_proved [(prop "b", prop "c")] (PLLND.Search.proved_sound
    (.impLLaxLax (A := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
      (B := (((PLLFormula.prop "b").somehow).or ((PLLFormula.prop "c").somehow)))
      (X := ((PLLFormula.prop "a").ifThen ((PLLFormula.prop "b").or (PLLFormula.prop "c"))))
      (by decide) (by decide)
      (.laxL (A := (PLLFormula.prop "a")) (by decide)
        (.laxR (.impLProp (a := "a")
          (B := ((PLLFormula.prop "b").or (PLLFormula.prop "c")))
          (by decide) (by decide)
          (.orL (A := (PLLFormula.prop "b")) (B := (PLLFormula.prop "c"))
            (by decide) (.orR1 (.init (by decide)))
            (.orR2 (.init (by decide)))))))
      (.orL (A := ((PLLFormula.prop "b").somehow))
        (B := ((PLLFormula.prop "c").somehow)) (by decide)
        (.impLLaxLax (A := (PLLFormula.prop "b")) (B := (PLLFormula.prop "p"))
          (X := (PLLFormula.prop "b")) (by decide) (by decide)
          (.laxR (.init (by decide))) (.init (by decide)))
        (.impLLaxLax (A := (PLLFormula.prop "c")) (B := (PLLFormula.prop "p"))
          (X := (PLLFormula.prop "c")) (by decide) (by decide)
          (.laxR (.init (by decide))) (.init (by decide))))))

/-- The `p`-decorated five-world countermodel: `p` everywhere except the
root. -/
def cutCM : FinCM :=
  ⟨5, [(0, 1), (0, 2), (1, 3), (2, 4), (0, 3), (0, 4)],
   [(1, 3), (2, 4), (0, 3)], [],
   [(3, "a"), (4, "a"), (3, "b"), (4, "c"),
    (1, "p"), (2, "p"), (3, "p"), (4, "p")]⟩

/-- **PLL + `¬◯⊥` does not derive the cut-necessity sequent.** -/
theorem cutNeed_not_pll :
    ¬ DerivPllNoFall [sepHyp₁, sepHyp₂, cutHyp₃, cutHyp₄] (prop "p") :=
  FinCM.not_provable_of_check (M := cutCM) (w := 0) (by decide)

end NoFall
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.NoFall.sep_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.sep_derivable

/-- info: 'PLLND.NoFall.sep_not_pll_nofall' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.sep_not_pll_nofall

/-- info: 'PLLND.NoFall.cutNeed_derivable' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.cutNeed_derivable

/-- info: 'PLLND.NoFall.cutNeed_not_pll' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.cutNeed_not_pll
