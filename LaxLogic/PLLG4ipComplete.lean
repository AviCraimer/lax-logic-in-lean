import LaxLogic.PLLG4HComp
import LaxLogic.PLLNoFallNF

/-!
# The `◯`-free base of G4iLL is Dyckhoff's G4ip, and it *is* complete

`PLLG4Gap.lean` shows that Iemhoff's calculus **G4iLL** (our `G4`,
arXiv:2209.08976 Fig. 2.3) is incomplete for PLL: `SC [◯G', F'] r` holds
while `¬ G4 [◯G', F'] r` (both kernel-checked, `sc_but_not_G4`).  This
file locates the defect exactly.  On sequents containing no `◯` — where
`G4` is literally Dyckhoff's G4ip (JSL 57(3), 1992) and `SC` is G3ip —
the equivalence Iemhoff claims **does** hold:

    (∀ ψ ∈ Γ, isIPL ψ) → isIPL C → SC Γ C → G4 Γ C

(`G4.completeness_isIPL`), and hence `G4 Γ C ↔ SC Γ C ↔ IPLND Γ C` on
the fragment (`G4.iff_SC_isIPL`, `G4.iff_IPLND`), and contraction is
admissible there (`G4.contract_isIPL`) although
`PLLG4Gap.contraction_not_admissible` refutes it in general.  So the
incompleteness of G4iLL is created **exactly** by its two
`◯`-antecedent implication rules `R◯→`/`L◯→` (`impLLax`,
`impLLaxLax`) together with `L◯` (`laxL`) — not by the propositional
base it inherits from Dyckhoff.  `G4.base_complete_gap_modal` packages
the two halves as one statement.

## Route

The proof does **not** re-run Dyckhoff–Negri's contraction-admissibility
induction for G4ip.  It goes through the repaired calculus `G4c`
(**G4iLL″**, `PLLG4H.lean`), whose completeness `SC Γ C → G4c Γ C` is
already unconditional (`G4c.completeness`, `PLLG4HComp.lean`, resting on
the contraction lemma of `PLLG4HCtr.lean` and `selfAbsorb` of
`PLLG4HCut.lean`).  What makes this legitimate here — and is the one
observation the file contributes — is that

* `G4h`'s **propositional** rules (`init`, `botL`, `andR`, `orR1`,
  `orR2`, `impR`, `andL`, `orL`, `impLProp`, `impLBot`, `impLAnd`,
  `impLOr`, `impLImp`) are *verbatim* `G4`'s, modulo the height index:
  the repair of `PLLG4H.lean` touches only the three modal rules
  (`laxL`, `impLLax`, `impLLaxLax`), where `G4c` keeps material that
  `G4` consumes;
* those three modal rules cannot fire on a `◯`-free sequent, since each
  needs a principal formula containing `◯` (`◯A` in the context for
  `laxL`, `◯A ⊃ B` in the context for the other two), and `laxR` cannot
  fire because its conclusion is `◯A`;
* `◯`-freeness is inherited by the premises of every propositional
  rule — each premise formula is built from subformulas of the
  conclusion (`A ⊃ (B ⊃ D)` from `(A ∧ B) ⊃ D`, and so on).

So a `G4h` derivation of a `◯`-free sequent is, rule for rule, a `G4`
derivation: `G4h.toG4_isIPL` is a plain structural induction in which
the four modal cases are discharged by contradiction.  Had `G4c` been
cumulative where Dyckhoff consumes *in the propositional rules*, this
route would have needed contraction for `G4` after all; it is not, and
it does not.

`isIPL` is the repository's `◯`-freeness predicate (`PLLNDCore.lean`),
the same one `conservativity_IPL` is stated with.

## Provenance (`docs/calculus-map.md`)

`G4` = Iemhoff's G4iLL; `SC`/`SCh` = G3iLL; `G4h`/`G4c` = this
repository's repair G4iLL″; `LaxND` = the natural-deduction system
`Deriv` of the map; `IPLND` = intuitionistic natural deduction
(`PLLNDCore.lean`).  On `◯`-free sequents `G4` is Dyckhoff's G4ip and
`SC` is G3ip, so the results below are statements about **IPC**, proved
inside the PLL formalisation.
-/

open PLLFormula

namespace PLLND

/-! ## `◯`-freeness bookkeeping -/

/-- `◯`-freeness of a context is inherited under `cons`. -/
private theorem ipl_cons {Γ : List PLLFormula} {A : PLLFormula}
    (hA : isIPL A) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) : ∀ ψ ∈ A :: Γ, isIPL ψ := by
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hA
  · exact hΓ _ hψ

/-- A `Perm`-exposed principal formula and the remaining context are both
`◯`-free when the whole context is.  This is the shape every left rule of
`G4`/`G4h` presents its principal formula in. -/
private theorem ipl_perm {Γ Δ : List PLLFormula} {P : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (h : Γ.Perm (P :: Δ)) :
    isIPL P ∧ ∀ ψ ∈ Δ, isIPL ψ :=
  ⟨hΓ _ (h.symm.subset (.head _)),
    fun _ hψ => hΓ _ (h.symm.subset (.tail _ hψ))⟩

namespace G4h

/-! ## The repaired calculus collapses onto G4iLL on the `◯`-free fragment -/

/-- **The `◯`-free restriction of G4iLL″ is G4iLL.**  A `G4h` derivation
of a `◯`-free sequent uses only the propositional rules, which `G4` has
verbatim; the four modal cases are impossible.

This is the step that lets the already-proved completeness of `G4c`
(`G4c.completeness`) be transported to the incomplete `G4`, without
re-proving contraction admissibility for Dyckhoff's calculus. -/
theorem toG4_isIPL : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    G4h n Γ C → (∀ ψ ∈ Γ, isIPL ψ) → isIPL C → G4 Γ C := by
  intro n Γ C d
  induction d with
  | init h => intro _ _; exact .init h
  | botL h => intro _ _; exact .botL h
  | andR _ _ ih₁ ih₂ => rintro hΓ ⟨hA, hB⟩; exact .andR (ih₁ hΓ hA) (ih₂ hΓ hB)
  | orR1 _ ih => rintro hΓ ⟨hA, _⟩; exact .orR1 (ih hΓ hA)
  | orR2 _ ih => rintro hΓ ⟨_, hB⟩; exact .orR2 (ih hΓ hB)
  | impR _ ih => rintro hΓ ⟨hA, hB⟩; exact .impR (ih (ipl_cons hA hΓ) hB)
  -- `R◯`: the conclusion `◯A` is not `◯`-free
  | laxR _ _ => intro _ hC; simp at hC
  | @andL _ _ Δ A B _ h _ ih =>
      intro hΓ hC
      obtain ⟨⟨hA, hB⟩, hΔ⟩ := ipl_perm hΓ h
      exact .andL h (ih (ipl_cons hA (ipl_cons hB hΔ)) hC)
  | @orL _ _ Δ A B _ h _ _ ih₁ ih₂ =>
      intro hΓ hC
      obtain ⟨⟨hA, hB⟩, hΔ⟩ := ipl_perm hΓ h
      exact .orL h (ih₁ (ipl_cons hA hΔ) hC) (ih₂ (ipl_cons hB hΔ) hC)
  -- `L◯`: the principal `◯A` is in the context, so the context is not `◯`-free
  | laxL h _ _ => intro hΓ _; have hbox := hΓ _ h; simp at hbox
  | @impLProp _ _ Δ a B _ h ha _ ih =>
      intro hΓ hC
      obtain ⟨⟨_, hB⟩, hΔ⟩ := ipl_perm hΓ h
      exact .impLProp h ha (ih (ipl_cons hB hΔ) hC)
  | @impLBot _ _ Δ B _ h _ ih =>
      intro hΓ hC
      obtain ⟨_, hΔ⟩ := ipl_perm hΓ h
      exact .impLBot h (ih hΔ hC)
  | @impLAnd _ _ Δ A B D _ h _ ih =>
      intro hΓ hC
      obtain ⟨⟨⟨hA, hB⟩, hD⟩, hΔ⟩ := ipl_perm hΓ h
      exact .impLAnd h (ih (ipl_cons ⟨hA, hB, hD⟩ hΔ) hC)
  | @impLOr _ _ Δ A B D _ h _ ih =>
      intro hΓ hC
      obtain ⟨⟨⟨hA, hB⟩, hD⟩, hΔ⟩ := ipl_perm hΓ h
      exact .impLOr h (ih (ipl_cons ⟨hA, hD⟩ (ipl_cons ⟨hB, hD⟩ hΔ)) hC)
  | @impLImp _ _ Δ A B D _ h _ _ ih₁ ih₂ =>
      intro hΓ hC
      obtain ⟨⟨⟨hA, hB⟩, hD⟩, hΔ⟩ := ipl_perm hΓ h
      exact .impLImp h (ih₁ (ipl_cons ⟨hB, hD⟩ hΔ) ⟨hA, hB⟩)
        (ih₂ (ipl_cons hD hΔ) hC)
  -- `R◯→`: the principal `◯A ⊃ B` is in the context
  | @impLLax _ _ _ _ _ _ h _ _ _ _ =>
      intro hΓ _; have hbox := (ipl_perm hΓ h).1; simp at hbox
  -- `L◯→`: likewise
  | @impLLaxLax _ _ _ _ _ _ _ h _ _ _ _ _ =>
      intro hΓ _; have hbox := (ipl_perm hΓ h).1; simp at hbox

end G4h

namespace G4c

/-- The same statement at the working judgment `G4c = ∃ n, G4h n`. -/
theorem toG4_isIPL {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4c Γ C) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) : G4 Γ C :=
  let ⟨_, hn⟩ := d; hn.toG4_isIPL hΓ hC

end G4c

namespace G4

/-! ## Completeness of the G4ip base -/

/-- **Completeness of the `◯`-free base of G4iLL** (Dyckhoff's G4ip) for
the cut-free G3 calculus (G3ip on this fragment):

    (∀ ψ ∈ Γ, isIPL ψ) → isIPL C → SC Γ C → G4 Γ C

Contrast `PLLG4Gap.sc_but_not_G4`, which refutes the same implication
without the `◯`-freeness hypotheses. -/
theorem completeness_isIPL {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) (d : SC Γ C) : G4 Γ C :=
  (G4c.completeness d).toG4_isIPL hΓ hC

/-- **G4ip = G3ip.**  On `◯`-free sequents Iemhoff's calculus and the
cut-free G3 calculus agree — the equivalence claimed in general by
Theorem 1 of arXiv:2011.11847, here restricted to the fragment where it
survives.  (`←` is `completeness_isIPL`; `→` is `G4.toSC`, which needs no
hypotheses.) -/
theorem iff_SC_isIPL {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) : G4 Γ C ↔ SC Γ C :=
  ⟨toSC, completeness_isIPL hΓ hC⟩

/-- **The repair is invisible on the `◯`-free fragment**: `G4iLL` and the
repaired `G4iLL″` derive the same `◯`-free sequents.  (`→` is the
unrestricted embedding `G4c.ofG4p ∘ G4p.ofG4`; `←` is `toG4_isIPL`.)
This is the precise sense in which `PLLG4H.lean`'s revisions 1–3 are
purely modal. -/
theorem iff_G4c_isIPL {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) : G4 Γ C ↔ G4c Γ C :=
  ⟨fun d => G4c.ofG4p (G4p.ofG4 d), fun d => d.toG4_isIPL hΓ hC⟩

/-- **The `◯`-free fragment of G4iLL is complete for IPC**: every
intuitionistic natural-deduction derivation of a `◯`-free sequent is
matched by a `G4` derivation.  Composes `IPLND.toLax`
(`PLLNoFallNF.lean`), `cutElimination` (`PLLSequent.lean`) and
`completeness_isIPL`. -/
theorem of_IPLND {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) (d : IPLND Γ C) : G4 Γ C :=
  completeness_isIPL hΓ hC (cutElimination.mp d.toLax)

/-- **… and sound for IPC**: `G4.toSC` into G3iLL, cut elimination into
`LaxND`, then `conservativity_IPL` (`PLLNDCore.lean`) back to IPC. -/
theorem toIPLND {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) (d : G4 Γ C) : IPLND Γ C := by
  obtain ⟨p⟩ := cutElimination.mpr d.toSC
  exact conservativity_IPL hC hΓ p

/-- **The `◯`-free fragment of G4iLL is exactly IPC.** -/
theorem iff_IPLND {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hC : isIPL C) : G4 Γ C ↔ IPLND Γ C :=
  ⟨toIPLND hΓ hC, of_IPLND hΓ hC⟩

/-- **Contraction is admissible on the `◯`-free fragment.**  Directly
opposite to `PLLG4Gap.contraction_not_admissible`, which exhibits a
sequent with a `◯` where contraction fails in `G4`.  Proof: out to `SC`,
where contraction is `SC.rename`, and back by `completeness_isIPL`. -/
theorem contract_isIPL {Γ : List PLLFormula} {A C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, isIPL ψ) (hA : isIPL A) (hC : isIPL C)
    (d : G4 (A :: A :: Γ) C) : G4 (A :: Γ) C := by
  refine completeness_isIPL (ipl_cons hA hΓ) hC (d.toSC.rename ?_)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact .head _
  · exact hψ

/-! ## The packaging: the gap is modal -/

/-- **The incompleteness of G4iLL is created by its `◯` rules.**  Both
halves in one statement:

* on `◯`-free sequents the calculus is complete for the cut-free G3
  calculus — every propositional rule of Iemhoff's calculus is
  Dyckhoff's, and the argument never leaves the fragment;
* with `◯` present it is not: `◯G', F' ⇒ r` is `SC`-derivable and
  `G4`-underivable (`PLLG4Gap.sc_but_not_G4`), and the sequent's
  underivability turns precisely on `L◯→` consuming its implication.

So no repair of the propositional base can close the gap, and none is
needed: the repair `G4c` of `PLLG4H.lean` changes only the modal
rules. -/
theorem base_complete_gap_modal :
    (∀ {Γ : List PLLFormula} {C : PLLFormula},
      (∀ ψ ∈ Γ, isIPL ψ) → isIPL C → SC Γ C → G4 Γ C) ∧
    (∃ Γ : List PLLFormula, ∃ C : PLLFormula, SC Γ C ∧ ¬ G4 Γ C) :=
  ⟨fun hΓ hC d => completeness_isIPL hΓ hC d,
    ⟨[PLLG4Gap.Ga.somehow, PLLG4Gap.Fa], prop "r", PLLG4Gap.sc_but_not_G4⟩⟩

/-! ### Sanity checks: the fragment is not trivial

Peirce's law is `◯`-free and G4-underivable, so `completeness_isIPL`
does not prove everything on the fragment.  (Compiled evaluation, a
control only — the load-bearing underivability of this development,
`PLLG4Gap.sep_not_G4`, is kernel-checked.) -/

/-- info: false -/
#guard_msgs in
#eval decide (G4 []
  ((((prop "p").ifThen (prop "q")).ifThen (prop "p")).ifThen (prop "p")))

/-- A `◯`-free sequent obtained *through* the new chain, from an IPC
natural-deduction derivation: `p ⊢ p ∨ q`. -/
example : G4 [prop "p"] ((prop "p").or (prop "q")) :=
  of_IPLND (by simp) (by simp) (.orIntro1 (.iden (.head _)))

/-! ## Axiom audits -/

/-- info: 'PLLND.G4h.toG4_isIPL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms G4h.toG4_isIPL

/-- info: 'PLLND.G4.completeness_isIPL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms completeness_isIPL

/-- info: 'PLLND.G4.iff_SC_isIPL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms iff_SC_isIPL

-- The `G4 ↔ G4c` equivalence on the fragment does *not* go through cut
-- elimination, so it stays at `[propext]` — the same trust base as the
-- gap's `sep_not_G4`.
/-- info: 'PLLND.G4.iff_G4c_isIPL' depends on axioms: [propext] -/
#guard_msgs in
#print axioms iff_G4c_isIPL

/-- info: 'PLLND.G4.iff_IPLND' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms iff_IPLND

/-- info: 'PLLND.G4.contract_isIPL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms contract_isIPL

/-- info: 'PLLND.G4.base_complete_gap_modal' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms base_complete_gap_modal

end G4

end PLLND
