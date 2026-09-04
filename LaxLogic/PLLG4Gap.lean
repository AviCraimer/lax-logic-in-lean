import LaxLogic.PLLDecide

/-!
# G4iLL is incomplete: a machine-checked separation from G3iLL

Iemhoff's calculus G4iLL (*Proof Theory for Lax Logic*, arXiv:2209.08976,
Fig. 2.3 — our `G4`) was claimed equivalent to G3iLL (our `SC`) via the
general Theorem 1 of *The G4i analogue of a G3i calculus*
(arXiv:2011.11847).  This file refutes the equivalence, with both sides
machine-checked:

* `SC [◯G', F'] r` is derived below, where `F' = ◯p → r` and
  `G' = F' → ◯p`;
* `decide (G4 [◯G', F'] r) = false` by the *verified* decision procedure
  of `PLLDecide` (whose completeness over the `G4` rules is a theorem).

The sequent is PLL-valid: bind on `◯G'` — inside the box, `G'` and the
(reused!) hypothesis `F'` give `◯p` — so `◯p` holds outright, and `F'`
then yields `r`.  The G3 derivation below uses `F'` **twice**: once
inside the `laxL` box-opening, once as the final implication.  G4iLL's
`L◯→` (`impLLaxLax`) reuses the *box* across its premises but *consumes
the implication*, and its first premise `G' ⇒ ◯p` is invalid — so no G4
rule instance closes the sequent.  This is Howe's duplication phenomenon
(MSCS 2001) one level up: the formula needing contraction is the
`◯`-antecedent implication itself, straddling a box-opening.

Consequently the modal case of Theorem 1 of arXiv:2011.11847 fails as
stated (its premises `Sᵢ` carry an extra copy of `◯φ→ψ`, so `Sᵢ ≪ S`
does not hold, and the copy cannot be dropped), and Corollary 1 of
arXiv:2209.08976 with it.  A `⊥`-instantiated variant is included to
show even the constant-only fragment separates.  The decidability
development of `PLLDecide` is untouched — it decides `G4` — but a
repaired calculus is needed before it decides PLL.
-/

open PLLFormula PLLND

namespace PLLG4Gap

/-- `F' := ◯p ⊃ r`. -/
def Fa : PLLFormula := ((prop "p").somehow).ifThen (prop "r")

/-- `G' := F' ⊃ ◯p = (◯p ⊃ r) ⊃ ◯p`. -/
def Ga : PLLFormula := Fa.ifThen (prop "p").somehow

-- Control: `◯G', F' ⇒ ◯p` is G4-derivable (the boxed detour exists).
/-- info: true -/
#guard_msgs in
#eval decide (G4 [Ga.somehow, Fa] ((prop "p").somehow))

-- **The separation**: `◯G', F' ⇒ r` is *not* G4-derivable.
/-- info: false -/
#guard_msgs in
#eval decide (G4 [Ga.somehow, Fa] (prop "r"))

/-- … but it *is* derivable in the G3 calculus `SC`, reusing `F'` on
both sides of the box-opening. -/
theorem sep_SC : SC [Ga.somehow, Fa] (prop "r") := by
  -- impL on F' : premises ◯G', F' ⇒ ◯p and r, ◯G', F' ⇒ r
  refine SC.impL (A := (prop "p").somehow) (.tail _ (.head _)) ?_ ?_
  · -- ◯G', F' ⇒ ◯p : open the box, then impL on G'
    refine SC.laxL (A := Ga) (.head _) ?_
    refine SC.impL (A := Fa) (.head _) ?_ ?_
    · -- G', ◯G', F' ⇒ F' : the second use of F'
      refine SC.impR ?_
      refine SC.impL (A := (prop "p").somehow)
        (.tail _ (.tail _ (.tail _ (.head _)))) ?_ ?_
      · exact SC.iden _ (.head _)
      · exact SC.iden _ (.head _)
    · exact SC.iden _ (.head _)
  · exact SC.iden _ (.head _)

/-! ## The `⊥`-only variant: `F = ◯⊥ ⊃ ⊥`, `G = F ⊃ ◯⊥` -/

/-- `F := ◯⊥ ⊃ ⊥` (i.e. `¬◯⊥`). -/
def Fm : PLLFormula := (falsePLL.somehow).ifThen falsePLL

/-- `G := F ⊃ ◯⊥`. -/
def Gm : PLLFormula := Fm.ifThen falsePLL.somehow

/-- info: true -/
#guard_msgs in
#eval decide (G4 [Gm.somehow, Fm] falsePLL.somehow)

/-- info: false -/
#guard_msgs in
#eval decide (G4 [Gm.somehow, Fm] (prop "q"))

/-- `◯G, F` is PLL-inconsistent, and `SC` sees it. -/
example : SC [Gm.somehow, Fm] (prop "q") := by
  refine SC.impL (A := falsePLL.somehow) (.tail _ (.head _)) ?_ ?_
  · refine SC.laxL (A := Gm) (.head _) ?_
    refine SC.impL (A := Fm) (.head _) ?_ ?_
    · refine SC.impR ?_
      refine SC.impL (A := falsePLL.somehow)
        (.tail _ (.tail _ (.tail _ (.head _)))) ?_ ?_
      · exact SC.iden _ (.head _)
      · exact SC.botL (.head _)
    · exact SC.iden _ (.head _)
  · exact SC.botL (.head _)

/-! ## Contraction is not admissible in G4iLL

With **two** copies of `F'` the separation sequent *is* derivable: one
copy is consumed by `impLLaxLax` (box `◯G'`), whose first premise
`G', F' ⇒ ◯p` spends the second copy inside the box-opening (via
`impLImp` on `G'` and `impLLaxLax` again, box `◯p`).  Together with the
`false` verdict on the single-copy sequent above, this machine-checks
that the contraction rule is **not** admissible in G4iLL — the very
hypothesis the referee-patched Theorem 3.4 of Studia Logica 110 (2022)
added, and the substance of Howe's conjecture (MSCS 2001, §5), whose
example this is (in packaged form). -/

/-- info: true -/
#guard_msgs in
#eval decide (G4 [Ga.somehow, Fa, Fa] (prop "r"))

/-! ## Kernel-checked underivability

The `decide` verdicts above run the verified search as *compiled* code;
here the headline verdict `¬ G4 [◯G′, F′] r` is re-established as an
ordinary proof term, checked by the kernel alone.  The refutation tree
mirrors the `succs` exhaustion: the endsequent's only two applicable
rule instances are `impLLax` on `F′` (premise 1: `◯G′ ⇒ p`, refuted as
`not_S1`) and `impLLaxLax` on `F′` with box `◯G′` (premise 1:
`G′ ⇒ ◯p`, refuted as `not_S2` via `laxR`/`impLImp`, descending through
`⇒ F′` to the modus-ponens residue `◯p, r→◯p ⇒ r`, where `Lp→` finally
demands a second occurrence of `r` that is not there).  All `Perm`
hypotheses are dismantled with `subset`/`cons_inv` only; the reducible
abbreviations keep every formula constructor-visible to `cases`. -/

section Kernel

private abbrev p₀ : PLLFormula := prop "p"
private abbrev r₀ : PLLFormula := prop "r"
/-- `F′ = ◯p → r`, reducibly. -/
private abbrev F' : PLLFormula := p₀.somehow.ifThen r₀
/-- `G′ = F′ → ◯p`, reducibly. -/
private abbrev G' : PLLFormula := F'.ifThen p₀.somehow

/-- `◯p, r→◯p ⇒ r`: the modus-ponens residue is underivable — `Lp→`
on `r→◯p` needs `r` in the remaining context, and it is not there. -/
private theorem not_S5 : ¬ G4 [p₀.somehow, r₀.ifThen p₀.somehow] r₀ := by
  intro d
  cases d with
  | init h => simp at h
  | botL h => simp at h
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | @impLProp _ Δ a B _ h ha _ =>
      cases h.symm.subset (List.Mem.head _) with
      | tail _ hm =>
        cases hm with
        | head =>
            -- principal is r→◯p, so Δ ~ [◯p]; but Lp→ needs r ∈ Δ
            have hΔ : Δ.Perm [p₀.somehow] :=
              (((List.Perm.swap _ _ _).symm.trans h).cons_inv).symm
            have hr := hΔ.subset ha
            simp at hr
        | tail _ hm => exact nomatch hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLImp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLaxLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm

/-- `r→◯p ⇒ F′` is underivable: `impR` leads to `not_S5`, and `Lp→`
would need an `r` that is not there. -/
private theorem not_S4 : ¬ G4 [r₀.ifThen p₀.somehow] F' := by
  intro d
  cases d with
  | botL h => simp at h
  | impR d₁ => exact not_S5 d₁
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | @impLProp _ Δ a B _ h ha _ =>
      cases h.symm.subset (List.Mem.head _) with
      | head => exact nomatch (h.cons_inv.symm.subset ha)
      | tail _ hm => exact nomatch hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLImp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLaxLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm

/-- `G′ ⇒ p` is underivable: only `impLImp` on `G′` applies, and its
first premise is `r→◯p ⇒ F′`. -/
private theorem not_S3 : ¬ G4 [G'] p₀ := by
  intro d
  cases d with
  | init h => simp at h
  | botL h => simp at h
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLProp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | @impLImp _ Δ A B D _ h d₁ _ =>
      cases h.symm.subset (List.Mem.head _) with
      | head => exact not_S4 (d₁.perm (h.cons_inv.symm.cons _))
      | tail _ hm => exact nomatch hm
  | impLLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLaxLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm

/-- `G′ ⇒ ◯p` is underivable — **the invalid premise of `L◯→`**:
`laxR` leads to `not_S3`, `impLImp` to `not_S4`. -/
private theorem not_S2 : ¬ G4 [G'] p₀.somehow := by
  intro d
  cases d with
  | botL h => simp at h
  | laxR d₁ => exact not_S3 d₁
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | laxL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLProp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | @impLImp _ Δ A B D _ h d₁ _ =>
      cases h.symm.subset (List.Mem.head _) with
      | head => exact not_S4 (d₁.perm (h.cons_inv.symm.cons _))
      | tail _ hm => exact nomatch hm
  | impLLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLaxLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm

/-- `◯G′ ⇒ p` is underivable — **the invalid premise of `R◯→`**:
nothing engages a boxed hypothesis towards an atomic goal. -/
private theorem not_S1 : ¬ G4 [G'.somehow] p₀ := by
  intro d
  cases d with
  | init h => simp at h
  | botL h => simp at h
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLProp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLImp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLLaxLax h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm

/-- The root: `◯G′, F′ ⇒ r` is underivable.  The only two live rule
instances are `impLLax` on `F′` (→ `not_S1`) and `impLLaxLax` on `F′`
with box `◯G′` (→ `not_S2`). -/
private theorem not_S0 : ¬ G4 [G'.somehow, F'] r₀ := by
  intro d
  cases d with
  | init h => simp at h
  | botL h => simp at h
  | andL h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | orL h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLProp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLBot h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLAnd h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLOr h _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | impLImp h _ _ =>
      have hm := h.symm.subset (List.Mem.head _); simp at hm
  | @impLLax _ Δ A B _ h d₁ _ =>
      cases h.symm.subset (List.Mem.head _) with
      | tail _ hm =>
        cases hm with
        | head =>
            -- principal is F′, so Δ ~ [◯G′]; premise 1 is ◯G′ ⇒ p
            have hΔ : [G'.somehow].Perm Δ :=
              ((List.Perm.swap _ _ _).symm.trans h).cons_inv
            exact not_S1 (d₁.perm hΔ.symm)
        | tail _ hm => exact nomatch hm
  | @impLLaxLax _ Δ A B X _ h d₁ _ =>
      cases h.symm.subset (List.Mem.head _) with
      | tail _ hm =>
        cases hm with
        | head =>
            -- implication is F′; the box must then be ◯G′, Δ ~ []
            have h₂ : [G'.somehow].Perm (X.somehow :: Δ) :=
              ((List.Perm.swap _ _ _).symm.trans h).cons_inv
            cases h₂.symm.subset (List.Mem.head _) with
            | head =>
                -- premise 1 is G′ ⇒ ◯p
                exact not_S2 (d₁.perm (h₂.cons_inv.symm.cons _))
            | tail _ hm => exact nomatch hm
        | tail _ hm => exact nomatch hm

end Kernel

/-- **Kernel-checked** underivability of the separating sequent: the
same verdict as the `decide … = false` guard above, but established by
an explicit proof term — no compiled evaluation in the trusted base. -/
theorem sep_not_G4 : ¬ G4 [Ga.somehow, Fa] (prop "r") := not_S0

/-- The separation, packaged: G3iLL derives what G4iLL provably cannot.
Left component kernel-checked in §above; right component kernel-checked
by `sep_not_G4`. -/
theorem sc_but_not_G4 :
    SC [Ga.somehow, Fa] (prop "r") ∧ ¬ G4 [Ga.somehow, Fa] (prop "r") :=
  ⟨sep_SC, sep_not_G4⟩

/-! ## The failures of contraction and cut, as explicit derivations

The positive halves are plain proof terms, so the structural-rule
failures need no decision procedure at all. -/

/-- `G′, F′ ⊢ ◯p`: inside the box-opening, `G′` and a copy of `F′`
produce `◯p` (this is the sequent whose `F′`-free version `G′ ⊢ ◯p`
is refuted by `not_S2`). -/
private theorem GF_proves_boxp : G4 [G', F'] p₀.somehow :=
  .impLImp (List.Perm.refl _)
    (-- r→◯p, F′ ⊢ F′ : the copy of F′ fires under `impR`
      .impR
        (.impLLaxLax
          (List.perm_middle (l₁ := [p₀.somehow, r₀.ifThen p₀.somehow]))
          (.laxR (.init (.head _)))
          (.init (.head _))))
    (-- ◯p, F′ ⊢ ◯p
      .laxL (List.Perm.refl _) (.laxR (.init (.head _))))

/-- **Two copies of `F′` suffice**: the explicit derivation, one copy
consumed by `impLLaxLax` outside the box-opening, the other inside it
(within `GF_proves_boxp`). -/
theorem two_copies_G4 : G4 [Ga.somehow, Fa, Fa] (prop "r") :=
  .impLLaxLax (List.Perm.swap _ _ _)
    GF_proves_boxp
    (.init (.head _))

/-- **Contraction is not admissible in G4iLL**: derivable with two
copies of `F′`, underivable with one — both directions kernel-checked. -/
theorem contraction_not_admissible :
    G4 [Ga.somehow, Fa, Fa] (prop "r") ∧ ¬ G4 [Ga.somehow, Fa] (prop "r") :=
  ⟨two_copies_G4, sep_not_G4⟩

/-- `◯G′, F′ ⊢ ◯p`: the left premise of the failing cut. -/
theorem cut_left_G4 : G4 [Ga.somehow, Fa] ((prop "p").somehow) :=
  .laxL (List.Perm.refl _) GF_proves_boxp

/-- `◯p, ◯G′, F′ ⊢ r`: the right premise of the failing cut — with
`◯p` supplied as a hypothesis, `impLLaxLax` can use it as the box. -/
theorem cut_right_G4 :
    G4 [(prop "p").somehow, Ga.somehow, Fa] (prop "r") :=
  .impLLaxLax (List.perm_middle (l₁ := [p₀.somehow, G'.somehow]))
    (.laxR (.init (.head _)))
    (.init (.head _))

/-- **Cut is not admissible in G4iLL** either: `◯p` interpolates
between `◯G′, F′` and `r`, but the cut cannot be eliminated. -/
theorem cut_not_admissible :
    G4 [Ga.somehow, Fa] ((prop "p").somehow) ∧
    G4 [(prop "p").somehow, Ga.somehow, Fa] (prop "r") ∧
    ¬ G4 [Ga.somehow, Fa] (prop "r") :=
  ⟨cut_left_G4, cut_right_G4, sep_not_G4⟩

/-! Axiom audit, pinned at build time: the underivability needs
`propext` only — no choice, no quotients, and in particular no
`Lean.ofReduceBool` (i.e. no trusted compiled evaluation). -/

/-- info: 'PLLG4Gap.sep_not_G4' depends on axioms: [propext] -/
#guard_msgs in
#print axioms sep_not_G4

/-- info: 'PLLG4Gap.two_copies_G4' does not depend on any axioms -/
#guard_msgs in
#print axioms two_copies_G4

/-- info: 'PLLG4Gap.contraction_not_admissible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms contraction_not_admissible

/-- info: 'PLLG4Gap.cut_not_admissible' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cut_not_admissible

/-- info: 'PLLG4Gap.sc_but_not_G4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms sc_but_not_G4

end PLLG4Gap
