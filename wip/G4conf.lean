import LaxLogic.PLLConfluentComplete
import LaxLogic.PLLG4H

/-!
# G4cf — a cut-free sequent calculus for CONFLUENT PLL

Branch `ui-confluence`.  Design in `docs/confluent-ui-plan.md`.

`G4cf` = the repaired complete calculus `G4c` (`PLLG4H.lean`, the
height-indexed `G4h`) PLUS one additive left rule `distL` for the
distribution scheme `◯(A∨B) ⊃ (◯A∨◯B)`, which is sound and complete for
mutually confluent constraint models (`PLLFrames.lean:224`,
`PLLConfluentComplete.lean`).  On such models the ∀∃-clause for ◯
collapses to bare possibility `w ⊩ ◯φ ↔ ∃u, Rₘ w u ∧ u ⊩ φ`.

The 17 `G4h` rules are copied verbatim (a `G4h → G4hf` rename); `distL`
is the one new rule.  Every ported metatheorem gets exactly one new case.

Proved here: `force_dist_elim` (the semantic core of `distL`-soundness)
and full soundness via `DerivU`.  The heavier metatheory that was
assumed under licence — completeness without cut, and cut
admissibility — is REFUTED (2026-07-28): see the adjudication block
before the (removed) statements, and `wip/g4confGap.lean`.
-/

open PLLFormula

namespace PLLND
namespace G4Conf

/-- **G4cf, height-indexed.**  The 17 rules of `G4h` (`PLLG4H.lean:49`)
verbatim, plus `distL`.  Premises at `n`, conclusion at `n+1`. -/
inductive G4hf : Nat → List PLLFormula → PLLFormula → Prop
  | init {n : Nat} {Γ : List PLLFormula} {a : String}
      (h : prop a ∈ Γ) : G4hf n Γ (prop a)
  | botL {n : Nat} {Γ : List PLLFormula} {C : PLLFormula}
      (h : falsePLL ∈ Γ) : G4hf n Γ C
  | andR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ A → G4hf n Γ B → G4hf (n + 1) Γ (A.and B)
  | orR1 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ A → G4hf (n + 1) Γ (A.or B)
  | orR2 {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n Γ B → G4hf (n + 1) Γ (A.or B)
  | impR {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula} :
      G4hf n (A :: Γ) B → G4hf (n + 1) Γ (A.ifThen B)
  | laxR {n : Nat} {Γ : List PLLFormula} {A : PLLFormula} :
      G4hf n Γ A → G4hf (n + 1) Γ A.somehow
  | andL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.and B :: Δ)) :
      G4hf n (A :: B :: Δ) C → G4hf (n + 1) Γ C
  | orL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.or B :: Δ)) :
      G4hf n (A :: Δ) C → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | laxL {n : Nat} {Γ : List PLLFormula} {A B : PLLFormula}
      (h : A.somehow ∈ Γ) :
      G4hf n (A :: Γ) B.somehow → G4hf (n + 1) Γ B.somehow
  | impLProp {n : Nat} {Γ Δ : List PLLFormula} {a : String} {B C : PLLFormula}
      (h : Γ.Perm ((prop a).ifThen B :: Δ)) (ha : prop a ∈ Δ) :
      G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | impLBot {n : Nat} {Γ Δ : List PLLFormula} {B C : PLLFormula}
      (h : Γ.Perm (falsePLL.ifThen B :: Δ)) :
      G4hf n Δ C → G4hf (n + 1) Γ C
  | impLAnd {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.and B).ifThen D :: Δ)) :
      G4hf n (A.ifThen (B.ifThen D) :: Δ) E → G4hf (n + 1) Γ E
  | impLOr {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.or B).ifThen D :: Δ)) :
      G4hf n (A.ifThen D :: B.ifThen D :: Δ) E → G4hf (n + 1) Γ E
  | impLImp {n : Nat} {Γ Δ : List PLLFormula} {A B D E : PLLFormula}
      (h : Γ.Perm ((A.ifThen B).ifThen D :: Δ)) :
      G4hf n (B.ifThen D :: Δ) (A.ifThen B) → G4hf n (D :: Δ) E →
      G4hf (n + 1) Γ E
  | impLLax {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) :
      G4hf n Γ A → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  | impLLaxLax {n : Nat} {Γ Δ : List PLLFormula} {A B X C : PLLFormula}
      (h : Γ.Perm (A.somehow.ifThen B :: Δ)) (hX : X.somehow ∈ Δ) :
      G4hf n (X :: Γ) A.somehow → G4hf n (B :: Δ) C → G4hf (n + 1) Γ C
  -- the one new rule: ◯∨-distribution as an analytic left rule
  | distL {n : Nat} {Γ Δ : List PLLFormula} {A B C : PLLFormula}
      (h : Γ.Perm ((A.or B).somehow :: Δ)) :
      G4hf n (A.somehow :: Δ) C → G4hf n (B.somehow :: Δ) C →
      G4hf (n + 1) Γ C

/-- The working judgment: derivable in confluent PLL at some height. -/
def G4cf (Γ : List PLLFormula) (C : PLLFormula) : Prop := ∃ n, G4hf n Γ C

/-! ## The semantic core of `distL`-soundness (PROVED)

On mutually confluent models `◯(A∨B)` gives `◯A ∨ ◯B` — the exact fact
the new rule needs, a two-line corollary of the already-proven
`force_somehow_or_dist_of_confluent` (`PLLFrames.lean:240`). -/

theorem force_dist_elim {M : ConstraintModel} (hc : MutuallyConfluent M)
    {w : M.W} {A B : PLLFormula} (h : M.force w (somehow (A.or B))) :
    M.force w (somehow A) ∨ M.force w (somehow B) := by
  have hd := force_somehow_or_dist_of_confluent hc w A B
  have hor := hd w (M.refl_i w) h
  simpa [ConstraintModel.force] using hor

/-! ## Formal soundness, via `G4cf → DerivU → confluent-valid`.

Only `distL` is genuinely new; the 17 shared rules are the ordinary
`G4 → ND` translation.  Built interactively, one case at a time. -/

open ConfluentU

/-- Lift a closed `LaxND` theorem into `DerivU` over any context. -/
private theorem thmU {φ : PLLFormula} (p : LaxND [] φ)
    {Γ : List PLLFormula} : DerivU Γ φ :=
  DerivU.rename (fun _ h => by simp at h) (DerivU.of_nd p)

private theorem cutU {Γ : List PLLFormula} {A C : PLLFormula}
    (h₁ : DerivU Γ A) (h₂ : DerivU (A :: Γ) C) : DerivU Γ C :=
  DerivU.mp (DerivU.deduction h₂) h₁

private theorem falsoU {Γ : List PLLFormula} {C : PLLFormula}
    (h : DerivU Γ falsePLL) : DerivU Γ C :=
  DerivU.mp (thmU (φ := falsePLL.ifThen C)
    (.impIntro (.falsoElim C (.iden (by simp))))) h

private theorem andIU {Γ : List PLLFormula} {A B : PLLFormula}
    (h₁ : DerivU Γ A) (h₂ : DerivU Γ B) : DerivU Γ (A.and B) :=
  DerivU.mp (DerivU.mp (thmU (φ := A.ifThen (B.ifThen (A.and B)))
    (.impIntro (.impIntro (.andIntro (.iden (by simp)) (.iden (by simp)))))) h₁) h₂

private theorem andE1U {Γ : List PLLFormula} {A B : PLLFormula}
    (h : DerivU Γ (A.and B)) : DerivU Γ A :=
  DerivU.mp (thmU (φ := (A.and B).ifThen A)
    (.impIntro (.andElim1 (ψ := B) (.iden (by simp))))) h

private theorem andE2U {Γ : List PLLFormula} {A B : PLLFormula}
    (h : DerivU Γ (A.and B)) : DerivU Γ B :=
  DerivU.mp (thmU (φ := (A.and B).ifThen B)
    (.impIntro (.andElim2 (φ := A) (.iden (by simp))))) h

private theorem orI1U {Γ : List PLLFormula} {A B : PLLFormula}
    (h : DerivU Γ A) : DerivU Γ (A.or B) :=
  DerivU.mp (thmU (φ := A.ifThen (A.or B))
    (.impIntro (.orIntro1 (.iden (by simp))))) h

private theorem orI2U {Γ : List PLLFormula} {A B : PLLFormula}
    (h : DerivU Γ B) : DerivU Γ (A.or B) :=
  DerivU.mp (thmU (φ := B.ifThen (A.or B))
    (.impIntro (.orIntro2 (.iden (by simp))))) h

private theorem orEU {Γ : List PLLFormula} {A B C : PLLFormula}
    (h₀ : DerivU Γ (A.or B)) (h₁ : DerivU (A :: Γ) C) (h₂ : DerivU (B :: Γ) C) :
    DerivU Γ C :=
  DerivU.mp (DerivU.mp (DerivU.mp
    (thmU (φ := (A.or B).ifThen ((A.ifThen C).ifThen ((B.ifThen C).ifThen C)))
      (.impIntro (.impIntro (.impIntro
      (.orElim (φ := A) (ψ := B) (.iden (by simp))
        (.impElim (φ := A) (.iden (by simp)) (.iden (by simp)))
        (.impElim (φ := B) (.iden (by simp)) (.iden (by simp))))))))
    h₀) (DerivU.deduction h₁)) (DerivU.deduction h₂)

private theorem bindU {Γ : List PLLFormula} {A B : PLLFormula}
    (h₀ : DerivU Γ (somehow A)) (h₁ : DerivU (A :: Γ) (somehow B)) :
    DerivU Γ (somehow B) :=
  DerivU.mp (DerivU.mp
    (thmU (φ := (somehow A).ifThen ((A.ifThen (somehow B)).ifThen (somehow B)))
      (.impIntro (.impIntro
      (.laxElim (φ := A) (.iden (by simp)) (.impElim (φ := A) (.iden (by simp)) (.iden (by simp)))))))
    h₀) (DerivU.deduction h₁)

/-- Membership transported across a `Perm`-with-principal into `Γ`. -/
private theorem permMem {Γ Δ : List PLLFormula} {p ψ : PLLFormula}
    (h : Γ.Perm (p :: Δ)) (hψ : ψ ∈ p :: Δ) : ψ ∈ Γ :=
  h.symm.subset hψ

/-- **G4cf → DerivU** (the translation; only `distL` is new). -/
theorem G4cf_to_DerivU {n : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4hf n Γ C) : DerivU Γ C := by
  induction d with
  | init h => exact DerivU.hyp h
  | botL h => exact falsoU (DerivU.hyp h)
  | andR _ _ ih₁ ih₂ => exact andIU ih₁ ih₂
  | orR1 _ ih => exact orI1U ih
  | orR2 _ ih => exact orI2U ih
  | impR _ ih => exact DerivU.deduction ih
  | laxR _ ih => exact DerivU.unit ih
  | andL h _ ih =>
      have hAB := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      exact DerivU.mp (DerivU.mp
        (DerivU.rename (fun ψ hψ => permMem h (List.mem_cons_of_mem _ hψ))
          (DerivU.deduction (DerivU.deduction ih)))
        (andE2U hAB)) (andE1U hAB)
  | orL h _ _ ih₁ ih₂ =>
      exact orEU (DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl))))
        (DerivU.rename (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons.mpr (.inl rfl)
          · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₁)
        (DerivU.rename (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons.mpr (.inl rfl)
          · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₂)
  | laxL h _ ih => exact bindU (DerivU.hyp h) ih
  | impLProp h ha _ ih =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      have hA := DerivU.hyp (permMem h (List.mem_cons_of_mem _ ha))
      exact cutU (DerivU.mp hImp hA) (DerivU.rename (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons.mpr (.inl rfl)
        · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih)
  | impLBot h _ ih =>
      exact DerivU.rename (fun ψ hψ => permMem h (List.mem_cons_of_mem _ hψ)) ih
  | impLAnd h _ ih =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      exact cutU
        (DerivU.deduction (DerivU.deduction
          (DerivU.mp
            (DerivU.rename (fun ψ hψ =>
              List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ)) hImp)
            (andIU (DerivU.hyp (List.mem_cons_of_mem _ (List.mem_cons.mpr (.inl rfl))))
                   (DerivU.hyp (List.mem_cons.mpr (.inl rfl)))))))
        (DerivU.rename (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons.mpr (.inl rfl)
          · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih)
  | impLOr h _ ih =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      have hAD := DerivU.deduction (DerivU.mp
        (DerivU.rename (fun ψ hψ => List.mem_cons_of_mem _ hψ) hImp)
        (orI1U (DerivU.hyp (List.mem_cons.mpr (.inl rfl)))))
      have hBD := DerivU.deduction (DerivU.mp
        (DerivU.rename (fun ψ hψ => List.mem_cons_of_mem _ hψ) hImp)
        (orI2U (DerivU.hyp (List.mem_cons.mpr (.inl rfl)))))
      exact DerivU.mp (DerivU.mp
        (DerivU.rename (fun ψ hψ => permMem h (List.mem_cons_of_mem _ hψ))
          (DerivU.deduction (DerivU.deduction ih)))
        hBD) hAD
  | impLImp h _ _ ih₁ ih₂ =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      have hBD := DerivU.deduction (DerivU.mp
        (DerivU.rename (fun ψ hψ => List.mem_cons_of_mem _ hψ) hImp)
        (DerivU.deduction (DerivU.hyp
          (List.mem_cons_of_mem _ (List.mem_cons.mpr (.inl rfl))))))
      have hAB := cutU hBD (DerivU.rename (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons.mpr (.inl rfl)
        · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₁)
      exact cutU (DerivU.mp hImp hAB) (DerivU.rename (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons.mpr (.inl rfl)
        · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₂)
  | impLLax h _ _ ih₁ ih₂ =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      exact cutU (DerivU.mp hImp (DerivU.unit ih₁)) (DerivU.rename (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons.mpr (.inl rfl)
        · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₂)
  | impLLaxLax h hX _ _ ih₁ ih₂ =>
      have hImp := DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))
      have hOA := bindU (DerivU.hyp (permMem h (List.mem_cons_of_mem _ hX))) ih₁
      exact cutU (DerivU.mp hImp hOA) (DerivU.rename (fun ψ hψ => by
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons.mpr (.inl rfl)
        · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₂)
  | distL h _ _ ih₁ ih₂ =>
      exact orEU
        (DerivU.mp (DerivU.dist _ _)
          (DerivU.hyp (permMem h (List.mem_cons.mpr (.inl rfl)))))
        (DerivU.rename (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons.mpr (.inl rfl)
          · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₁)
        (DerivU.rename (fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact List.mem_cons.mpr (.inl rfl)
          · exact List.mem_cons_of_mem _ (permMem h (List.mem_cons_of_mem _ hψ))) ih₂)

/-- **Soundness of G4cf for mutually confluent models** (FORMAL). -/
theorem G4cf_sound {Γ : List PLLFormula} {C : PLLFormula} (d : G4cf Γ C)
    {M : ConstraintModel} (hc : MutuallyConfluent M) {w : M.W}
    (hΓ : ∀ φ ∈ Γ, M.force w φ) : M.force w C := by
  obtain ⟨n, d⟩ := d
  exact derivU_iff_confluent_valid.mp (G4cf_to_DerivU d) M hc w hΓ

/-- **`G4cf` extends `G4c`.**  Every `G4h` rule is a `G4hf` rule, so the
embedding is a 17-case rename induction (no new mathematics). -/
theorem G4cf_of_G4c {Γ : List PLLFormula} {C : PLLFormula}
    (d : G4c Γ C) : G4cf Γ C := by
  sorry

/-- **`G4cf` derives every distribution instance.**  From `◯A ⊢ ◯A∨◯B`
and `◯B ⊢ ◯A∨◯B` by `distL` — the completeness bridge to `DerivU`.
(Quick once `orR`/`init`-for-`◯` plumbing is in; stated for now.) -/
theorem G4cf_distF (A B : PLLFormula) :
    G4cf [] ((somehow (A.or B)).ifThen ((somehow A).or (somehow B))) := by
  sorry

/-! ## The assumed metatheory, ADJUDICATED (2026-07-28)

The two heavier claims that were stated here under licence —
completeness for confluent validity, and cut admissibility — are
**FALSE**, kernel-checked in `wip/g4confGap.lean`:

* `G4ConfGap.g4cf_complete_refuted` refutes the completeness claim
  outright, witnessed by the cut-necessity sequent
  `◯(a⊃(b∨c)), ◯a, ◯b⊃p, ◯c⊃p ⊢ p` — PCLL-derivable (through the cut
  formula `◯b ∨ ◯c`), confluent-valid, but not `G4cf`-derivable: no
  formula with a subformula of shape `◯(A∨B)` occurs in its backward
  cone, so `distL` never fires and `G4cf` collapses to `G4c` there
  (`G4ConfGap.g4hf_to_g4h`), and PLL refutes the sequent.
* Consequently cut admissibility fails too, granted the two routine
  true lemmas below: with cut, `G4cf` derives the sequent (compose the
  distribution instance), without it it does not.

The analytic `distL` is too weak: the confluence content can sit under
an implication inside a box, out of reach of a left rule keyed to
`◯(A∨B)`-hypotheses.  A cut-free calculus for the distributing systems
needs a `◯`-rule that carries a disjunction of `◯`-formulas across
implication eliminations (multi-succedent, or an internalised case
split) — see PROGRESS §§62, 67.  The two statements formerly here
(`G4cf_complete`, `G4cf_cut`) are removed so no proof effort can be
spent on them. -/

-- Audit: soundness is sorry-free (only the standard three axioms).
#print axioms G4cf_sound

end G4Conf
end PLLND
