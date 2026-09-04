/- Challenge: `focalization` from LaxLogic/LJFComplete.lean:437
   Ground truth exists (6-line proof); the goal here is
   to re-derive it. Group: completeness. -/
import LaxLogic.LJF
import LaxLogic.PLLSequent
import LaxLogic.PLLSemUIFrag

/-!
# Focalization completeness for `LJF`, and uniform interpolation for IPC

`LaxLogic/LJF.lean` builds a polarised focused calculus from scratch and proves
**uniform interpolation for it**: `eSound`, `aSound`, `eMinF`, `aMinF`.  That
file is deliberately self-contained — it has no bridge to the repository's
natural-deduction system, so on its own the interpolation theorem is a theorem
*about `LJF`*, not about intuitionistic propositional logic.

This file supplies the missing half: the two directions of

    Γ ⊢ φ   (natural deduction, `◯`-free)     ⟺     `LJF` derives its translation

and reads the four interpolation properties back across the bridge, giving
**uniform interpolation for IPC** stated in `Deriv` terms.

## The route

Two routes were available.  The one taken here is the cheap one:

* **soundness** (`LJF` ⟹ ND) is a direct four-judgment erasure — focus phases
  carry no information that natural deduction cannot reconstruct;
* **completeness** (ND ⟹ `LJF`) is obtained by *simulating the repository's
  cut-free sequent calculus* `PLLND.SCh` rule by rule in `LJF`, and composing
  with `PLLND.ND_to_SC` (cut elimination, F&M Theorem 2.6, already machine
  checked in `LaxLogic/PLLSequent.lean`).

The alternative — proving identity expansion and cut admissibility for `LJF`
itself, in the style of Simmons' *Structural focalization* — was rejected as
the more expensive route: **no cut whatsoever is needed on the `LJF` side**
once the simulated calculus is cut-free.  That is the whole point of
simulating a *sequent* calculus rather than natural deduction: a sequent
calculus has left rules where natural deduction has elimination rules, and a
left rule is exactly what a left focus performs.  Concretely, `SCh`'s

    A ⊃ B ∈ Γ    Γ ⇒ A    B, Γ ⇒ C
    ------------------------------  (impL)
                Γ ⇒ C

is simulated by `simHyp`: every left focus on the hypothesis `B` in the right
premise is replaced by `LFoc.impL` applied to the left premise, under the
hypothesis `A ⊃ B` that is already in the context.  Nothing is cut.

The one case that genuinely needs an argument is `orL`, where the disjunctive
hypothesis fires (`upMerge`) and hands back the *branch contexts* of the
inversion of `posOf A`, not the hypothesis `negOf A` that the premise was
proved from.  `branchIn` below closes that gap, again without cut: a branch of
`invertPos (posOf φ)` re-proves `negOf φ` by `extract`, which replays the
already-present branch of the inversion.

## Provenance

* `LJF.*` — the focused calculus and its uniform interpolant, `LaxLogic/LJF.lean`.
* `PLLND.LaxND` / `PLLND.SemUI.Deriv` — the canonical natural-deduction system
  ("PLL proves"), `LaxLogic/PLLNDCore.lean` and `LaxLogic/PLLSemUIFrag.lean`.
* `PLLND.SCh` / `PLLND.ND_to_SC` — the cut-free sequent calculus and cut
  elimination, `LaxLogic/PLLSequent.lean`.

See `docs/calculus-map.md`.
-/

namespace LJFIPC

open PLLND (LaxND SCh SC)

/-! ## Part 1: the polarisation translation

Canonical polarity: atoms, `⊥` and `∨` are positive; `⊃` and `∧` are negative.
A formula therefore has *both* a positive and a negative translation, and the
two differ only by a shift at the head:

    posOf φ = ↓(negOf φ)   when φ is `⊃`- or `∧`-headed,
    negOf φ = ↑(posOf φ)   when φ is atom-, `⊥`- or `∨`-headed.

`◯` is transparent: `posOf (◯φ) = posOf φ`.  The translation is thus total on
`PLLFormula`, and equals the translation of the `◯`-erasure.  Every theorem
below about the *round trip* is stated for `◯`-free formulas, where erasure is
the identity; the bridge theorems themselves need no such restriction. -/

mutual

/-- The positive translation. -/
def posOf : PLLFormula → LJF.Pos
  | .prop a     => .atom a
  | .falsePLL   => .fls
  | .or φ ψ     => .or (posOf φ) (posOf ψ)
  | .and φ ψ    => .down (.and (negOf φ) (negOf ψ))
  | .ifThen φ ψ => .down (.imp (posOf φ) (negOf ψ))
  | .somehow φ  => posOf φ

/-- The negative translation. -/
def negOf : PLLFormula → LJF.Neg
  | .prop a     => .up (.atom a)
  | .falsePLL   => .up .fls
  | .or φ ψ     => .up (.or (posOf φ) (posOf ψ))
  | .and φ ψ    => .and (negOf φ) (negOf ψ)
  | .ifThen φ ψ => .imp (posOf φ) (negOf ψ)
  | .somehow φ  => negOf φ

end

/-! ## The erasure back to `PLLFormula` -/

mutual

/-- Forget the polarity of a positive. -/
def unPos : LJF.Pos → PLLFormula
  | .atom a  => .prop a
  | .fls     => .falsePLL
  | .or P Q  => .or (unPos P) (unPos Q)
  | .down N  => unNeg N

/-- Forget the polarity of a negative. -/
def unNeg : LJF.Neg → PLLFormula
  | .up P    => unPos P
  | .imp Q N => .ifThen (unPos Q) (unNeg N)
  | .and M N => .and (unNeg M) (unNeg N)

end

/-! Nothing in the polarised syntax mentions `◯`, so every erasure is an IPL
formula. -/

mutual

theorem isIPL_unPos : ∀ P : LJF.Pos, PLLND.isIPL (unPos P)
  | .atom _  => trivial
  | .fls     => trivial
  | .or P Q  => ⟨isIPL_unPos P, isIPL_unPos Q⟩
  | .down N  => isIPL_unNeg N

theorem isIPL_unNeg : ∀ N : LJF.Neg, PLLND.isIPL (unNeg N)
  | .up P    => isIPL_unPos P
  | .imp Q N => ⟨isIPL_unPos Q, isIPL_unNeg N⟩
  | .and M N => ⟨isIPL_unNeg M, isIPL_unNeg N⟩

end

/-- **The round trip.**  Translating and erasing is `◯`-erasure. -/
theorem un_round : ∀ φ : PLLFormula,
    unPos (posOf φ) = PLLND.erase φ ∧ unNeg (negOf φ) = PLLND.erase φ := by
  intro φ
  induction φ with
  | prop a => exact ⟨rfl, rfl⟩
  | falsePLL => exact ⟨rfl, rfl⟩
  | and a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unNeg (LJF.Neg.and (negOf a) (negOf b)) = _
        rw [unNeg, iha.2, ihb.2]; rfl
      · show unNeg (LJF.Neg.and (negOf a) (negOf b)) = _
        rw [unNeg, iha.2, ihb.2]; rfl
  | or a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unPos (LJF.Pos.or (posOf a) (posOf b)) = _
        rw [unPos, iha.1, ihb.1]; rfl
      · show unNeg (LJF.Neg.up (LJF.Pos.or (posOf a) (posOf b))) = _
        rw [unNeg, unPos, iha.1, ihb.1]; rfl
  | ifThen a b iha ihb =>
      refine ⟨?_, ?_⟩
      · show unNeg (LJF.Neg.imp (posOf a) (negOf b)) = _
        rw [unNeg, iha.1, ihb.2]; rfl
      · show unNeg (LJF.Neg.imp (posOf a) (negOf b)) = _
        rw [unNeg, iha.1, ihb.2]; rfl
  | somehow a iha => exact ⟨iha.1, iha.2⟩

theorem unPos_posOf (φ : PLLFormula) : unPos (posOf φ) = PLLND.erase φ :=
  (un_round φ).1

theorem unNeg_negOf (φ : PLLFormula) : unNeg (negOf φ) = PLLND.erase φ :=
  (un_round φ).2

theorem unNeg_negOf_isIPL {φ : PLLFormula} (h : PLLND.isIPL φ) :
    unNeg (negOf φ) = φ := by
  rw [unNeg_negOf, PLLND.erase_eq_self_of_isIPL φ h]

theorem map_unNeg_negOf {Γ : List PLLFormula} (h : ∀ ψ ∈ Γ, PLLND.isIPL ψ) :
    (Γ.map negOf).map unNeg = Γ := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
      rw [List.map_cons, List.map_cons,
        unNeg_negOf_isIPL (h φ (List.mem_cons_self ..)),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-! ## Part 2: soundness — `LJF` derivations erase to natural deduction

One traversal of the four judgments.  A left focus `Γ [N] ⇒ P` becomes the
sequent `N, Γ ⊢ P`, and an inversion `Γ ; Ω ⇒ N` becomes `Ω, Γ ⊢ N`: the two
zones are simply concatenated, since natural deduction has no phases. -/

mutual

/-- Soundness at a stable sequent. -/
def soundStab : {Γ : List LJF.Neg} → {P : LJF.Pos} → LJF.Stab Γ P →
    LaxND (Γ.map unNeg) (unPos P)
  | _, _, .rfoc r => soundRF r
  | _, _, .lfoc h d =>
      (soundLF d).rename (by
        intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_map_of_mem h
        · exact hψ)

/-- Soundness under right focus. -/
def soundRF : {Γ : List LJF.Neg} → {P : LJF.Pos} → LJF.RFocus Γ P →
    LaxND (Γ.map unNeg) (unPos P)
  | _, _, .init h => .iden (List.mem_map_of_mem h)
  | _, _, .or1 r => .orIntro1 (soundRF r)
  | _, _, .or2 r => .orIntro2 (soundRF r)
  | _, _, .rel d => soundInv d

/-- Soundness under left focus: the focused hypothesis becomes an ordinary
one. -/
def soundLF : {Γ : List LJF.Neg} → {N : LJF.Neg} → {P : LJF.Pos} →
    LJF.LFoc Γ N P → LaxND (unNeg N :: Γ.map unNeg) (unPos P)
  | _, _, _, .rel d => soundInv d
  | _, _, _, .impL s d =>
      .impElim
        ((PLLND.LaxND.impIntro (soundLF d)).weaken _)
        (.impElim (.iden (List.mem_cons_self ..)) ((soundStab s).weaken _))
  | _, _, _, .and1 d =>
      .impElim ((PLLND.LaxND.impIntro (soundLF d)).weaken _)
        (.andElim1 (.iden (List.mem_cons_self ..)))
  | _, _, _, .and2 d =>
      .impElim ((PLLND.LaxND.impIntro (soundLF d)).weaken _)
        (.andElim2 (.iden (List.mem_cons_self ..)))

/-- Soundness through inversion. -/
def soundInv : {Γ : List LJF.Neg} → {Ω : List LJF.Pos} → {N : LJF.Neg} →
    LJF.Inv Γ Ω N → LaxND (Ω.map unPos ++ Γ.map unNeg) (unNeg N)
  | _, _, _, .impR d => .impIntro (soundInv d)
  | _, _, _, .andR d e => .andIntro (soundInv d) (soundInv e)
  | _, _, _, .stable s => soundStab s
  | _, _, _, .orL d e =>
      .orElim (.iden (List.mem_cons_self ..))
        ((soundInv d).rename (by
          intro ψ hψ
          simp only [List.map_cons, List.cons_append, List.mem_cons] at hψ ⊢
          tauto))
        ((soundInv e).rename (by
          intro ψ hψ
          simp only [List.map_cons, List.cons_append, List.mem_cons] at hψ ⊢
          tauto))
  | _, _, _, .flsL => .falsoElim _ (.iden (List.mem_cons_self ..))
  | _, _, _, .downL d =>
      (soundInv d).rename (by
        intro ψ hψ
        simp only [List.map_cons, List.cons_append, List.mem_append,
          List.mem_cons] at hψ ⊢
        tauto)
  | _, _, _, .atomL d =>
      (soundInv d).rename (by
        intro ψ hψ
        simp only [List.map_cons, List.cons_append, List.mem_append,
          List.mem_cons] at hψ ⊢
        tauto)

end

/-- **Soundness, headline form.**  An `LJF` derivation of `Γ ⇒ N` with nothing
pending yields the natural-deduction sequent it erases to. -/
theorem sound {Γ : List LJF.Neg} {N : LJF.Neg} (d : LJF.Inv Γ [] N) :
    PLLND.SemUI.Deriv (Γ.map unNeg) (unNeg N) :=
  ⟨soundInv d⟩

/-! ## Part 3: the shift bridge

For a *translated* formula the two polarities are interchangeable: a stable
proof of `posOf φ` and an inversion proof of `negOf φ` are interconvertible.
This is what lets the unpolarised sequent calculus be simulated at all — the
shifts of the translation never obstruct a rule. -/

/-- A proof of the negative translation is a stable proof of the positive
one. -/
def stabOfInv : (φ : PLLFormula) → {Δ : List LJF.Neg} →
    LJF.Inv Δ [] (negOf φ) → LJF.Stab Δ (posOf φ)
  | .prop _, _, d     => LJF.unStable d
  | .falsePLL, _, d   => LJF.unStable d
  | .or _ _, _, d     => LJF.unStable d
  | .and _ _, _, d    => .rfoc (.rel d)
  | .ifThen _ _, _, d => .rfoc (.rel d)
  | .somehow φ, _, d  => stabOfInv φ d

/-- …and conversely. -/
def invOfStab : (φ : PLLFormula) → {Δ : List LJF.Neg} →
    LJF.Stab Δ (posOf φ) → LJF.Inv Δ [] (negOf φ)
  | .prop _, _, s     => .stable s
  | .falsePLL, _, s   => .stable s
  | .or _ _, _, s     => .stable s
  | .and _ _, _, s    => LJF.negOfDownStab _ s
  | .ifThen _ _, _, s => LJF.negOfDownStab _ s
  | .somehow φ, _, s  => invOfStab φ s

/-! ### Branches of an inversion re-prove the hypothesis they came from

`upMerge` fires a shifted hypothesis and hands back, for each branch `b` of
the inversion of the positive, a context `b ++ Γ`.  The premise of the rule
being simulated was proved from the *hypothesis* `negOf φ`, not from `b`.  The
two lemmas below bridge that gap with no cut: a left focus on `negOf φ` is
discharged directly, because `extract` replays the branch of the inversion
that is already present in the derivation. -/

/-- Discharge a left focus on a shifted hypothesis against a branch of its
positive. -/
def upBranchLFoc {Q : LJF.Pos} {Δ : List LJF.Neg} {P : LJF.Pos}
    {b : List LJF.Neg} (hb : b ∈ LJF.invertPos Q) (hsub : ∀ X ∈ b, X ∈ Δ) :
    LJF.LFoc Δ (.up Q) P → LJF.Stab Δ P
  | .rel e =>
      LJF.unStable ((LJF.extract [] e b hb).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hsub Z hZ
        · exact hZ))

/-- Discharge a left focus on a hypothesis whose positive is a shift: the
single branch *is* the hypothesis. -/
def downBranchLFoc {M : LJF.Neg} {Δ : List LJF.Neg} {P : LJF.Pos}
    {b : List LJF.Neg} (hb : b ∈ LJF.invertPos (.down M))
    (hsub : ∀ X ∈ b, X ∈ Δ) (lf : LJF.LFoc Δ M P) : LJF.Stab Δ P := by
  simp only [LJF.invertPos, List.mem_singleton] at hb
  subst hb
  exact .lfoc (hsub _ (List.mem_cons_self ..)) lf

/-- Every use of the hypothesis `negOf φ` is available inside any branch of
the inversion of `posOf φ`. -/
def branchLFoc : (φ : PLLFormula) → {Δ : List LJF.Neg} → {P : LJF.Pos} →
    {b : List LJF.Neg} → b ∈ LJF.invertPos (posOf φ) → (∀ X ∈ b, X ∈ Δ) →
    LJF.LFoc Δ (negOf φ) P → LJF.Stab Δ P
  | .prop _, _, _, _, hb, hsub, lf   => upBranchLFoc hb hsub lf
  | .falsePLL, _, _, _, hb, _, _     => by
      simp only [posOf, LJF.invertPos, List.not_mem_nil] at hb
  | .or _ _, _, _, _, hb, hsub, lf   => upBranchLFoc hb hsub lf
  | .and _ _, _, _, _, hb, hsub, lf  => downBranchLFoc hb hsub lf
  | .ifThen _ _, _, _, _, hb, hsub, lf => downBranchLFoc hb hsub lf
  | .somehow φ, _, _, _, hb, hsub, lf => branchLFoc φ hb hsub lf

/-- **Branch transfer.**  A derivation from the hypothesis `negOf φ` is a
derivation from any branch of the inversion of `posOf φ`. -/
def branchIn (φ : PLLFormula) {Γ : List LJF.Neg} {C : LJF.Neg}
    {b : List LJF.Neg} (hb : b ∈ LJF.invertPos (posOf φ))
    (d : LJF.Inv (negOf φ :: Γ) [] C) : LJF.Inv (b ++ Γ) [] C :=
  LJF.simHyp (H := negOf φ)
    (fl := fun hs lf =>
      branchLFoc φ hb (fun X hX => hs X (List.mem_append_left _ hX)) lf)
    (fun _ hZ => List.mem_append_right b hZ) d

/-- **Hypothesis to pending positive.**  The translated hypothesis can be put
back into the inversion queue — the focused form of `⊃R`'s premise. -/
def shiftIn (φ : PLLFormula) {Γ : List LJF.Neg} {C : LJF.Neg}
    (d : LJF.Inv (negOf φ :: Γ) [] C) : LJF.Inv Γ [posOf φ] C :=
  LJF.invBranches (posOf φ) (fun _ hb => branchIn φ hb d)

/-! ## Part 4: completeness — the cut-free sequent calculus simulated in `LJF`

Every rule of `PLLND.SCh` is a construction in `LJF`.  No cut is used: left
rules become left foci (`simHyp`) or fires of a shifted hypothesis
(`upMerge`), which is exactly what a *cut-free* calculus makes possible. -/

/-- **Focalization, sequent form.**  Every cut-free sequent derivation has a
focused counterpart. -/
theorem focalizeSC : ∀ {n : Nat} {Γ : List PLLFormula} {C : PLLFormula},
    SCh n Γ C → Nonempty (LJF.Inv (Γ.map negOf) [] (negOf C)) := by
  intro n Γ C d
  induction d with
  | @init n Γ a h =>
      exact ⟨.stable (.rfoc (.init (List.mem_map_of_mem h)))⟩
  | @botL n Γ C h =>
      exact ⟨LJF.nBotElim (negOf C) (List.mem_map_of_mem h)⟩
  | @andR n Γ A B _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      exact ⟨.andR d₁ d₂⟩
  | @andL n Γ A B C h _ ih =>
      obtain ⟨d⟩ := ih
      have hAB : LJF.Neg.and (negOf A) (negOf B) ∈ Γ.map negOf :=
        List.mem_map_of_mem h
      exact ⟨LJF.simHyp (H := negOf B)
        (fl := fun hs lf => .lfoc (hs _ hAB) (.and2 lf)) (LJF.Sub.refl _)
        (LJF.simHyp (H := negOf A)
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ hAB)) (.and1 lf))
          (LJF.Sub.refl _) d)⟩
  | @orR1 n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.stable (LJF.stabOr1 (stabOfInv A d))⟩
  | @orR2 n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.stable (LJF.stabOr2 (stabOfInv B d))⟩
  | @orL n Γ A B C h _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      have hAB : LJF.Neg.up (LJF.Pos.or (posOf A) (posOf B)) ∈ Γ.map negOf :=
        List.mem_map_of_mem h
      refine ⟨LJF.upMerge (negOf C) hAB (fun b hb => ?_)⟩
      have hb' : b ∈ LJF.invertPos (posOf A) ++ LJF.invertPos (posOf B) := hb
      exact
        if hA : b ∈ LJF.invertPos (posOf A) then branchIn A hA d₁
        else branchIn B ((List.mem_append.mp hb').resolve_left hA) d₂
  | @impR n Γ A B _ ih =>
      obtain ⟨d⟩ := ih
      exact ⟨.impR (shiftIn A d)⟩
  | @impL n Γ A B C h _ _ ih₁ ih₂ =>
      obtain ⟨d₁⟩ := ih₁; obtain ⟨d₂⟩ := ih₂
      have hAB : LJF.Neg.imp (posOf A) (negOf B) ∈ Γ.map negOf :=
        List.mem_map_of_mem h
      exact ⟨LJF.simHyp (H := negOf B)
        (fl := fun {Δ'} _ hs lf =>
          .lfoc (hs _ hAB) (.impL (stabOfInv A (d₁.wk hs)) lf))
        (LJF.Sub.refl _) d₂⟩
  | @laxR n Γ A _ ih => exact ih
  | @laxL n Γ A B h _ ih =>
      obtain ⟨d⟩ := ih
      have hA : negOf (PLLFormula.somehow A) ∈ Γ.map negOf :=
        List.mem_map_of_mem h
      refine ⟨d.wk (fun Z hZ => ?_)⟩
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact hA
      · exact hZ

/-- **Focalization.**  Every natural-deduction derivation has a focused
counterpart, via cut elimination (`PLLND.ND_to_SC`). -/
theorem focalize {Γ : List PLLFormula} {C : PLLFormula}
    (d : LaxND Γ C) : Nonempty (LJF.Inv (Γ.map negOf) [] (negOf C)) :=
  match PLLND.ND_to_SC d with
  | ⟨_, s⟩ => focalizeSC s

/-- **Focalization, `Deriv` form.** -/
theorem focalizeD {Γ : List PLLFormula} {C : PLLFormula}
    (h : PLLND.SemUI.Deriv Γ C) :
    Nonempty (LJF.Inv (Γ.map negOf) [] (negOf C)) :=
  h.elim focalize

/-- **The bridge, both ways**, on the `◯`-free fragment: `LJF` derives the
translation of a sequent exactly when natural deduction derives the
sequent. -/
theorem focalization {Γ : List PLLFormula} {φ : PLLFormula}
    (hφ : PLLND.isIPL φ) (hΓ : ∀ ψ ∈ Γ, PLLND.isIPL ψ) :
    PLLND.SemUI.Deriv Γ φ ↔
      Nonempty (LJF.Inv (Γ.map negOf) [] (negOf φ)) := by
  sorry
