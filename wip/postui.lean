import wip.collapse

/-!
# POSITIVE uniform interpolation: the substitution-cover method

The campaign's refutation attack on last-variable uniform interpolation
closed both ways (`wip/collapse.lean`).  This file opens the POSITIVE
side: it exhibits a general method for *constructing* last-variable
uniform interpolants over the variable-free fragment, proves the method
correct, and discharges it on genuine syntactic subclasses.

## The method in one line

For a one-variable `φ` (atoms ⊆ `{p}`) and ANY variable-free `θ`, the
instance `φ[p := θ]` is variable-free and

    φ[p := θ] ⊢ χ    for every variable-free χ with φ ⊢ χ

— substitute `p := θ` in the derivation `φ ⊢ χ`; `χ` is untouched
(`inst_below`).  So *every* instance is a LOWER BOUND of the consequence
filter `F(φ) = {χ variable-free : φ ⊢ χ}`, and so is any finite
disjunction of instances.  Dually every instance is an UPPER BOUND of
the antecedent ideal `I(φ) = {χ variable-free : χ ⊢ φ}`
(`inst_above`), and so is any finite conjunction of instances.

Hence the whole `∃p`-problem reduces to a purely syntactic question:

    (★∃)   is there a finite list S of variable-free θ with
           φ ⊢ ⋁_{θ ∈ S} φ[p := θ]  ?

If yes, `⋁_{θ∈S} φ[p := θ]` IS the post-interpolant `∃p.φ`
(`postInterp_of_cover`).  Dually

    (★∀)   is there a finite list S of variable-free θ with
           ⋀_{θ ∈ S} φ[p := θ] ⊢ φ  ?

and then `⋀_{θ∈S} φ[p := θ]` IS the pre-interpolant `∀p.φ`
(`preInterp_of_cover`).  These are `HasCover` / `HasMeetCover` below;
the reduction theorems `postUI_of_coverConj` / `preUI_of_meetCoverConj`
turn the conjecture "every one-variable formula has a cover" into
last-variable UI for PLL.

## What is PROVED here

* `inst_below`, `inst_above` — the bound lemmas (the engine).
* `postInterp_of_cover`, `preInterp_of_cover` — the master reduction.
* `postInterp_of_pos`, `postInterp_of_neg`, `preInterp_of_pos`,
  `preInterp_of_neg` — **UI holds for every one-variable formula in
  which `p` occurs only positively, or only negatively**, with the
  interpolant given explicitly as `φ[p := ⊤]` or `φ[p := ⊥]`.  This
  needs the polarity monotonicity lemma `subst_mono`, proved here.
* A calculus of interpolants: closure under `∨` and under conjunction
  with a variable-free formula (`∃`-side); under `∧` and under a
  variable-free antecedent (`∀`-side); invariance under
  interderivability; uniqueness up to interderivability.
* `postInterp_of_boxFree` / `hasCover_of_boxFree` — **UI holds for the
  WHOLE `◯`-free one-variable fragment**: `∃p.φ = ⊥` if `φ` is
  inconsistent and `= ⊤` otherwise, with a ONE-element cover.  Proved
  semantically from the FMP: the replacement lemma `force_inst_congr`
  plus the two-valuedness of the variable-free `◯`-free fragment
  (`evalCl_sound`, `thm_of_force_nf`).
* Pinned instances, including
  `∃p.p = ⊤`, `∃p.◯p = ⊤`, `∃p.(◯p ⊃ p) = ⊤`,
  `∀p.p = ⊥`, `∀p.◯p = ◯⊥` (pinning the July stabilisation probe),
  `∃p.(p ∧ (p ⊃ t3)) = t3` (a NON-trivial ladder interpolant), and
  `∃p.((p ⊃ ◯⊥) ∧ ¬¬p) = ¬¬◯⊥` — an instance whose cover uses a `θ`
  that is neither `⊤` nor `⊥`, and in which `p` occurs with BOTH
  polarities.
* `phiMix_no_boolean_cover` — the fixed pool `[⊤, ⊥]` does NOT suffice
  in general (three-world countermodel `M3`), so the cover conjecture
  has real content: the substitution has to be read off `φ`.

## What is REFUTED

* `meetCoverConj_false` — the `∀`-side meet-cover method is
  INCOMPLETE: `p ∨ ¬p` has no finite variable-free substitution
  meet-cover (two-world model `N`; every variable-free `θ` satisfies
  `θ ∨ ¬θ` at the root, while `p ∨ ¬p` does not).  This refutes the
  method, not `∀p` itself — indeed `preInterp_wemP` PROVES
  `∀p.(p ∨ ¬p) = ⊥` by a doubling construction (`dbl`,
  `dbl_transfer`).  So the `∀`-side reduction is strictly
  one-directional.

## What is OPEN

`CoverConj`: whether every one-variable `φ` has a finite variable-free
substitution cover — equivalently (by `postUI_of_coverConj`) enough for
last-variable `∃p` in PLL.  Known to hold on the `◯`-free fragment and
on the polarity-pure fragment; not discharged by any fixed pool.
Stated as a `Prop`-valued definition.  No sorries anywhere in the file.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI PLLND.SemUI.RND
open PLLND.LaxInfinite (atomFree)

/-! ## 0.  Instances of a one-variable formula -/

/-- `inst θ φ = φ[p := θ]`, substitution for the single propositional
variable `pv = "p"`.  (`embed = inst oBot`.) -/
def inst (θ φ : PLLFormula) : PLLFormula := substP pv θ φ

theorem inst_var_eq (θ : PLLFormula) : inst θ (PLLFormula.prop pv) = θ := by
  show (if pv = pv then θ else PLLFormula.prop pv) = θ
  rw [if_pos rfl]

theorem inst_bot (θ : PLLFormula) : inst θ PLLFormula.falsePLL = .falsePLL := rfl

theorem inst_and (θ A B : PLLFormula) :
    inst θ (A.and B) = (inst θ A).and (inst θ B) := rfl

theorem inst_or (θ A B : PLLFormula) :
    inst θ (A.or B) = (inst θ A).or (inst θ B) := rfl

theorem inst_imp (θ A B : PLLFormula) :
    inst θ (A.ifThen B) = (inst θ A).ifThen (inst θ B) := rfl

theorem inst_box (θ A : PLLFormula) :
    inst θ A.somehow = (inst θ A).somehow := rfl

/-- Substitution fixes variable-free formulas. -/
theorem inst_atomFree_eq (θ : PLLFormula) {χ : PLLFormula}
    (hχ : atomFree χ = true) : inst θ χ = χ :=
  substP_atomFree pv θ χ hχ

/-- Substituting the variable for itself is the identity. -/
theorem inst_self : ∀ φ : PLLFormula, inst (PLLFormula.prop pv) φ = φ
  | .prop a => by
      by_cases ha : a = pv
      · subst ha; exact inst_var_eq _
      · show (if a = pv then PLLFormula.prop pv else PLLFormula.prop a) = _
        rw [if_neg ha]
  | .falsePLL => rfl
  | .and A B => by rw [inst_and, inst_self A, inst_self B]
  | .or A B => by rw [inst_or, inst_self A, inst_self B]
  | .ifThen A B => by rw [inst_imp, inst_self A, inst_self B]
  | .somehow A => by rw [inst_box, inst_self A]

/-! ### One-variable formulas -/

/-- `φ`'s only propositional variable is `pv`. -/
def onlyPv : PLLFormula → Bool
  | .prop a => a == pv
  | .falsePLL => true
  | .and A B => onlyPv A && onlyPv B
  | .or A B => onlyPv A && onlyPv B
  | .ifThen A B => onlyPv A && onlyPv B
  | .somehow A => onlyPv A

/-- A variable-free formula is (vacuously) one-variable. -/
theorem onlyPv_of_atomFree {φ : PLLFormula} (h : atomFree φ = true) :
    onlyPv φ = true := by
  induction φ with
  | prop a => simp [atomFree] at h
  | falsePLL => rfl
  | and A B ihA ihB =>
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      show (onlyPv A && onlyPv B) = true
      rw [ihA h'.1, ihB h'.2]; rfl
  | or A B ihA ihB =>
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      show (onlyPv A && onlyPv B) = true
      rw [ihA h'.1, ihB h'.2]; rfl
  | ifThen A B ihA ihB =>
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      show (onlyPv A && onlyPv B) = true
      rw [ihA h'.1, ihB h'.2]; rfl
  | somehow A ihA => exact ihA (by simpa [atomFree] using h)

/-- **A variable-free substitution instance of a one-variable formula is
variable-free.** -/
theorem inst_atomFree {θ : PLLFormula} (hθ : atomFree θ = true) :
    ∀ {φ : PLLFormula}, onlyPv φ = true → atomFree (inst θ φ) = true
  | .prop a, h => by
      have ha : a = pv := by simpa [onlyPv] using h
      subst ha
      rw [inst_var_eq]; exact hθ
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show (atomFree (inst θ A) && atomFree (inst θ B)) = true
      rw [inst_atomFree hθ h'.1, inst_atomFree hθ h'.2]; rfl
  | .or A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show (atomFree (inst θ A) && atomFree (inst θ B)) = true
      rw [inst_atomFree hθ h'.1, inst_atomFree hθ h'.2]; rfl
  | .ifThen A B, h => by
      have h' : onlyPv A = true ∧ onlyPv B = true := by
        simpa [onlyPv, Bool.and_eq_true] using h
      show (atomFree (inst θ A) && atomFree (inst θ B)) = true
      rw [inst_atomFree hθ h'.1, inst_atomFree hθ h'.2]; rfl
  | .somehow A, h => inst_atomFree hθ (φ := A) (by simpa [onlyPv] using h)

/-! ## 1.  The two bound lemmas — the engine

Everything downstream is these two lines of substitution. -/

/-- **LOWER BOUND.**  Every variable-free consequence of `φ` is already
a consequence of every instance `φ[p := θ]`.  (No hypothesis on `φ` or
`θ`: substitution is applied to the derivation and fixes `χ`.) -/
theorem inst_below {φ χ : PLLFormula} (θ : PLLFormula)
    (hχ : atomFree χ = true) (h : Deriv [φ] χ) : Deriv [inst θ φ] χ := by
  have h1 := Deriv.substP' (Γ := [φ]) (φ := χ) pv θ h
  rwa [show [φ].map (substP pv θ) = [inst θ φ] from rfl,
       substP_atomFree pv θ χ hχ] at h1

/-- **UPPER BOUND.**  Every variable-free antecedent of `φ` is already
an antecedent of every instance `φ[p := θ]`. -/
theorem inst_above {φ χ : PLLFormula} (θ : PLLFormula)
    (hχ : atomFree χ = true) (h : Deriv [χ] φ) : Deriv [χ] (inst θ φ) := by
  have h1 := Deriv.substP' (Γ := [χ]) (φ := φ) pv θ h
  rwa [show [χ].map (substP pv θ) = [substP pv θ χ] from rfl,
       substP_atomFree pv θ χ hχ] at h1

/-! ## 2.  Variable-freeness of finite meets and joins -/

theorem atomFree_bigOr :
    ∀ {L : List PLLFormula}, (∀ θ ∈ L, atomFree θ = true) →
      atomFree (bigOr L) = true
  | [], _ => rfl
  | a :: l, h => by
      show (atomFree a && atomFree (bigOr l)) = true
      rw [h a (.head _), atomFree_bigOr (fun θ hθ => h θ (.tail _ hθ))]; rfl

theorem atomFree_bigAnd :
    ∀ {L : List PLLFormula}, (∀ θ ∈ L, atomFree θ = true) →
      atomFree (bigAnd L) = true
  | [], _ => rfl
  | [a], h => h a (.head _)
  | a :: b :: l, h => by
      show (atomFree a && atomFree (bigAnd (b :: l))) = true
      rw [h a (.head _), atomFree_bigAnd (fun θ hθ => h θ (.tail _ hθ))]; rfl

/-- A finite conjunction is forced where all its members are. -/
theorem force_bigAnd {C : ConstraintModel} {w : C.W} :
    ∀ {L : List PLLFormula}, (∀ A ∈ L, C.force w A) → C.force w (bigAnd L)
  | [], _ => fun _ _ h => h
  | [A], h => h A (.head _)
  | A :: B :: l, h =>
      ⟨h A (.head _), force_bigAnd (fun D hD => h D (.tail _ hD))⟩

/-! ## 3.  The master reduction -/

/-- The list of instances of `φ` at the substitutions in `S`. -/
def instList (S : List PLLFormula) (φ : PLLFormula) : List PLLFormula :=
  S.map (fun θ => inst θ φ)

theorem mem_instList {S : List PLLFormula} {φ ψ : PLLFormula}
    (h : ψ ∈ instList S φ) : ∃ θ ∈ S, ψ = inst θ φ := by
  obtain ⟨θ, hθ, rfl⟩ := List.mem_map.mp h
  exact ⟨θ, hθ, rfl⟩

theorem atomFree_instList {S : List PLLFormula} {φ : PLLFormula}
    (hS : ∀ θ ∈ S, atomFree θ = true) (hφ : onlyPv φ = true) :
    ∀ ψ ∈ instList S φ, atomFree ψ = true := by
  intro ψ hψ
  obtain ⟨θ, hθ, rfl⟩ := mem_instList hψ
  exact inst_atomFree (hS θ hθ) hφ

/-- **MASTER REDUCTION, `∃`-side.**  If `φ` is covered by the finitely
many variable-free instances `φ[p := θ]`, `θ ∈ S`, then their
disjunction IS the uniform post-interpolant of `φ` over the
variable-free fragment. -/
theorem postInterp_of_cover {φ : PLLFormula} (hφ : onlyPv φ = true)
    {S : List PLLFormula} (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [φ] (bigOr (instList S φ))) :
    IsPostInterp φ (bigOr (instList S φ)) := by
  refine ⟨atomFree_bigOr (atomFree_instList hS hφ), hcov, ?_⟩
  intro χ hχ hd
  refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
  intro ψ hψ
  obtain ⟨θ, -, rfl⟩ := mem_instList hψ
  exact Deriv.toHead (inst_below θ hχ hd)

/-- **MASTER REDUCTION, `∀`-side.**  If the finite meet of the
variable-free instances entails `φ`, that meet IS the uniform
pre-interpolant. -/
theorem preInterp_of_cover {φ : PLLFormula} (hφ : onlyPv φ = true)
    {S : List PLLFormula} (hS : ∀ θ ∈ S, atomFree θ = true)
    (hcov : Deriv [bigAnd (instList S φ)] φ) :
    IsPreInterp φ (bigAnd (instList S φ)) := by
  refine ⟨atomFree_bigAnd (atomFree_instList hS hφ), hcov, ?_⟩
  intro χ hχ hd
  refine Deriv.bigAndIntro ?_
  intro ψ hψ
  obtain ⟨θ, -, rfl⟩ := mem_instList hψ
  exact inst_above θ hχ hd

/-- Single-instance form of the `∃`-side reduction. -/
theorem postInterp_of_self_inst {φ θ : PLLFormula} (hφ : onlyPv φ = true)
    (hθ : atomFree θ = true) (h : Deriv [φ] (inst θ φ)) :
    IsPostInterp φ (inst θ φ) :=
  ⟨inst_atomFree hθ hφ, h, fun χ hχ hd => inst_below θ hχ hd⟩

/-- Single-instance form of the `∀`-side reduction. -/
theorem preInterp_of_self_inst {φ θ : PLLFormula} (hφ : onlyPv φ = true)
    (hθ : atomFree θ = true) (h : Deriv [inst θ φ] φ) :
    IsPreInterp φ (inst θ φ) :=
  ⟨inst_atomFree hθ hφ, h, fun χ hχ hd => inst_above θ hχ hd⟩

/-- **`⊤` is the post-interpolant whenever some variable-free instance
of `φ` is a theorem.**  (No one-variable hypothesis needed.) -/
theorem postInterp_top {φ θ : PLLFormula} (hθ : atomFree θ = true)
    (h : Deriv [] (inst θ φ)) : IsPostInterp φ truePLL := by
  refine ⟨rfl, topD, ?_⟩
  intro χ hχ hd
  exact Deriv.cutHead (h.rename (by simp)) (inst_below θ hχ hd)

/-- **`⊥` is the pre-interpolant whenever some variable-free instance of
`φ` is refutable.** -/
theorem preInterp_bot {φ θ : PLLFormula}
    (h : Deriv [inst θ φ] PLLFormula.falsePLL) : IsPreInterp φ PLLFormula.falsePLL := by
  refine ⟨rfl, Deriv.falsoElim _ (Deriv.iden (.head _)), ?_⟩
  intro χ hχ hd
  exact Deriv.cutHead (inst_above θ hχ hd) h

/-! ## 4.  The open conjecture, and the reduction of last-variable UI -/

/-- **`φ` has a variable-free substitution cover**: finitely many
variable-free `θ` whose instances jointly exhaust `φ`. -/
def HasCover (φ : PLLFormula) : Prop :=
  ∃ S : List PLLFormula, (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [φ] (bigOr (instList S φ))

/-- **`φ` has a variable-free substitution meet-cover.** -/
def HasMeetCover (φ : PLLFormula) : Prop :=
  ∃ S : List PLLFormula, (∀ θ ∈ S, atomFree θ = true) ∧
    Deriv [bigAnd (instList S φ)] φ

/-- **OPEN.**  Every one-variable formula has a variable-free
substitution cover. -/
def CoverConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasCover φ

/-- **REFUTED** (`meetCoverConj_false`, §10).  Every one-variable
formula has a variable-free substitution meet-cover — false at
`wem = p ∨ ¬p`. -/
def MeetCoverConj : Prop := ∀ φ : PLLFormula, onlyPv φ = true → HasMeetCover φ

/-- **The reduction of last-variable `∃p` to the cover conjecture.** -/
theorem postUI_of_coverConj (h : CoverConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPostInterp φ ψ := by
  intro φ hφ
  obtain ⟨S, hS, hcov⟩ := h φ hφ
  exact ⟨_, postInterp_of_cover hφ hS hcov⟩

/-- **The reduction of last-variable `∀p` to the meet-cover
conjecture.** -/
theorem preUI_of_meetCoverConj (h : MeetCoverConj) :
    ∀ φ : PLLFormula, onlyPv φ = true → ∃ ψ, IsPreInterp φ ψ := by
  intro φ hφ
  obtain ⟨S, hS, hcov⟩ := h φ hφ
  exact ⟨_, preInterp_of_cover hφ hS hcov⟩

/-! ## 5.  Polarity, and the first genuinely positive UI theorems -/

/-- `polar φ = (p occurs only positively in φ, p occurs only negatively
in φ)`. -/
def polar : PLLFormula → Bool × Bool
  | .prop a => (true, !(a == pv))
  | .falsePLL => (true, true)
  | .and A B => ((polar A).1 && (polar B).1, (polar A).2 && (polar B).2)
  | .or A B => ((polar A).1 && (polar B).1, (polar A).2 && (polar B).2)
  | .ifThen A B => ((polar A).2 && (polar B).1, (polar A).1 && (polar B).2)
  | .somehow A => polar A

/-- `p` occurs only positively in `φ`. -/
def posIn (φ : PLLFormula) : Bool := (polar φ).1

/-- `p` occurs only negatively in `φ`. -/
def negIn (φ : PLLFormula) : Bool := (polar φ).2

/-- **Polarity monotonicity.**  A derivation `θ₁ ⊢ θ₂` lifts through
positive occurrences and reverses through negative ones. -/
theorem subst_mono {θ₁ θ₂ : PLLFormula} (hθ : Deriv [θ₁] θ₂) :
    ∀ φ : PLLFormula,
      (posIn φ = true → Deriv [inst θ₁ φ] (inst θ₂ φ)) ∧
      (negIn φ = true → Deriv [inst θ₂ φ] (inst θ₁ φ)) := by
  intro φ
  induction φ with
  | prop a =>
      by_cases ha : a = pv
      · subst ha
        refine ⟨fun _ => ?_, fun h => ?_⟩
        · rw [inst_var_eq, inst_var_eq]; exact hθ
        · exact absurd h (by simp [negIn, polar])
      · have e : ∀ θ : PLLFormula, inst θ (PLLFormula.prop a) = PLLFormula.prop a := by
          intro θ
          show (if a = pv then θ else PLLFormula.prop a) = _
          rw [if_neg ha]
        exact ⟨fun _ => by simp only [e]; exact Deriv.iden (.head _),
               fun _ => by simp only [e]; exact Deriv.iden (.head _)⟩
  | falsePLL => exact ⟨fun _ => Deriv.iden (.head _), fun _ => Deriv.iden (.head _)⟩
  | and A B ihA ihB =>
      constructor
      · intro h
        have h' : posIn A = true ∧ posIn B = true := by
          simpa [posIn, polar, Bool.and_eq_true] using h
        exact Deriv.andIntro
          (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (ihA.1 h'.1))
          (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (ihB.1 h'.2))
      · intro h
        have h' : negIn A = true ∧ negIn B = true := by
          simpa [negIn, polar, Bool.and_eq_true] using h
        exact Deriv.andIntro
          (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (ihA.2 h'.1))
          (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (ihB.2 h'.2))
  | or A B ihA ihB =>
      constructor
      · intro h
        have h' : posIn A = true ∧ posIn B = true := by
          simpa [posIn, polar, Bool.and_eq_true] using h
        exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.orIntro1 (Deriv.toHead (ihA.1 h'.1)))
          (Deriv.orIntro2 (Deriv.toHead (ihB.1 h'.2)))
      · intro h
        have h' : negIn A = true ∧ negIn B = true := by
          simpa [negIn, polar, Bool.and_eq_true] using h
        exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.orIntro1 (Deriv.toHead (ihA.2 h'.1)))
          (Deriv.orIntro2 (Deriv.toHead (ihB.2 h'.2)))
  | ifThen A B ihA ihB =>
      constructor
      · intro h
        have h' : negIn A = true ∧ posIn B = true := by
          simpa [posIn, negIn, polar, Bool.and_eq_true] using h
        exact Deriv.impIntro (Deriv.cutHead
          (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
            (Deriv.cutHead (Deriv.iden (.head _)) (ihA.2 h'.1))) (ihB.1 h'.2))
      · intro h
        have h' : posIn A = true ∧ negIn B = true := by
          simpa [posIn, negIn, polar, Bool.and_eq_true] using h
        exact Deriv.impIntro (Deriv.cutHead
          (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
            (Deriv.cutHead (Deriv.iden (.head _)) (ihA.1 h'.1))) (ihB.2 h'.2))
  | somehow A ihA =>
      exact ⟨fun h => Deriv.somehowMono (ihA.1 (by simpa [posIn, polar] using h)),
             fun h => Deriv.somehowMono (ihA.2 (by simpa [negIn, polar] using h))⟩

theorem atomFree_true : atomFree truePLL = true := rfl

/-- `φ ⊢ φ[p := ⊤]` when `p` occurs only positively. -/
theorem deriv_inst_top_of_pos {φ : PLLFormula} (h : posIn φ = true) :
    Deriv [φ] (inst truePLL φ) := by
  have := (subst_mono (θ₁ := PLLFormula.prop pv) (θ₂ := truePLL) topD φ).1 h
  rwa [inst_self] at this

/-- `φ ⊢ φ[p := ⊥]` when `p` occurs only negatively. -/
theorem deriv_inst_bot_of_neg {φ : PLLFormula} (h : negIn φ = true) :
    Deriv [φ] (inst PLLFormula.falsePLL φ) := by
  have := (subst_mono (θ₁ := PLLFormula.falsePLL) (θ₂ := PLLFormula.prop pv)
    (Deriv.falsoElim _ (Deriv.iden (.head _))) φ).2 h
  rwa [inst_self] at this

/-- `φ[p := ⊥] ⊢ φ` when `p` occurs only positively. -/
theorem deriv_inst_bot_le_of_pos {φ : PLLFormula} (h : posIn φ = true) :
    Deriv [inst PLLFormula.falsePLL φ] φ := by
  have := (subst_mono (θ₁ := PLLFormula.falsePLL) (θ₂ := PLLFormula.prop pv)
    (Deriv.falsoElim _ (Deriv.iden (.head _))) φ).1 h
  rwa [inst_self] at this

/-- `φ[p := ⊤] ⊢ φ` when `p` occurs only negatively. -/
theorem deriv_inst_top_le_of_neg {φ : PLLFormula} (h : negIn φ = true) :
    Deriv [inst truePLL φ] φ := by
  have := (subst_mono (θ₁ := PLLFormula.prop pv) (θ₂ := truePLL) topD φ).2 h
  rwa [inst_self] at this

/-- **POSITIVE UI, `∃`-side, positive polarity.**  For every
one-variable `φ` in which `p` occurs only positively, `φ[p := ⊤]` is
the uniform post-interpolant `∃p.φ` over the variable-free fragment. -/
theorem postInterp_of_pos {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : posIn φ = true) : IsPostInterp φ (inst truePLL φ) :=
  postInterp_of_self_inst hφ atomFree_true (deriv_inst_top_of_pos h)

/-- **POSITIVE UI, `∃`-side, negative polarity.**  `p` only negative:
`∃p.φ = φ[p := ⊥]`. -/
theorem postInterp_of_neg {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : negIn φ = true) : IsPostInterp φ (inst PLLFormula.falsePLL φ) :=
  postInterp_of_self_inst hφ rfl (deriv_inst_bot_of_neg h)

/-- **POSITIVE UI, `∀`-side, positive polarity.**  `p` only positive:
`∀p.φ = φ[p := ⊥]`. -/
theorem preInterp_of_pos {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : posIn φ = true) : IsPreInterp φ (inst PLLFormula.falsePLL φ) :=
  preInterp_of_self_inst hφ rfl (deriv_inst_bot_le_of_pos h)

/-- **POSITIVE UI, `∀`-side, negative polarity.**  `p` only negative:
`∀p.φ = φ[p := ⊤]`. -/
theorem preInterp_of_neg {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : negIn φ = true) : IsPreInterp φ (inst truePLL φ) :=
  preInterp_of_self_inst hφ atomFree_true (deriv_inst_top_le_of_neg h)

/-- **Both interpolants exist for every polarity-pure one-variable
formula.** -/
theorem UI_of_pure {φ : PLLFormula} (hφ : onlyPv φ = true)
    (h : posIn φ = true ∨ negIn φ = true) :
    (∃ ψ, IsPostInterp φ ψ) ∧ (∃ ψ, IsPreInterp φ ψ) := by
  rcases h with h | h
  · exact ⟨⟨_, postInterp_of_pos hφ h⟩, ⟨_, preInterp_of_pos hφ h⟩⟩
  · exact ⟨⟨_, postInterp_of_neg hφ h⟩, ⟨_, preInterp_of_neg hφ h⟩⟩

/-! ## 6.  A calculus of uniform interpolants -/

/-- A variable-free formula is its own post-interpolant. -/
theorem postInterp_self {φ : PLLFormula} (hφ : atomFree φ = true) :
    IsPostInterp φ φ :=
  ⟨hφ, Deriv.iden (.head _), fun _ _ h => h⟩

/-- A variable-free formula is its own pre-interpolant. -/
theorem preInterp_self {φ : PLLFormula} (hφ : atomFree φ = true) :
    IsPreInterp φ φ :=
  ⟨hφ, Deriv.iden (.head _), fun _ _ h => h⟩

/-- Post-interpolants are unique up to interderivability. -/
theorem postInterp_unique {φ ψ ψ' : PLLFormula}
    (h : IsPostInterp φ ψ) (h' : IsPostInterp φ ψ') : Interd ψ ψ' :=
  ⟨h.2.2 ψ' h'.1 h'.2.1, h'.2.2 ψ h.1 h.2.1⟩

/-- Pre-interpolants are unique up to interderivability. -/
theorem preInterp_unique {φ ψ ψ' : PLLFormula}
    (h : IsPreInterp φ ψ) (h' : IsPreInterp φ ψ') : Interd ψ ψ' :=
  ⟨h'.2.2 ψ h.1 h.2.1, h.2.2 ψ' h'.1 h'.2.1⟩

/-- Post-interpolation is invariant under interderivability of the
argument. -/
theorem postInterp_congr {φ φ' ψ : PLLFormula} (hI : Interd φ φ')
    (h : IsPostInterp φ ψ) : IsPostInterp φ' ψ :=
  ⟨h.1, Deriv.cutHead hI.2 h.2.1,
   fun χ hχ hd => h.2.2 χ hχ (Deriv.cutHead hI.1 hd)⟩

/-- … and under interderivability of the interpolant. -/
theorem postInterp_congr_right {φ ψ ψ' : PLLFormula} (hI : Interd ψ ψ')
    (hψ' : atomFree ψ' = true) (h : IsPostInterp φ ψ) : IsPostInterp φ ψ' :=
  ⟨hψ', Deriv.cutHead h.2.1 hI.1,
   fun χ hχ hd => Deriv.cutHead hI.2 (h.2.2 χ hχ hd)⟩

theorem preInterp_congr {φ φ' ψ : PLLFormula} (hI : Interd φ φ')
    (h : IsPreInterp φ ψ) : IsPreInterp φ' ψ :=
  ⟨h.1, Deriv.cutHead h.2.1 hI.1,
   fun χ hχ hd => h.2.2 χ hχ (Deriv.cutHead hd hI.2)⟩

theorem preInterp_congr_right {φ ψ ψ' : PLLFormula} (hI : Interd ψ ψ')
    (hψ' : atomFree ψ' = true) (h : IsPreInterp φ ψ) : IsPreInterp φ ψ' :=
  ⟨hψ', Deriv.cutHead hI.2 h.2.1,
   fun χ hχ hd => Deriv.cutHead (h.2.2 χ hχ hd) hI.1⟩

/-- **`∃p` commutes with `∨`.** -/
theorem postInterp_or {φ₁ φ₂ ψ₁ ψ₂ : PLLFormula}
    (h₁ : IsPostInterp φ₁ ψ₁) (h₂ : IsPostInterp φ₂ ψ₂) :
    IsPostInterp (φ₁.or φ₂) (ψ₁.or ψ₂) := by
  obtain ⟨a₁, d₁, m₁⟩ := h₁
  obtain ⟨a₂, d₂, m₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · show (atomFree ψ₁ && atomFree ψ₂) = true
    rw [a₁, a₂]; rfl
  · exact Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.toHead d₁)) (Deriv.orIntro2 (Deriv.toHead d₂))
  · intro χ hχ hd
    refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · exact Deriv.toHead (m₁ χ hχ
        (Deriv.cutHead (Deriv.orIntro1 (Deriv.iden (.head _))) hd))
    · exact Deriv.toHead (m₂ χ hχ
        (Deriv.cutHead (Deriv.orIntro2 (Deriv.iden (.head _))) hd))

/-- **`∃p` passes a variable-free conjunct.** -/
theorem postInterp_andClosed {φ ψ χ : PLLFormula} (h : IsPostInterp φ ψ)
    (hχ : atomFree χ = true) : IsPostInterp (φ.and χ) (ψ.and χ) := by
  obtain ⟨a, d, m⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (atomFree ψ && atomFree χ) = true
    rw [a, hχ]; rfl
  · exact Deriv.andIntro
      (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) d)
      (Deriv.andElim2 (Deriv.iden (.head _)))
  · intro δ hδ hdd
    have h1 : Deriv [φ] (χ.ifThen δ) :=
      Deriv.impIntro (Deriv.cutHead
        (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))) hdd)
    have hcd : atomFree (χ.ifThen δ) = true := by
      show (atomFree χ && atomFree δ) = true
      rw [hχ, hδ]; rfl
    exact Deriv.impElim
      (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (m _ hcd h1))
      (Deriv.andElim2 (Deriv.iden (.head _)))

/-- **`∀p` commutes with `∧`.** -/
theorem preInterp_and {φ₁ φ₂ ψ₁ ψ₂ : PLLFormula}
    (h₁ : IsPreInterp φ₁ ψ₁) (h₂ : IsPreInterp φ₂ ψ₂) :
    IsPreInterp (φ₁.and φ₂) (ψ₁.and ψ₂) := by
  obtain ⟨a₁, d₁, m₁⟩ := h₁
  obtain ⟨a₂, d₂, m₂⟩ := h₂
  refine ⟨?_, ?_, ?_⟩
  · show (atomFree ψ₁ && atomFree ψ₂) = true
    rw [a₁, a₂]; rfl
  · exact Deriv.andIntro
      (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) d₁)
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) d₂)
  · intro χ hχ hd
    exact Deriv.andIntro
      (m₁ χ hχ (Deriv.cutHead hd (Deriv.andElim1 (Deriv.iden (.head _)))))
      (m₂ χ hχ (Deriv.cutHead hd (Deriv.andElim2 (Deriv.iden (.head _)))))

/-- **`∀p` passes a variable-free antecedent.** -/
theorem preInterp_impClosed {φ ψ χ : PLLFormula} (h : IsPreInterp φ ψ)
    (hχ : atomFree χ = true) : IsPreInterp (χ.ifThen φ) (χ.ifThen ψ) := by
  obtain ⟨a, d, m⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show (atomFree χ && atomFree ψ) = true
    rw [a, hχ]; rfl
  · exact Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))) d)
  · intro δ hδ hd
    have hdc : atomFree (δ.and χ) = true := by
      show (atomFree δ && atomFree χ) = true
      rw [hχ, hδ]; rfl
    have h1 : Deriv [δ.and χ] φ :=
      Deriv.impElim
        (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) hd)
        (Deriv.andElim2 (Deriv.iden (.head _)))
    have h2 : Deriv [δ.and χ] ψ := m _ hdc h1
    exact Deriv.impIntro (Deriv.cutHead
      (Deriv.andIntro (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))) h2)

/-! ## 7.  Pinned instances

Each is a machine-checked value of `∃p.φ` or `∀p.φ` over the
variable-free fragment. -/

/-- `∃p. p = ⊤`. -/
theorem exists_p : IsPostInterp (PLLFormula.prop pv) truePLL := by
  have h := postInterp_of_pos (φ := PLLFormula.prop pv) rfl rfl
  rwa [inst_var_eq] at h

/-- `∀p. p = ⊥`. -/
theorem forall_p : IsPreInterp (PLLFormula.prop pv) PLLFormula.falsePLL := by
  have h := preInterp_of_pos (φ := PLLFormula.prop pv) rfl rfl
  rwa [inst_var_eq] at h

/-- `◯⊤ ⊣⊢ ⊤`. -/
theorem interd_boxTop : Interd (PLLFormula.somehow truePLL) truePLL :=
  ⟨topD, dSomehowIntro topD⟩

/-- `∃p. ◯p = ⊤`. -/
theorem exists_box_p : IsPostInterp ((PLLFormula.prop pv).somehow) truePLL := by
  have h := postInterp_of_pos (φ := (PLLFormula.prop pv).somehow) rfl rfl
  rw [inst_box, inst_var_eq] at h
  exact postInterp_congr_right interd_boxTop rfl h

/-- **`∀p. ◯p = ◯⊥`** — the July stabilisation probe (approximants of
`∀p.◯p` settle at `◯⊥` from rank 2), now a theorem. -/
theorem forall_box_p : IsPreInterp ((PLLFormula.prop pv).somehow) oBot := by
  have h := preInterp_of_pos (φ := (PLLFormula.prop pv).somehow) rfl rfl
  rw [inst_box, inst_var_eq] at h
  exact h

/-- `∃p. (◯p ⊃ p) = ⊤` — `p` has mixed polarity, but the instance
`p := ⊤` is a theorem. -/
theorem exists_boxp_imp_p :
    IsPostInterp (((PLLFormula.prop pv).somehow).ifThen (PLLFormula.prop pv))
      truePLL := by
  refine postInterp_top (θ := truePLL) rfl ?_
  rw [inst_imp, inst_box, inst_var_eq]
  exact Deriv.impIntro topD

/-! ### A non-trivial ladder interpolant: `∃p.(p ∧ (p ⊃ t3)) = t3` -/

/-- `p ∧ (p ⊃ t3)`, with `t3 = rnSub 3 = ◯⊥ ∨ ¬◯⊥` the third
Rieger–Nishimura rung over `◯⊥`. -/
def exLadder : PLLFormula :=
  (PLLFormula.prop pv).and ((PLLFormula.prop pv).ifThen (rnSub 3))

theorem exLadder_onlyPv : onlyPv exLadder = true := by
  show ((pv == pv) && ((pv == pv) && onlyPv (rnSub 3))) = true
  rw [onlyPv_of_atomFree (rnSub_atomFree 3)]
  rfl

theorem inst_top_exLadder :
    inst truePLL exLadder = truePLL.and (truePLL.ifThen (rnSub 3)) := by
  show (inst truePLL (PLLFormula.prop pv)).and
    ((inst truePLL (PLLFormula.prop pv)).ifThen (inst truePLL (rnSub 3))) = _
  rw [inst_var_eq, inst_atomFree_eq truePLL (rnSub_atomFree 3)]

/-- `∃p.(p ∧ (p ⊃ t3))`, in raw instance form. -/
theorem exists_exLadder_raw : IsPostInterp exLadder (inst truePLL exLadder) := by
  refine postInterp_of_self_inst exLadder_onlyPv atomFree_true ?_
  rw [inst_top_exLadder]
  refine Deriv.andIntro topD (Deriv.impIntro ?_)
  exact Deriv.impElim (Deriv.andElim2 (Deriv.iden (.tail _ (.head _))))
    (Deriv.andElim1 (Deriv.iden (.tail _ (.head _))))

theorem interd_inst_top_exLadder : Interd (inst truePLL exLadder) (rnSub 3) := by
  rw [inst_top_exLadder]
  exact ⟨Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _))) topD,
         Deriv.andIntro topD (Deriv.impIntro (Deriv.iden (.tail _ (.head _))))⟩

/-- **`∃p.(p ∧ (p ⊃ t3)) = t3`** — a uniform post-interpolant which is
neither `⊤` nor `⊥` but a genuine Rieger–Nishimura rung. -/
theorem exists_exLadder : IsPostInterp exLadder (rnSub 3) :=
  postInterp_congr_right interd_inst_top_exLadder (rnSub_atomFree 3)
    exists_exLadder_raw

/-! ### A mixed-polarity instance whose cover needs `θ ∉ {⊤, ⊥}`

`φmix = (p ⊃ ◯⊥) ∧ ¬¬p`.  Here `p` occurs negatively in the first
conjunct and positively in the second, and the cover substitution is
`θ = ◯⊥`; §8 shows that neither `θ = ⊤` nor `θ = ⊥` covers `φmix`. -/

/-- `¬A`. -/
def nt (A : PLLFormula) : PLLFormula := A.ifThen PLLFormula.falsePLL

/-- `(p ⊃ ◯⊥) ∧ ¬¬p`. -/
def phiMix : PLLFormula :=
  ((PLLFormula.prop pv).ifThen oBot).and (nt (nt (PLLFormula.prop pv)))

theorem phiMix_onlyPv : onlyPv phiMix = true := by decide

theorem inst_oBot_phiMix :
    inst oBot phiMix = (oBot.ifThen oBot).and (nt (nt oBot)) := by
  show ((inst oBot (PLLFormula.prop pv)).ifThen (inst oBot oBot)).and
    (((inst oBot (PLLFormula.prop pv)).ifThen (inst oBot PLLFormula.falsePLL)).ifThen
      (inst oBot PLLFormula.falsePLL)) = _
  rw [inst_var_eq, inst_atomFree_eq oBot (show atomFree oBot = true from rfl)]
  rfl

/-- `φmix ⊢ φmix[p := ◯⊥]` — the cover. -/
theorem phiMix_cover : Deriv [phiMix] (inst oBot phiMix) := by
  rw [inst_oBot_phiMix]
  refine Deriv.andIntro (Deriv.impIntro (Deriv.iden (.head _))) ?_
  -- `¬¬◯⊥`: assume `¬◯⊥`; `p ⊃ ◯⊥` then gives `¬p`, contradicting `¬¬p`
  refine Deriv.impIntro ?_
  refine Deriv.impElim
    (Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))) ?_
  refine Deriv.impIntro ?_
  refine Deriv.impElim (Deriv.iden (.tail _ (.head _))) ?_
  exact Deriv.impElim
    (Deriv.andElim1 (Deriv.iden (.tail _ (.tail _ (.head _)))))
    (Deriv.iden (.head _))

/-- **`∃p.((p ⊃ ◯⊥) ∧ ¬¬p) = ¬¬◯⊥`.** -/
theorem exists_phiMix_raw : IsPostInterp phiMix (inst oBot phiMix) :=
  postInterp_of_self_inst phiMix_onlyPv (show atomFree oBot = true from rfl)
    phiMix_cover

theorem interd_inst_oBot_phiMix : Interd (inst oBot phiMix) (nt (nt oBot)) := by
  rw [inst_oBot_phiMix]
  exact ⟨Deriv.andElim2 (Deriv.iden (.head _)),
         Deriv.andIntro (Deriv.impIntro (Deriv.iden (.head _)))
           (Deriv.iden (.head _))⟩

/-- The interpolant in reduced form: `∃p.φmix = ¬¬◯⊥`. -/
theorem exists_phiMix : IsPostInterp phiMix (nt (nt oBot)) :=
  postInterp_congr_right interd_inst_oBot_phiMix rfl exists_phiMix_raw

/-! ## 8.  The trivial cover is NOT enough

A three-world countermodel `M3` shows that `φmix` is covered by
`θ = ◯⊥` but by neither `θ = ⊤` nor `θ = ⊥`, and not by the
two-element list `[⊤, ⊥]` either.  So the cover conjecture cannot be
discharged by any fixed finite pool of "Boolean" substitutions: the
substitution has to be read off `φ`.

    M3 :  0 ⊑ 1 ⊑ 2,   Rₘ = id ∪ {(1,2)},   F = {2},   V(a) = {1,2}

At `0`: `p ⊃ ◯⊥` holds because `p` only starts at `1`, where the
`Rₘ`-edge `1 ⇝ 2` into the fallible world validates `◯⊥`; `¬¬p` holds
because every non-fallible world sees a `p`-world; but `◯⊥` itself
fails at `0`, whose only `Rₘ`-successor is `0`. -/

/-- The modal relation of `M3`: identity plus the edge `1 ⇝ 2`. -/
def Rm3 (x y : Fin 3) : Prop := x = y ∨ (x = 1 ∧ y = 2)

instance (x y : Fin 3) : Decidable (Rm3 x y) := by
  unfold Rm3; infer_instance

theorem Rm3_refl : ∀ x : Fin 3, Rm3 x x := by decide
theorem Rm3_trans : ∀ x y z : Fin 3, Rm3 x y → Rm3 y z → Rm3 x z := by decide
theorem Rm3_sub : ∀ x y : Fin 3, Rm3 x y → x ≤ y := by decide
theorem Rm3_to_two : ∀ v : Fin 3, 1 ≤ v → Rm3 v 2 := by decide
theorem Fin3_hered_F : ∀ x y : Fin 3, x ≤ y → x = 2 → y = 2 := by decide
theorem Fin3_hered_V : ∀ x y : Fin 3, x ≤ y → 1 ≤ x → 1 ≤ y := by decide
theorem Fin3_full : ∀ x : Fin 3, x = 2 → 1 ≤ x := by decide
theorem Fin3_ne_two : ∀ v : Fin 3, ¬ (v = 2) → v ≤ 1 := by decide

/-- The three-world separating model. -/
@[reducible] def M3 : ConstraintModel where
  W := Fin 3
  Ri x y := x ≤ y
  Rm := Rm3
  F := {x | x = 2}
  V _ := {x | 1 ≤ x}
  refl_i x := le_refl x
  trans_i {x y z} h1 h2 := le_trans h1 h2
  refl_m := Rm3_refl
  trans_m {x y z} h1 h2 := Rm3_trans x y z h1 h2
  sub_mi {x y} h := Rm3_sub x y h
  hered_F {x y} h hx := Fin3_hered_F x y h hx
  hered_V {_ x y} h hx := Fin3_hered_V x y h hx
  full_F {_ x} hx := Fin3_full x hx

/-- `◯⊥` holds from world `1` upwards: the edge `1 ⇝ 2` lands in `F`. -/
theorem M3_oBot_of_one {x : Fin 3} (h : (1 : Fin 3) ≤ x) : M3.force x oBot := by
  intro v hv
  exact ⟨2, Rm3_to_two v (le_trans h hv), rfl⟩

/-- `◯⊥` fails at the root: `0`'s only `Rₘ`-successor is `0`. -/
theorem M3_not_oBot_zero : ¬ M3.force (0 : Fin 3) oBot := by
  intro h
  obtain ⟨u, hu, hf⟩ := h 0 (le_refl _)
  have : u = 2 := hf
  subst this
  exact absurd hu (by decide)

/-- `φmix` holds at the root of `M3`. -/
theorem M3_force_phiMix : M3.force (0 : Fin 3) phiMix := by
  refine ⟨?_, ?_⟩
  · intro v _ hp
    exact M3_oBot_of_one hp
  · intro v _ hnp
    by_contra hne
    have h1 : M3.Ri v 1 := Fin3_ne_two v hne
    have hcon : (1 : Fin 3) = 2 := hnp 1 h1 (le_refl (1 : Fin 3))
    exact absurd hcon (by decide)

/-- **`φmix ⊬ ◯⊥`.** -/
theorem phiMix_not_oBot : ¬ Deriv [phiMix] oBot := by
  rintro ⟨d⟩
  refine M3_not_oBot_zero (soundness d M3 0 ?_)
  intro ψ hψ
  have e : ψ = phiMix := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  exact M3_force_phiMix

theorem inst_top_phiMix :
    inst truePLL phiMix
      = (truePLL.ifThen oBot).and ((truePLL.ifThen PLLFormula.falsePLL).ifThen
          PLLFormula.falsePLL) := by decide

theorem inst_bot_phiMix :
    inst PLLFormula.falsePLL phiMix
      = ((PLLFormula.falsePLL : PLLFormula).ifThen oBot).and
          (((PLLFormula.falsePLL : PLLFormula).ifThen PLLFormula.falsePLL).ifThen
            PLLFormula.falsePLL) := by decide

/-- **`θ = ⊤` does not cover `φmix`**: `φmix[p:=⊤] ⊢ ◯⊥`. -/
theorem phiMix_top_fails : ¬ Deriv [phiMix] (inst truePLL phiMix) := by
  intro h
  refine phiMix_not_oBot (Deriv.cutHead h ?_)
  rw [inst_top_phiMix]
  exact Deriv.impElim (Deriv.andElim1 (Deriv.iden (.head _))) topD

/-- **`θ = ⊥` does not cover `φmix`**: `φmix[p:=⊥] ⊢ ⊥`. -/
theorem phiMix_bot_fails : ¬ Deriv [phiMix] (inst PLLFormula.falsePLL phiMix) := by
  intro h
  refine phiMix_not_oBot (Deriv.cutHead h ?_)
  rw [inst_bot_phiMix]
  refine Deriv.falsoElim _ ?_
  exact Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
    (Deriv.impIntro (Deriv.iden (.head _)))

/-- **The two-point cover `S = [⊤, ⊥]` fails as well.**  So the cover
conjecture has real content: no fixed finite pool of substitutions
independent of `φ` can serve. -/
theorem phiMix_no_boolean_cover :
    ¬ Deriv [phiMix] (bigOr (instList [truePLL, PLLFormula.falsePLL] phiMix)) := by
  intro h
  refine phiMix_not_oBot (Deriv.cutHead h ?_)
  show Deriv [(inst truePLL phiMix).or
    ((inst PLLFormula.falsePLL phiMix).or PLLFormula.falsePLL)] oBot
  refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
  · rw [inst_top_phiMix]
    exact Deriv.impElim (Deriv.andElim1 (Deriv.iden (.head _))) topD
  · refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · rw [inst_bot_phiMix]
      refine Deriv.falsoElim _ ?_
      exact Deriv.impElim (Deriv.andElim2 (Deriv.iden (.head _)))
        (Deriv.impIntro (Deriv.iden (.head _)))
    · exact Deriv.falsoElim _ (Deriv.iden (.head _))

/-- `φmix` is consistent — the interpolant `¬¬◯⊥` is not `⊥`. -/
theorem phiMix_consistent : ¬ Deriv [phiMix] PLLFormula.falsePLL := by
  rintro ⟨d⟩
  have hs := soundness d M3 0 (fun ψ hψ => by
    have e : ψ = phiMix := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact M3_force_phiMix)
  have hcon : (0 : Fin 3) = 2 := hs
  exact absurd hcon (by decide)

/-! ## 9.  UI PROVED for the ◯-free one-variable fragment

For `◯`-free `φ` the cover conjecture holds with a ONE-element cover,
and the interpolant is always `⊤` or `⊥`:

    φ ⊢ ⊥        ⟹  ∃p.φ = ⊥
    φ ⊬ ⊥        ⟹  ⊢ φ[p := ⊤]  or  ⊢ φ[p := ⊥],  so  ∃p.φ = ⊤.

The proof is semantic and needs no maximal worlds.  Take a world `w`
with `w ⊩ φ`, `w ∉ F` (FMP, `countermodel_of_not_deriv`).  Split on
whether some non-fallible `v ≥ᵢ w` forces `p`.

* If yes, at that `m` the atom `p` holds throughout `≥ᵢ m` by heredity,
  so `p` and `⊤` are interchangeable there (`force_inst_congr`), giving
  `m ⊩ φ[p := ⊤]`, with `m ∉ F`.
* If no, then above `w` the atom `p` holds exactly at the fallible
  worlds — which is where `⊥` holds — so `p` and `⊥` are
  interchangeable there, giving `w ⊩ φ[p := ⊥]`, with `w ∉ F`.

Either way a variable-free `◯`-free formula is forced at a
non-fallible world; such a formula is a theorem (`thm_of_force_nf`,
via the classical two-valued evaluation `evalCl`), and `postInterp_top`
finishes. -/

/-- Classical two-valued evaluation, correct on variable-free `◯`-free
formulas. -/
def evalCl : PLLFormula → Bool
  | .prop _ => false
  | .falsePLL => false
  | .and A B => evalCl A && evalCl B
  | .or A B => evalCl A || evalCl B
  | .ifThen A B => !(evalCl A) || evalCl B
  | .somehow A => evalCl A

/-- **Two-valuedness of the variable-free `◯`-free fragment**: such a
formula is either a theorem or refutable, as `evalCl` says. -/
theorem evalCl_sound : ∀ {A : PLLFormula}, atomFree A = true → boxFree A = true →
    (evalCl A = true → Deriv [] A) ∧
    (evalCl A = false → Deriv [A] PLLFormula.falsePLL) := by
  intro A
  induction A with
  | prop a => intro ha _; exact absurd ha (by simp [atomFree])
  | falsePLL =>
      intro _ _
      exact ⟨fun h => absurd h (by simp [evalCl]), fun _ => Deriv.iden (.head _)⟩
  | and A B ihA ihB =>
      intro ha hb
      have ha' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using ha
      have hb' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hb
      obtain ⟨pA, nA⟩ := ihA ha'.1 hb'.1
      obtain ⟨pB, nB⟩ := ihB ha'.2 hb'.2
      constructor
      · intro h
        have h' : evalCl A = true ∧ evalCl B = true := by
          simpa [evalCl, Bool.and_eq_true] using h
        exact Deriv.andIntro (pA h'.1) (pB h'.2)
      · intro h
        have h' : evalCl A = false ∨ evalCl B = false := by
          rcases hA : evalCl A with _ | _
          · exact Or.inl rfl
          · rcases hB : evalCl B with _ | _
            · exact Or.inr rfl
            · exact absurd h (by simp [evalCl, hA, hB])
        rcases h' with h' | h'
        · exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) (nA h')
        · exact Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) (nB h')
  | or A B ihA ihB =>
      intro ha hb
      have ha' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using ha
      have hb' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hb
      obtain ⟨pA, nA⟩ := ihA ha'.1 hb'.1
      obtain ⟨pB, nB⟩ := ihB ha'.2 hb'.2
      constructor
      · intro h
        have h' : evalCl A = true ∨ evalCl B = true := by
          rcases hA : evalCl A with _ | _
          · rcases hB : evalCl B with _ | _
            · exact absurd h (by simp [evalCl, hA, hB])
            · exact Or.inr rfl
          · exact Or.inl rfl
        rcases h' with h' | h'
        · exact Deriv.orIntro1 (pA h')
        · exact Deriv.orIntro2 (pB h')
      · intro h
        have h' : evalCl A = false ∧ evalCl B = false := by
          simpa [evalCl, Bool.or_eq_false_iff] using h
        exact Deriv.orElim (Deriv.iden (.head _))
          (Deriv.toHead (nA h'.1)) (Deriv.toHead (nB h'.2))
  | ifThen A B ihA ihB =>
      intro ha hb
      have ha' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using ha
      have hb' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using hb
      obtain ⟨pA, nA⟩ := ihA ha'.1 hb'.1
      obtain ⟨pB, nB⟩ := ihB ha'.2 hb'.2
      constructor
      · intro h
        have h' : evalCl A = false ∨ evalCl B = true := by
          rcases hA : evalCl A with _ | _
          · exact Or.inl rfl
          · rcases hB : evalCl B with _ | _
            · exact absurd h (by simp [evalCl, hA, hB])
            · exact Or.inr rfl
        rcases h' with h' | h'
        · exact Deriv.impIntro (Deriv.falsoElim B (nA h'))
        · exact Deriv.impIntro ((pB h').rename (by simp))
      · intro h
        have h' : evalCl A = true ∧ evalCl B = false := by
          rcases hA : evalCl A with _ | _
          · exact absurd h (by simp [evalCl, hA])
          · rcases hB : evalCl B with _ | _
            · exact ⟨rfl, rfl⟩
            · exact absurd h (by simp [evalCl, hA, hB])
        exact Deriv.cutHead
          (Deriv.impElim (Deriv.iden (.head _)) ((pA h'.1).rename (by simp)))
          (nB h'.2)
  | somehow A _ => intro _ hb; exact absurd hb (by simp [boxFree])

/-- A variable-free `◯`-free formula forced at a NON-fallible world is
a theorem. -/
theorem thm_of_force_nf {C : ConstraintModel} {A : PLLFormula}
    (ha : atomFree A = true) (hb : boxFree A = true) {w : C.W}
    (hw : C.force w A) (hF : ¬ C.force w PLLFormula.falsePLL) : Deriv [] A := by
  obtain ⟨h1, h2⟩ := evalCl_sound ha hb
  rcases hev : evalCl A with _ | _
  · exfalso
    obtain ⟨d⟩ := h2 hev
    refine hF (soundness d C w ?_)
    intro ψ hψ
    have e : ψ = A := by
      cases hψ with
      | head => rfl
      | tail _ h => cases h
    subst e
    exact hw
  · exact h1 hev

/-- **Replacement.**  If `p` and `θ` are interchangeable everywhere
above `m`, then so are `A` and `A[p := θ]`, for EVERY `A` (the `◯`
clause stays inside the `Rᵢ`-cone because `Rₘ ⊆ Rᵢ`). -/
theorem force_inst_congr {C : ConstraintModel} {m : C.W} {θ : PLLFormula}
    (h : ∀ v : C.W, C.Ri m v →
      (C.force v (PLLFormula.prop pv) ↔ C.force v θ)) :
    ∀ (A : PLLFormula) (v : C.W), C.Ri m v →
      (C.force v A ↔ C.force v (inst θ A)) := by
  intro A
  induction A with
  | prop a =>
      intro v hv
      by_cases ha : a = pv
      · subst ha; rw [inst_var_eq]; exact h v hv
      · rw [show inst θ (PLLFormula.prop a) = PLLFormula.prop a from by
              show (if a = pv then θ else PLLFormula.prop a) = _
              rw [if_neg ha]]
  | falsePLL => intro _ _; exact Iff.rfl
  | and A B ihA ihB => intro v hv; exact and_congr (ihA v hv) (ihB v hv)
  | or A B ihA ihB => intro v hv; exact or_congr (ihA v hv) (ihB v hv)
  | ifThen A B ihA ihB =>
      intro v hv
      show (∀ u, C.Ri v u → C.force u A → C.force u B) ↔
        (∀ u, C.Ri v u → C.force u (inst θ A) → C.force u (inst θ B))
      constructor
      · intro hh u hu hA
        exact (ihB u (C.trans_i hv hu)).mp
          (hh u hu ((ihA u (C.trans_i hv hu)).mpr hA))
      · intro hh u hu hA
        exact (ihB u (C.trans_i hv hu)).mpr
          (hh u hu ((ihA u (C.trans_i hv hu)).mp hA))
  | somehow A ih =>
      intro v hv
      show (∀ u, C.Ri v u → ∃ y, C.Rm u y ∧ C.force y A) ↔
        (∀ u, C.Ri v u → ∃ y, C.Rm u y ∧ C.force y (inst θ A))
      constructor
      · intro hh u hu
        obtain ⟨y, hy, hfy⟩ := hh u hu
        exact ⟨y, hy, (ih y (C.trans_i (C.trans_i hv hu) (C.sub_mi hy))).mp hfy⟩
      · intro hh u hu
        obtain ⟨y, hy, hfy⟩ := hh u hu
        exact ⟨y, hy, (ih y (C.trans_i (C.trans_i hv hu) (C.sub_mi hy))).mpr hfy⟩

/-- Substitution of a `◯`-free formula preserves `◯`-freeness. -/
theorem boxFree_inst {θ : PLLFormula} (hθ : boxFree θ = true) :
    ∀ {A : PLLFormula}, boxFree A = true → boxFree (inst θ A) = true
  | .prop a, _ => by
      by_cases ha : a = pv
      · subst ha; rw [inst_var_eq]; exact hθ
      · rw [show inst θ (PLLFormula.prop a) = PLLFormula.prop a from by
              show (if a = pv then θ else PLLFormula.prop a) = _
              rw [if_neg ha]]
        rfl
  | .falsePLL, _ => rfl
  | .and A B, h => by
      have h' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using h
      show (boxFree (inst θ A) && boxFree (inst θ B)) = true
      rw [boxFree_inst hθ h'.1, boxFree_inst hθ h'.2]; rfl
  | .or A B, h => by
      have h' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using h
      show (boxFree (inst θ A) && boxFree (inst θ B)) = true
      rw [boxFree_inst hθ h'.1, boxFree_inst hθ h'.2]; rfl
  | .ifThen A B, h => by
      have h' : boxFree A = true ∧ boxFree B = true := by
        simpa [boxFree, Bool.and_eq_true] using h
      show (boxFree (inst θ A) && boxFree (inst θ B)) = true
      rw [boxFree_inst hθ h'.1, boxFree_inst hθ h'.2]; rfl
  | .somehow _, h => absurd h (by simp [boxFree])

/-- **`◯`-FREE UI, `∃`-side — PROVED.**  Every `◯`-free one-variable
`φ` has a uniform post-interpolant over the variable-free fragment,
namely `⊥` if `φ` is inconsistent and `⊤` otherwise. -/
theorem postInterp_of_boxFree {φ : PLLFormula} (hv : onlyPv φ = true)
    (hb : boxFree φ = true) : ∃ ψ, IsPostInterp φ ψ := by
  classical
  by_cases hc : Deriv [φ] PLLFormula.falsePLL
  · exact ⟨PLLFormula.falsePLL, rfl, hc,
      fun _ _ _ => Deriv.falsoElim _ (Deriv.iden (.head _))⟩
  obtain ⟨C, -, w, hw, hwF⟩ := countermodel_of_not_deriv hc
  refine ⟨truePLL, ?_⟩
  by_cases hex : ∃ v : C.W, C.Ri w v ∧ C.force v (PLLFormula.prop pv) ∧
      ¬ C.force v PLLFormula.falsePLL
  · obtain ⟨m, hwm, hmp, hmF⟩ := hex
    have hcong : ∀ v : C.W, C.Ri m v →
        (C.force v (PLLFormula.prop pv) ↔ C.force v truePLL) := by
      intro v hv'
      exact ⟨fun _ _ _ hbot => hbot, fun _ => C.force_hered hv' hmp⟩
    have hmφ : C.force m (inst truePLL φ) :=
      (force_inst_congr hcong φ m (C.refl_i m)).mp (C.force_hered hwm hw)
    exact postInterp_top (θ := truePLL) rfl
      (thm_of_force_nf (inst_atomFree rfl hv) (boxFree_inst rfl hb) hmφ hmF)
  · have hall : ∀ v : C.W, C.Ri w v → C.force v (PLLFormula.prop pv) →
        C.force v PLLFormula.falsePLL := by
      intro v hv' hp
      by_contra hcon
      exact hex ⟨v, hv', hp, hcon⟩
    have hcong : ∀ v : C.W, C.Ri w v →
        (C.force v (PLLFormula.prop pv) ↔ C.force v PLLFormula.falsePLL) := by
      intro v hv'
      exact ⟨hall v hv', fun hbot => C.force_of_fallible hbot⟩
    have hwφ : C.force w (inst PLLFormula.falsePLL φ) :=
      (force_inst_congr hcong φ w (C.refl_i w)).mp hw
    exact postInterp_top (θ := PLLFormula.falsePLL) rfl
      (thm_of_force_nf (inst_atomFree rfl hv) (boxFree_inst rfl hb) hwφ hwF)

/-- The cover conjecture holds on the `◯`-free fragment, with a
one-element cover. -/
theorem hasCover_of_boxFree {φ : PLLFormula} (hv : onlyPv φ = true)
    (hb : boxFree φ = true) : HasCover φ := by
  classical
  by_cases hc : Deriv [φ] PLLFormula.falsePLL
  · refine ⟨[PLLFormula.falsePLL], ?_, ?_⟩
    · intro θ hθ
      rcases List.mem_singleton.mp hθ with rfl
      rfl
    · exact Deriv.orIntro1 (Deriv.falsoElim _ hc)
  obtain ⟨C, -, w, hw, hwF⟩ := countermodel_of_not_deriv hc
  by_cases hex : ∃ v : C.W, C.Ri w v ∧ C.force v (PLLFormula.prop pv) ∧
      ¬ C.force v PLLFormula.falsePLL
  · obtain ⟨m, hwm, hmp, hmF⟩ := hex
    have hcong : ∀ v : C.W, C.Ri m v →
        (C.force v (PLLFormula.prop pv) ↔ C.force v truePLL) := by
      intro v hv'
      exact ⟨fun _ _ _ hbot => hbot, fun _ => C.force_hered hv' hmp⟩
    have hmφ : C.force m (inst truePLL φ) :=
      (force_inst_congr hcong φ m (C.refl_i m)).mp (C.force_hered hwm hw)
    have hthm : Deriv [] (inst truePLL φ) :=
      thm_of_force_nf (inst_atomFree rfl hv) (boxFree_inst rfl hb) hmφ hmF
    exact ⟨[truePLL], by
      intro θ hθ; rcases List.mem_singleton.mp hθ with rfl; rfl,
      Deriv.orIntro1 (hthm.rename (by simp))⟩
  · have hall : ∀ v : C.W, C.Ri w v → C.force v (PLLFormula.prop pv) →
        C.force v PLLFormula.falsePLL := by
      intro v hv' hp
      by_contra hcon
      exact hex ⟨v, hv', hp, hcon⟩
    have hcong : ∀ v : C.W, C.Ri w v →
        (C.force v (PLLFormula.prop pv) ↔ C.force v PLLFormula.falsePLL) := by
      intro v hv'
      exact ⟨hall v hv', fun hbot => C.force_of_fallible hbot⟩
    have hwφ : C.force w (inst PLLFormula.falsePLL φ) :=
      (force_inst_congr hcong φ w (C.refl_i w)).mp hw
    have hthm : Deriv [] (inst PLLFormula.falsePLL φ) :=
      thm_of_force_nf (inst_atomFree rfl hv) (boxFree_inst rfl hb) hwφ hwF
    exact ⟨[PLLFormula.falsePLL], by
      intro θ hθ; rcases List.mem_singleton.mp hθ with rfl; rfl,
      Deriv.orIntro1 (hthm.rename (by simp))⟩

/-! ## 10.  REFUTED: the `∀`-side meet-cover method is incomplete

`MeetCoverConj` is FALSE.  Witness: `wem = p ∨ ¬p`.  Every
variable-free instance `wem[p := θ]` is `θ ∨ ¬θ`, and in the two-world
fallible-free model

    N :  0 ⊑ 1,   Rₘ = id,   F = ∅,   V(a) = {1}

every variable-free formula has the same truth value at `0` and at `1`
(`N_uniform` — the two worlds are indistinguishable without atoms), so
`θ ∨ ¬θ` holds at `0` for EVERY variable-free `θ`, while `p ∨ ¬p`
fails at `0`.  Hence no finite meet of instances entails `wem`.

This refutes the METHOD on the `∀`-side, not `∀p` itself: whether
`p ∨ ¬p` has a uniform pre-interpolant (`⊥` is the natural candidate)
is left OPEN here. -/

theorem Fin2_cases : ∀ v : Fin 2, v = 0 ∨ v = 1 := by decide
theorem Fin2_hered_V : ∀ x y : Fin 2, x ≤ y → 1 ≤ x → 1 ≤ y := by decide

/-- The two-world fallible-free model. -/
@[reducible] def N : ConstraintModel where
  W := Fin 2
  Ri x y := x ≤ y
  Rm x y := x = y
  F := {_x | False}
  V _ := {x | 1 ≤ x}
  refl_i x := le_refl x
  trans_i {x y z} h1 h2 := le_trans h1 h2
  refl_m _ := rfl
  trans_m {_ _ _} h1 h2 := h1.trans h2
  sub_mi {x y} h := le_of_eq h
  hered_F {_ _} _ hx := hx
  hered_V {_ x y} h hx := Fin2_hered_V x y h hx
  full_F {_ _} hx := hx.elim

/-- **The two worlds of `N` are indistinguishable to the variable-free
fragment.** -/
theorem N_uniform : ∀ {A : PLLFormula}, atomFree A = true →
    (N.force (0 : Fin 2) A ↔ N.force (1 : Fin 2) A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _; exact Iff.rfl
  | and A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact and_congr (ihA h'.1) (ihB h'.2)
  | or A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact or_congr (ihA h'.1) (ihB h'.2)
  | ifThen A B ihA ihB =>
      intro h
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      constructor
      · intro hh
        exact N.force_hered (show N.Ri 0 1 by decide) hh
      · intro hh u hu hA
        rcases Fin2_cases u with rfl | rfl
        · exact (ihB h'.2).mpr (hh 1 (le_refl (1 : Fin 2)) ((ihA h'.1).mp hA))
        · exact hh 1 (le_refl (1 : Fin 2)) hA
  | somehow A ih =>
      intro h
      constructor
      · intro hh
        exact N.force_hered (show N.Ri 0 1 by decide) hh
      · intro hh u _
        rcases Fin2_cases u with rfl | rfl
        · obtain ⟨y, hy, hfy⟩ := hh 1 (le_refl (1 : Fin 2))
          have hy1 : (1 : Fin 2) = y := hy
          subst hy1
          exact ⟨0, rfl, (ih h).mpr hfy⟩
        · exact hh 1 (le_refl (1 : Fin 2))

/-- Weak excluded middle for the variable, `p ∨ ¬p`. -/
def wemP : PLLFormula := (PLLFormula.prop pv).or (nt (PLLFormula.prop pv))

theorem wemP_onlyPv : onlyPv wemP = true := by decide

theorem inst_wemP (θ : PLLFormula) : inst θ wemP = θ.or (nt θ) := by
  show (inst θ (PLLFormula.prop pv)).or
    ((inst θ (PLLFormula.prop pv)).ifThen PLLFormula.falsePLL) = _
  rw [inst_var_eq]
  rfl

/-- Every variable-free instance `θ ∨ ¬θ` holds at the root of `N`. -/
theorem N_force_inst_wemP {θ : PLLFormula} (hθ : atomFree θ = true) :
    N.force (0 : Fin 2) (inst θ wemP) := by
  classical
  rw [inst_wemP]
  by_cases h0 : N.force (0 : Fin 2) θ
  · exact Or.inl h0
  · refine Or.inr ?_
    intro u _ hθu
    rcases Fin2_cases u with rfl | rfl
    · exact absurd hθu h0
    · exact absurd ((N_uniform hθ).mpr hθu) h0

/-- `p ∨ ¬p` fails at the root of `N`. -/
theorem N_not_wemP : ¬ N.force (0 : Fin 2) wemP := by
  intro h
  rcases h with hp | hn
  · have h' : (1 : Fin 2) ≤ 0 := hp
    exact absurd h' (by decide)
  · exact hn 1 (show N.Ri 0 1 by decide) (le_refl (1 : Fin 2))

/-- **`p ∨ ¬p` has NO finite variable-free substitution meet-cover.** -/
theorem wemP_no_meetCover : ¬ HasMeetCover wemP := by
  rintro ⟨S, hS, ⟨d⟩⟩
  refine N_not_wemP (soundness d N 0 ?_)
  intro ψ hψ
  have e : ψ = bigAnd (instList S wemP) := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  refine force_bigAnd ?_
  intro A hA
  obtain ⟨θ, hθ, rfl⟩ := mem_instList hA
  exact N_force_inst_wemP (hS θ hθ)

/-- **REFUTED**: not every one-variable formula has a variable-free
substitution meet-cover.  The `∀`-side of the method is incomplete. -/
theorem meetCoverConj_false : ¬ MeetCoverConj :=
  fun h => wemP_no_meetCover (h wemP wemP_onlyPv)

/-! ## 11.  The pre-interpolant `wem` DOES have exists — it is `⊥`

The meet-cover method misses it, but `∀p.(p ∨ ¬p)` exists: it is `⊥`.

The proof is a DOUBLING construction.  Given a variable-free `χ` with
`χ ⊬ ⊥`, take a model world `w ⊩ χ`, `w ∉ F`, and replace the model by
two vertical copies of itself,

    dbl C :  W × Fin 2,  Rᵢ = Rᵢ × (≤),  Rₘ = Rₘ × (=),  F = F × Fin 2,
             V(a) = upper copy ∪ F.

Variable-free formulas cannot see the second coordinate
(`dbl_transfer`: the `⊃` and `◯` clauses quantify over the extra layer
but the layer index can always be instantiated at its own value), so
`χ` still holds at `(w,0)`.  But `p` now holds at `(w,1)` and not at
`(w,0)`, so `p ∨ ¬p` fails at `(w,0)`.  Hence `χ ⊬ p ∨ ¬p`. -/

theorem Fin2_up : ∀ i j : Fin 2, i ≤ j → i = 1 → j = 1 := by decide

/-- The doubling of a constraint model, with `p` decorated to hold
exactly on the upper copy (plus the fallible worlds). -/
@[reducible] def dbl (C : ConstraintModel) : ConstraintModel where
  W := C.W × Fin 2
  Ri a b := C.Ri a.1 b.1 ∧ a.2 ≤ b.2
  Rm a b := C.Rm a.1 b.1 ∧ a.2 = b.2
  F := {a | a.1 ∈ C.F}
  V _ := {a | a.2 = 1 ∨ a.1 ∈ C.F}
  refl_i a := ⟨C.refl_i a.1, le_refl a.2⟩
  trans_i {_ _ _} h1 h2 := ⟨C.trans_i h1.1 h2.1, le_trans h1.2 h2.2⟩
  refl_m a := ⟨C.refl_m a.1, rfl⟩
  trans_m {_ _ _} h1 h2 := ⟨C.trans_m h1.1 h2.1, h1.2.trans h2.2⟩
  sub_mi {_ _} h := ⟨C.sub_mi h.1, le_of_eq h.2⟩
  hered_F {_ _} h hx := C.hered_F h.1 hx
  hered_V {_ x y} h hx :=
    hx.elim (fun h1 => Or.inl (Fin2_up x.2 y.2 h.2 h1))
      (fun h1 => Or.inr (C.hered_F h.1 h1))
  full_F {_ _} hx := Or.inr hx

/-- **Variable-free formulas cannot see the doubling.** -/
theorem dbl_transfer {C : ConstraintModel} :
    ∀ {A : PLLFormula}, atomFree A = true →
      ∀ (x : C.W) (i : Fin 2), ((dbl C).force (x, i) A ↔ C.force x A) := by
  intro A
  induction A with
  | prop a => intro h; exact absurd h (by simp [atomFree])
  | falsePLL => intro _ _ _; exact Iff.rfl
  | and A B ihA ihB =>
      intro h x i
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact and_congr (ihA h'.1 x i) (ihB h'.2 x i)
  | or A B ihA ihB =>
      intro h x i
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      exact or_congr (ihA h'.1 x i) (ihB h'.2 x i)
  | ifThen A B ihA ihB =>
      intro h x i
      have h' : atomFree A = true ∧ atomFree B = true := by
        simpa [atomFree, Bool.and_eq_true] using h
      show (∀ b : C.W × Fin 2, (dbl C).Ri (x, i) b →
            (dbl C).force b A → (dbl C).force b B) ↔
        (∀ v : C.W, C.Ri x v → C.force v A → C.force v B)
      constructor
      · intro hh v hv hA
        exact (ihB h'.2 v i).mp
          (hh (v, i) ⟨hv, le_refl i⟩ ((ihA h'.1 v i).mpr hA))
      · intro hh b hb hA
        exact (ihB h'.2 b.1 b.2).mpr
          (hh b.1 hb.1 ((ihA h'.1 b.1 b.2).mp hA))
  | somehow A ih =>
      intro h x i
      show (∀ b : C.W × Fin 2, (dbl C).Ri (x, i) b →
            ∃ u, (dbl C).Rm b u ∧ (dbl C).force u A) ↔
        (∀ v : C.W, C.Ri x v → ∃ u, C.Rm v u ∧ C.force u A)
      constructor
      · intro hh v hv
        obtain ⟨u, hu, hfu⟩ := hh (v, i) ⟨hv, le_refl i⟩
        exact ⟨u.1, hu.1, (ih h u.1 u.2).mp hfu⟩
      · intro hh b hb
        obtain ⟨u, hu, hfu⟩ := hh b.1 hb.1
        exact ⟨(u, b.2), ⟨hu, rfl⟩, (ih h u b.2).mpr hfu⟩

/-- `p ∨ ¬p` fails at the lower copy of a non-fallible world. -/
theorem dbl_not_wemP {C : ConstraintModel} {w : C.W}
    (hw : ¬ C.force w PLLFormula.falsePLL) :
    ¬ (dbl C).force ((w, 0) : C.W × Fin 2) wemP := by
  intro h
  rcases h with hp | hn
  · rcases (hp : ((0 : Fin 2) = 1 ∨ w ∈ C.F)) with h0 | hF
    · have h0' : (0 : Fin 2) = 1 := h0
      exact absurd h0' (by decide)
    · exact hw hF
  · have hle : (0 : Fin 2) ≤ 1 := by decide
    refine hw (hn (w, 1) ⟨C.refl_i w, hle⟩ ?_)
    exact Or.inl rfl

/-- **`∀p.(p ∨ ¬p) = ⊥`.**  So the `∀`-side uniform interpolant of
`wem` EXISTS; `wemP_no_meetCover` shows the meet-cover method cannot
produce it.  The method is incomplete, uniform interpolation is not
touched. -/
theorem preInterp_wemP : IsPreInterp wemP PLLFormula.falsePLL := by
  classical
  refine ⟨rfl, Deriv.falsoElim _ (Deriv.iden (.head _)), ?_⟩
  intro χ hχ hd
  by_contra hcon
  obtain ⟨C, -, w, hw, hwF⟩ := countermodel_of_not_deriv hcon
  obtain ⟨d⟩ := hd
  refine dbl_not_wemP hwF (soundness d (dbl C) (w, 0) ?_)
  intro ψ hψ
  have e : ψ = χ := by
    cases hψ with
    | head => rfl
    | tail _ h => cases h
  subst e
  exact (dbl_transfer hχ w 0).mpr hw

/-! ## 12.  The `∃`-side conjecture survives both countermodels

Neither witness of this file damages `CoverConj`: `φmix`, which defeats
the fixed Boolean pool, has the one-element cover `[◯⊥]`; and `wem`,
which defeats the whole `∀`-side method, has the one-element cover
`[⊤]`.  A further indication: in the two-world model `N`, ANY `φ`
forced at the root is forced there again under the constant-`⊤`
valuation (heredity to world `1`, then indistinguishability of the two
worlds when `p` is everywhere true), so `N` cannot refute a cover
either. -/

theorem hasCover_phiMix : HasCover phiMix :=
  ⟨[oBot], by
      intro θ hθ
      rcases List.mem_singleton.mp hθ with rfl
      rfl,
   Deriv.orIntro1 phiMix_cover⟩

theorem hasCover_wemP : HasCover wemP :=
  hasCover_of_boxFree wemP_onlyPv (by decide)

/-! ## 13.  Axiom audit -/

/-- info: 'PLLND.RNEmbed.inst_below' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inst_below

/-- info: 'PLLND.RNEmbed.inst_above' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inst_above

/-- info: 'PLLND.RNEmbed.postInterp_of_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_cover

/-- info: 'PLLND.RNEmbed.preInterp_of_cover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preInterp_of_cover

/-- info: 'PLLND.RNEmbed.postUI_of_coverConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postUI_of_coverConj

/-- info: 'PLLND.RNEmbed.preUI_of_meetCoverConj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms preUI_of_meetCoverConj

/-- info: 'PLLND.RNEmbed.subst_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subst_mono

/-- info: 'PLLND.RNEmbed.postInterp_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_pos

/-- info: 'PLLND.RNEmbed.postInterp_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_neg

/-- info: 'PLLND.RNEmbed.preInterp_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preInterp_of_pos

/-- info: 'PLLND.RNEmbed.preInterp_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preInterp_of_neg

/-- info: 'PLLND.RNEmbed.UI_of_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UI_of_pure

/-- info: 'PLLND.RNEmbed.postInterp_or' depends on axioms: [propext] -/
#guard_msgs in
#print axioms postInterp_or

/-- info: 'PLLND.RNEmbed.postInterp_andClosed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms postInterp_andClosed

/-- info: 'PLLND.RNEmbed.preInterp_and' depends on axioms: [propext] -/
#guard_msgs in
#print axioms preInterp_and

/-- info: 'PLLND.RNEmbed.preInterp_impClosed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms preInterp_impClosed

/-- info: 'PLLND.RNEmbed.exists_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_p

/-- info: 'PLLND.RNEmbed.forall_box_p' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms forall_box_p

/-- info: 'PLLND.RNEmbed.exists_exLadder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_exLadder

/-- info: 'PLLND.RNEmbed.exists_phiMix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms exists_phiMix

/-- info: 'PLLND.RNEmbed.phiMix_not_oBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiMix_not_oBot

/-- info: 'PLLND.RNEmbed.phiMix_top_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiMix_top_fails

/-- info: 'PLLND.RNEmbed.phiMix_bot_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiMix_bot_fails

/-- info: 'PLLND.RNEmbed.phiMix_no_boolean_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiMix_no_boolean_cover

/-- info: 'PLLND.RNEmbed.phiMix_consistent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms phiMix_consistent

/-- info: 'PLLND.RNEmbed.evalCl_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalCl_sound

/-- info: 'PLLND.RNEmbed.thm_of_force_nf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms thm_of_force_nf

/-- info: 'PLLND.RNEmbed.force_inst_congr' does not depend on any axioms -/
#guard_msgs in
#print axioms force_inst_congr

/-- info: 'PLLND.RNEmbed.postInterp_of_boxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postInterp_of_boxFree

/-- info: 'PLLND.RNEmbed.hasCover_of_boxFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasCover_of_boxFree

/-- info: 'PLLND.RNEmbed.N_uniform' depends on axioms: [propext] -/
#guard_msgs in
#print axioms N_uniform

/-- info: 'PLLND.RNEmbed.wemP_no_meetCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wemP_no_meetCover

/-- info: 'PLLND.RNEmbed.meetCoverConj_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms meetCoverConj_false

/-- info: 'PLLND.RNEmbed.dbl_transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms dbl_transfer

/-- info: 'PLLND.RNEmbed.preInterp_wemP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms preInterp_wemP

end RNEmbed
end PLLND
