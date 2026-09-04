import LaxLogic.PLLNDCore
import Mathlib.Tactic

/-!
# Derivability from sets of hypotheses, and admissible rules

Infrastructure for the completeness proof (`PLLCompleteness.lean`): theories
are *sets* of formulas, so we need derivability `Γ ⊩ φ` where `Γ : Set
PLLFormula` — some finite list of hypotheses drawn from `Γ` derives `φ` —
together with the admissible rules Fairtlough–Mendler call "structural
reasoning": cut, the deduction theorem, reasoning under finite disjunctions
(`bigOr`), and the two PLL-specific lemmas
`(N ⊃ ◯X) → (◯N ⊃ ◯X)` and `K ∨ ◯L ⊃ ◯(K ∨ L)`.

Everything stays cast-free: list-level rules are recursive functions on
derivations (membership-based `iden` means contexts only ever need
`LaxND.rename`), and set-level rules are `Prop`.
-/

open PLLFormula

namespace PLLND

/-! ### Finite disjunctions

`bigOr [] = ⊥` is a junk value: all uses in the completeness proof are guarded
by nonemptiness, and where it does leak in (`bigOrElim` on `[]`) falsity
elimination gives the right logic anyway. -/

@[simp]
def bigOr : List PLLFormula → PLLFormula
  | [] => .falsePLL
  | φ :: L => φ.or (bigOr L)

/-! ### List-level admissible rules (cast-free recursion on derivations) -/

namespace LaxND

/-- Cut: substitute a derivation for a hypothesis. -/
def cut {L L' : List PLLFormula} {φ ψ : PLLFormula}
    (p₁ : LaxND L φ) (p₂ : LaxND (φ :: L') ψ) : LaxND (L ++ L') ψ :=
  .impElim
    (.impIntro (p₂.rename (by
      intro χ h
      simp only [List.mem_cons, List.mem_append] at h ⊢
      exact h.imp id .inr)))
    (p₁.rename (by intro χ h; exact List.mem_append.mpr (.inl h)))

/-- Introduce a finite disjunction at any disjunct.  (`Prop`-level:
the membership hypothesis is a `Prop`, so it can only be matched when
eliminating into `Prop`.) -/
theorem bigOrIntro {L : List PLLFormula} {φ : PLLFormula} :
    ∀ {Ds : List PLLFormula}, φ ∈ Ds → LaxND L φ →
      Nonempty (LaxND L (bigOr Ds))
  | _ :: _, .head _, p => ⟨.orIntro1 p⟩
  | _ :: _, .tail _ h, p => (bigOrIntro h p).elim fun q => ⟨.orIntro2 q⟩

/-- Eliminate a finite disjunction: if every disjunct yields `χ`, so does the
disjunction.  On the empty list `bigOr [] = ⊥` and falsity elimination
applies. -/
def bigOrElim {L : List PLLFormula} {χ : PLLFormula} :
    {Ds : List PLLFormula} → LaxND L (bigOr Ds) →
      (∀ φ, φ ∈ Ds → LaxND (φ :: L) χ) → LaxND L χ
  | [], p, _ => .falsoElim _ p
  | ψ :: Ds', p, br =>
      .orElim p (br ψ (.head _))
        (bigOrElim (.iden (List.mem_cons_self ..))
          (fun φ h => (br φ (.tail _ h)).rename (by
            intro χ' h'
            simp only [List.mem_cons] at h' ⊢
            exact h'.imp id .inr)))

/-- The lax modality is functorial: from `φ ⊢ ψ` (over side context `L`)
conclude `◯φ ⊢ ◯ψ`. -/
def somehowMono {L : List PLLFormula} {φ ψ : PLLFormula}
    (p : LaxND (φ :: L) ψ) : LaxND (.somehow φ :: L) (.somehow ψ) :=
  .laxElim (.iden (.head _))
    (.laxIntro (p.rename (by
      intro χ h
      simp only [List.mem_cons] at h ⊢
      exact h.imp id .inr)))

end LaxND

/-! ### Derivability from a set of hypotheses -/

/-- `Γ ⊩ φ`: some finite list of hypotheses from `Γ` derives `φ`.
Compactness is built into the definition. -/
def SetDeriv (Γ : Set PLLFormula) (φ : PLLFormula) : Prop :=
  ∃ L : List PLLFormula, (∀ ψ ∈ L, ψ ∈ Γ) ∧ Nonempty (LaxND L φ)

infix:55 " ⊩ " => SetDeriv

namespace SetDeriv

theorem of_mem {Γ : Set PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : Γ ⊩ φ :=
  ⟨[φ], by simpa using h, ⟨.iden (.head _)⟩⟩

theorem ofList {Γ : Set PLLFormula} {L : List PLLFormula} {φ : PLLFormula}
    (hL : ∀ ψ ∈ L, ψ ∈ Γ) (p : LaxND L φ) : Γ ⊩ φ :=
  ⟨L, hL, ⟨p⟩⟩

theorem mono {Γ Γ' : Set PLLFormula} {φ : PLLFormula}
    (hΓ : Γ ⊆ Γ') (h : Γ ⊩ φ) : Γ' ⊩ φ := by
  obtain ⟨L, hL, hp⟩ := h
  exact ⟨L, fun ψ hψ => hΓ (hL ψ hψ), hp⟩

/-- Apply a unary list-level rule that keeps the context. -/
theorem map {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (f : ∀ {L : List PLLFormula}, LaxND L φ → LaxND L ψ) (h : Γ ⊩ φ) :
    Γ ⊩ ψ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  exact ⟨L, hL, ⟨f p⟩⟩

/-- Combine two derivations (contexts are merged by concatenation). -/
theorem map₂ {Γ : Set PLLFormula} {φ ψ χ : PLLFormula}
    (f : ∀ {L : List PLLFormula}, LaxND L φ → LaxND L ψ → LaxND L χ)
    (h₁ : Γ ⊩ φ) (h₂ : Γ ⊩ ψ) : Γ ⊩ χ := by
  obtain ⟨L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨L₂, hL₂, ⟨p₂⟩⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ⟨f (p₁.rename ?_) (p₂.rename ?_)⟩⟩
  · intro ψ' hψ'
    rcases List.mem_append.mp hψ' with h | h
    · exact hL₁ ψ' h
    · exact hL₂ ψ' h
  · intro χ' h; exact List.mem_append.mpr (.inl h)
  · intro χ' h; exact List.mem_append.mpr (.inr h)

/-- Combine three derivations. -/
theorem map₃ {Γ : Set PLLFormula} {φ ψ χ ω : PLLFormula}
    (f : ∀ {L : List PLLFormula}, LaxND L φ → LaxND L ψ → LaxND L χ → LaxND L ω)
    (h₁ : Γ ⊩ φ) (h₂ : Γ ⊩ ψ) (h₃ : Γ ⊩ χ) : Γ ⊩ ω := by
  obtain ⟨L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨L₂, hL₂, ⟨p₂⟩⟩ := h₂
  obtain ⟨L₃, hL₃, ⟨p₃⟩⟩ := h₃
  refine ⟨L₁ ++ L₂ ++ L₃, ?_, ⟨f (p₁.rename ?_) (p₂.rename ?_) (p₃.rename ?_)⟩⟩
  · intro ψ' hψ'
    simp only [List.mem_append] at hψ'
    rcases hψ' with (h | h) | h
    · exact hL₁ ψ' h
    · exact hL₂ ψ' h
    · exact hL₃ ψ' h
  · intro χ' h; simp only [List.mem_append]; exact .inl (.inl h)
  · intro χ' h; simp only [List.mem_append]; exact .inl (.inr h)
  · intro χ' h; simp only [List.mem_append]; exact .inr h

theorem mp {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h₁ : Γ ⊩ φ.ifThen ψ) (h₂ : Γ ⊩ φ) : Γ ⊩ ψ :=
  map₂ (fun p₁ p₂ => .impElim p₁ p₂) h₁ h₂

theorem falso {Γ : Set PLLFormula} (φ : PLLFormula)
    (h : Γ ⊩ .falsePLL) : Γ ⊩ φ :=
  map (fun p => .falsoElim φ p) h

theorem orL {Γ : Set PLLFormula} {φ : PLLFormula} (ψ : PLLFormula)
    (h : Γ ⊩ φ) : Γ ⊩ φ.or ψ :=
  map (fun p => .orIntro1 p) h

theorem orR {Γ : Set PLLFormula} (φ : PLLFormula) {ψ : PLLFormula}
    (h : Γ ⊩ ψ) : Γ ⊩ φ.or ψ :=
  map (fun p => .orIntro2 p) h

/-- Every hypothesis list over `insert φ Γ` renames into
`φ :: (the φ-free part)`, with the φ-free part drawn from `Γ`. -/
private theorem extract {Γ : Set PLLFormula} {φ : PLLFormula}
    {L : List PLLFormula} (hL : ∀ ψ ∈ L, ψ ∈ insert φ Γ) :
    (∀ ψ ∈ L.filter (fun χ => decide (χ ≠ φ)), ψ ∈ Γ) ∧
      (∀ ψ ∈ L, ψ ∈ φ :: L.filter (fun χ => decide (χ ≠ φ))) := by
  constructor
  · intro ψ hψ
    rw [List.mem_filter, decide_eq_true_iff] at hψ
    rcases hL ψ hψ.1 with h | h
    · exact absurd h hψ.2
    · exact h
  · intro ψ hψ
    by_cases h : ψ = φ
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _
        (List.mem_filter.mpr ⟨hψ, decide_eq_true h⟩)

/-- Deduction theorem, one direction: discharge a hypothesis. -/
theorem deduct {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h : insert φ Γ ⊩ ψ) : Γ ⊩ φ.ifThen ψ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  obtain ⟨hfilter, hren⟩ := extract hL
  exact ⟨_, hfilter, ⟨.impIntro (p.rename hren)⟩⟩

/-- Deduction theorem, converse direction. -/
theorem undeduct {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h : Γ ⊩ φ.ifThen ψ) : insert φ Γ ⊩ ψ :=
  mp (mono (Set.subset_insert φ Γ) h) (of_mem (Set.mem_insert φ Γ))

/-- Cut at the level of sets. -/
theorem cut {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h₁ : Γ ⊩ φ) (h₂ : insert φ Γ ⊩ ψ) : Γ ⊩ ψ :=
  mp (deduct h₂) h₁

/-- Disjunction elimination at the level of sets. -/
theorem orE {Γ : Set PLLFormula} {φ ψ χ : PLLFormula}
    (h₀ : Γ ⊩ φ.or ψ) (h₁ : insert φ Γ ⊩ χ) (h₂ : insert ψ Γ ⊩ χ) :
    Γ ⊩ χ :=
  map₃ (fun p₀ pd₁ pd₂ => .orElim p₀
      (.impElim (pd₁.rename (fun _ h => List.mem_cons_of_mem _ h))
        (.iden (.head _)))
      (.impElim (pd₂.rename (fun _ h => List.mem_cons_of_mem _ h))
        (.iden (.head _))))
    h₀ (deduct h₁) (deduct h₂)

/-- Finite-disjunction introduction, set level. -/
theorem bigOr_intro {Γ : Set PLLFormula} {φ : PLLFormula}
    {Ds : List PLLFormula} (hmem : φ ∈ Ds) (h : Γ ⊩ φ) : Γ ⊩ bigOr Ds := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine ⟨L, hL, ?_⟩
  exact LaxND.bigOrIntro hmem p

/-- Finite-disjunction elimination, set level. -/
theorem bigOr_elim {Γ : Set PLLFormula} {χ : PLLFormula} :
    ∀ {Ds : List PLLFormula}, Γ ⊩ bigOr Ds →
      (∀ φ ∈ Ds, insert φ Γ ⊩ χ) → Γ ⊩ χ
  | [], h, _ => falso χ h
  | ψ :: Ds', h, br =>
      orE h (br ψ (.head _))
        (bigOr_elim (Ds := Ds') (of_mem (Set.mem_insert ..))
          (fun φ hφ => by
            have := br φ (.tail _ hφ)
            exact mono (by
              intro χ' h'
              rcases h' with rfl | h'
              · exact Set.mem_insert ..
              · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h')) this))

/-- If every disjunct of `Ds` collapses to the single formula `χ`
(as happens for `Ds ⊆ {χ}`), the whole disjunction collapses. -/
theorem bigOr_collapse {Γ : Set PLLFormula} {χ : PLLFormula}
    {Ds : List PLLFormula} (hsub : ∀ φ ∈ Ds, φ = χ)
    (h : Γ ⊩ bigOr Ds) : Γ ⊩ χ :=
  bigOr_elim h (fun φ hφ => hsub φ hφ ▸ of_mem (Set.mem_insert ..))

/-- Weakening a finite disjunction to a superlist. -/
theorem bigOr_sub {Γ : Set PLLFormula} {Ds Ds' : List PLLFormula}
    (hsub : ∀ φ ∈ Ds, φ ∈ Ds') (h : Γ ⊩ bigOr Ds) : Γ ⊩ bigOr Ds' :=
  bigOr_elim h
    (fun φ hφ => bigOr_intro (hsub φ hφ) (of_mem (Set.mem_insert ..)))

/-! ### The PLL-specific lemmas -/

/-- `◯` is functorial, set level: from `insert φ Γ ⊩ ψ` and `Γ ⊩ ◯φ`
conclude `Γ ⊩ ◯ψ`.  (This is set-level `laxElim` with a non-`◯` minor
premise promoted by `laxIntro`.) -/
theorem somehow_mono {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h₁ : Γ ⊩ .somehow φ) (h₂ : insert φ Γ ⊩ ψ) : Γ ⊩ .somehow ψ :=
  map₂ (fun p₁ pd => .laxElim p₁
      (.laxIntro (.impElim (pd.rename (fun _ h => List.mem_cons_of_mem _ h))
        (.iden (.head _)))))
    h₁ (deduct h₂)

/-- `(φ ⊃ ◯χ) ⊢ ◯φ ⊃ ◯χ` — the key lemma for the `◯N ∈ Γ` case of the
truth lemma (Lemma 2.1 in Fairtlough–Mendler). -/
theorem somehow_bind {Γ : Set PLLFormula} {φ χ : PLLFormula}
    (h₁ : Γ ⊩ .somehow φ) (h₂ : Γ ⊩ φ.ifThen (.somehow χ)) :
    Γ ⊩ .somehow χ :=
  map₂ (fun p₁ p₂ => .laxElim p₁
      (.impElim (p₂.rename (fun _ h => List.mem_cons_of_mem _ h))
        (.iden (.head _))))
    h₁ h₂

/-- `K ∨ ◯L ⊢ ◯(K ∨ L)` — powers `Θ ⊆ Δ` (Lemma 4.2(vi)). -/
theorem somehow_or_absorb {Γ : Set PLLFormula} {φ ψ : PLLFormula}
    (h : Γ ⊩ φ.or (.somehow ψ)) : Γ ⊩ .somehow (φ.or ψ) :=
  orE h
    (map (fun p => .laxIntro (.orIntro1 p)) (of_mem (Set.mem_insert ..)))
    (somehow_mono (of_mem (Set.mem_insert ..))
      (orR φ (of_mem (Set.mem_insert ..))))

end SetDeriv

end PLLND
