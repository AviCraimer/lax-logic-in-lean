import LaxLogic.PLLNoFall

/-!
# Scheme extensions of PLL, and the chain-classification engine

Shared infrastructure for the two new rungs of the ladder of logics
(`wip/classical.lean`, `wip/linear.lean`), built to the pattern of
`LaxLogic/PLLNoFall.lean`.

`PLLNoFall.lean` adds the **closed** axiom `¬◯⊥` as a persistent hypothesis
and notes that for an axiom *with variables* the hypothesis form would be
strictly weaker than the substitution-closed extension.  Linearity and
excluded middle are schemes with variables, so here the axioms are supplied
as an arbitrary **set** `X : PLLFormula → Prop` of formulas, of which a
derivation may use any finite list:

    DerivX X Γ φ  :=  ∃ L, (∀ θ ∈ L, X θ) ∧ LaxND (L ++ Γ) φ

Taking `X` to be *all* instances of a scheme is exactly the
substitution-closed extension: every instance is available, at every node of
every derivation, and each derivation uses finitely many.  This is the form
`ConfluentU.DerivU` already uses for the distribution scheme.

## Contents

* `DerivX` and its admissible structure (`mp`, `deduction`, `rename`, `cut`,
  `substCtx`), monotonicity in the axiom set (`mono`), and the transport
  `of_derivable_axioms`: if every `X'`-axiom is `X`-derivable then
  `DerivX X' ≤ DerivX X`.
* `ndK` — **`K` for the lax modality is a theorem of plain PLL**:

      ◯(A ⊃ B) ⊃ (◯A ⊃ ◯B)

  by two `laxElim`s (F&M's `◯S` + `◯F` route, Inf. Comput. 137(1), p. 7).
  No extra axiom is used, so `K` is available in every system below.
* `Interd X Δ A B` — interderivability under the extra hypotheses `Δ`, with
  its congruence lemmas for `∧`, `∨`, `⊃`, `◯`.
* `chain_classify` — the engine: if the variable-free fragment has a finite
  list of representatives `rep : Fin n → PLLFormula` closed (up to `Interd`)
  under the four connectives, then **every** variable-free formula is
  `Interd`-equal to one of them.  Instantiated three times:

  - `dich_nobot`  (hypothesis `¬◯⊥`)   — two classes `⊥, ⊤`;
  - `dich_bot`    (hypothesis `◯⊥`)    — two classes `⊥, ⊤`;
  - `dich_nnbot`  (hypothesis `¬¬◯⊥`)  — three classes `⊥, ◯⊥, ⊤`.

* `sound` / `not_deriv_of_countermodel` — soundness of `DerivX X` over any
  constraint model validating every `X`-axiom, and the countermodel form used
  for the lower bounds.
-/

open PLLFormula

namespace PLLND
namespace SchemeExt

open NoFall (VarFree)

/-! ## 1. The system -/

/-- **PLL extended by an axiom set `X`**, hypothesis-list form: a derivation
may use any finite list of `X`-axioms as extra hypotheses.  For `X` the set of
all instances of a scheme this is the substitution-closed extension. -/
def DerivX (X : PLLFormula → Prop) (Γ : List PLLFormula) (φ : PLLFormula) : Prop :=
  ∃ L : List PLLFormula, (∀ θ ∈ L, X θ) ∧ Nonempty (LaxND (L ++ Γ) φ)

namespace DerivX

variable {X X' : PLLFormula → Prop} {Γ Δ : List PLLFormula} {φ ψ χ : PLLFormula}

theorem of_nd (p : LaxND Γ φ) : DerivX X Γ φ := ⟨[], by simp, ⟨p⟩⟩

theorem hyp (h : φ ∈ Γ) : DerivX X Γ φ := of_nd (.iden h)

/-- An axiom of the extension. -/
theorem ax (h : X φ) : DerivX X Γ φ :=
  ⟨[φ], by simpa using h, ⟨.iden (by simp)⟩⟩

theorem rename (H : ∀ ψ ∈ Γ, ψ ∈ Δ) (h : DerivX X Γ φ) : DerivX X Δ φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine ⟨L, hL, ⟨p.rename ?_⟩⟩
  intro θ hθ
  simp only [List.mem_append] at hθ ⊢
  rcases hθ with hθ | hθ
  exacts [Or.inl hθ, Or.inr (H θ hθ)]

/-- Monotone in the axiom set. -/
theorem mono (hX : ∀ θ, X θ → X' θ) (h : DerivX X Γ φ) : DerivX X' Γ φ := by
  obtain ⟨L, hL, p⟩ := h
  exact ⟨L, fun θ hθ => hX θ (hL θ hθ), p⟩

theorem mp (h₁ : DerivX X Γ (φ.ifThen ψ)) (h₂ : DerivX X Γ φ) : DerivX X Γ ψ := by
  obtain ⟨L₁, hL₁, ⟨p₁⟩⟩ := h₁
  obtain ⟨L₂, hL₂, ⟨p₂⟩⟩ := h₂
  refine ⟨L₁ ++ L₂, ?_, ⟨?_⟩⟩
  · intro θ hθ
    rcases List.mem_append.mp hθ with hθ | hθ
    exacts [hL₁ θ hθ, hL₂ θ hθ]
  · refine .impElim (p₁.rename ?_) (p₂.rename ?_) <;>
      · intro θ hθ
        simp only [List.mem_append] at hθ ⊢
        tauto

theorem deduction (h : DerivX X (φ :: Γ) ψ) : DerivX X Γ (φ.ifThen ψ) := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine ⟨L, hL, ⟨.impIntro (p.rename ?_)⟩⟩
  intro θ hθ
  simp only [List.mem_append, List.mem_cons] at hθ ⊢
  tauto

theorem unit (h : DerivX X Γ φ) : DerivX X Γ (somehow φ) := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  exact ⟨L, hL, ⟨.laxIntro p⟩⟩

theorem cut (h₁ : DerivX X Γ φ) (h₂ : DerivX X (φ :: Γ) ψ) : DerivX X Γ ψ :=
  mp (deduction h₂) h₁

theorem exfalso (h : DerivX X Γ falsePLL) (φ : PLLFormula) : DerivX X Γ φ :=
  mp (of_nd (.impIntro (.falsoElim φ (.iden (List.mem_cons_self ..))))) h

/-- **Context substitution / generalised cut**: if every hypothesis of a
derivation is itself derivable in `Δ`, the conclusion is derivable in `Δ`. -/
theorem substCtx : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    (∀ ψ ∈ Γ, DerivX X Δ ψ) → DerivX X Γ φ → DerivX X Δ φ
  | [], _, _, h => h.rename (by simp)
  | ψ :: Γ, _, H, h =>
      mp (substCtx (fun χ hχ => H χ (List.mem_cons_of_mem _ hχ)) (deduction h))
        (H ψ (List.mem_cons_self ..))

/-- **Transport along derivable axioms**: if every `X'`-axiom is a theorem of
the `X`-system, then everything `X'` derives, `X` derives. -/
theorem of_derivable_axioms (hax : ∀ θ, X' θ → DerivX X [] θ)
    (h : DerivX X' Γ φ) : DerivX X Γ φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine substCtx (Γ := L ++ Γ) (Δ := Γ) ?_ (of_nd (X := X) p)
  intro θ hθ
  rcases List.mem_append.mp hθ with hθ | hθ
  · exact (hax θ (hL θ hθ)).rename (by simp)
  · exact hyp hθ

theorem andI (h₁ : DerivX X Γ φ) (h₂ : DerivX X Γ ψ) : DerivX X Γ (φ.and ψ) :=
  mp (mp (of_nd (.impIntro (.impIntro
    (.andIntro (.iden (by simp)) (.iden (by simp)))))) h₁) h₂

theorem andE₁ (h : DerivX X Γ (φ.and ψ)) : DerivX X Γ φ :=
  mp (of_nd (.impIntro (.andElim1 (φ := φ) (ψ := ψ) (.iden (by simp))))) h

theorem andE₂ (h : DerivX X Γ (φ.and ψ)) : DerivX X Γ ψ :=
  mp (of_nd (.impIntro (.andElim2 (φ := φ) (ψ := ψ) (.iden (by simp))))) h

theorem orI₁ (h : DerivX X Γ φ) : DerivX X Γ (φ.or ψ) :=
  mp (of_nd (.impIntro (.orIntro1 (φ := φ) (ψ := ψ) (.iden (by simp))))) h

theorem orI₂ (h : DerivX X Γ ψ) : DerivX X Γ (φ.or ψ) :=
  mp (of_nd (.impIntro (.orIntro2 (φ := φ) (ψ := ψ) (.iden (by simp))))) h

/-- `∨`-elimination. -/
theorem orE (h₀ : DerivX X Γ (φ.or ψ)) (h₁ : DerivX X (φ :: Γ) χ)
    (h₂ : DerivX X (ψ :: Γ) χ) : DerivX X Γ χ := by
  have d₁ : DerivX X Γ (φ.ifThen χ) := deduction h₁
  have d₂ : DerivX X Γ (ψ.ifThen χ) := deduction h₂
  have base : DerivX X Γ
      ((φ.or ψ).ifThen ((φ.ifThen χ).ifThen ((ψ.ifThen χ).ifThen χ))) :=
    of_nd (.impIntro (.impIntro (.impIntro (.orElim (φ := φ) (ψ := ψ)
      (.iden (by simp))
      (.impElim (φ := φ) (.iden (by simp)) (.iden (by simp)))
      (.impElim (φ := ψ) (.iden (by simp)) (.iden (by simp)))))))
  exact mp (mp (mp base h₀) d₁) d₂

theorem top : DerivX X Γ truePLL := of_nd (.impIntro (.iden (by simp)))

end DerivX

/-! ## 2. `◯F` and `K`, in plain PLL -/

/-- `◯F` (F&M's normality axiom, Inf. Comput. 137(1), p. 7):

    (A ⊃ B) ⊃ (◯A ⊃ ◯B) . -/
def ndOF (A B : PLLFormula) :
    LaxND [] ((A.ifThen B).ifThen ((somehow A).ifThen (somehow B))) :=
  .impIntro (.impIntro (.laxElim (φ := A) (.iden (by simp))
    (.laxIntro (.impElim (φ := A) (.iden (by simp)) (.iden (by simp))))))

/-- **`K` for the lax modality is a theorem of plain PLL**:

    ◯(A ⊃ B) ⊃ (◯A ⊃ ◯B) .

Two `laxElim`s: bind the boxed implication, bind the boxed antecedent, apply,
`laxIntro`.  No axiom of any extension is used — in particular `K` needs
neither linearity nor excluded middle nor distribution.  (This is F&M's
`◯S` + `◯F` route: `◯(A⊃B) ∧ ◯A ⊢ ◯((A⊃B) ∧ A) ⊢ ◯B`.) -/
def ndK (A B : PLLFormula) :
    LaxND [] ((somehow (A.ifThen B)).ifThen ((somehow A).ifThen (somehow B))) :=
  .impIntro (.impIntro
    (.laxElim (φ := A.ifThen B) (.iden (by simp))
      (.laxElim (φ := A) (.iden (by simp))
        (.laxIntro (.impElim (φ := A) (.iden (by simp)) (.iden (by simp)))))))

/-- `◯`-monotonicity, derived form: from `Δ ⊢ A ⊃ B` conclude `Δ ⊢ ◯A ⊃ ◯B`. -/
theorem box_mono_imp {X : PLLFormula → Prop} {Δ : List PLLFormula}
    {A B : PLLFormula} (h : DerivX X Δ (A.ifThen B)) :
    DerivX X Δ ((somehow A).ifThen (somehow B)) :=
  DerivX.mp (DerivX.of_nd ((ndOF A B).rename (by simp))) h

/-- `◯`-monotonicity in hypothesis form. -/
theorem box_mono {X : PLLFormula → Prop} {Δ : List PLLFormula}
    {A B : PLLFormula} (h : DerivX X (A :: Δ) B) :
    DerivX X (somehow A :: Δ) (somehow B) :=
  DerivX.mp (φ := somehow A) (ψ := somehow B)
    ((box_mono_imp (DerivX.deduction h)).rename
      (fun _ hψ => List.mem_cons_of_mem _ hψ))
    (DerivX.hyp (by simp))

/-! ## 3. Interderivability under extra hypotheses, and its congruences -/

/-- `A` and `B` are interderivable over the extra hypotheses `Δ`. -/
def Interd (X : PLLFormula → Prop) (Δ : List PLLFormula) (A B : PLLFormula) :
    Prop :=
  DerivX X (A :: Δ) B ∧ DerivX X (B :: Δ) A

namespace Interd

variable {X : PLLFormula → Prop} {Δ : List PLLFormula} {A A' B B' : PLLFormula}

theorem refl : Interd X Δ A A := ⟨DerivX.hyp (by simp), DerivX.hyp (by simp)⟩

theorem symm (h : Interd X Δ A B) : Interd X Δ B A := ⟨h.2, h.1⟩

theorem trans (h₁ : Interd X Δ A B) (h₂ : Interd X Δ B A') :
    Interd X Δ A A' := by
  refine ⟨DerivX.cut h₁.1 (h₂.1.rename ?_), DerivX.cut h₂.2 (h₁.2.rename ?_)⟩ <;>
    · intro θ hθ
      simp only [List.mem_cons] at hθ ⊢
      tauto

/-- Weakening one formula into the head of a context. -/
theorem memShift {C D : PLLFormula} {Δ : List PLLFormula} :
    ∀ ψ ∈ C :: Δ, ψ ∈ C :: D :: Δ := by
  intro ψ hψ
  simp only [List.mem_cons] at hψ ⊢
  tauto

/-- Weakening two formulas into the head of a context. -/
theorem memShift₂ {C D E : PLLFormula} {Δ : List PLLFormula} :
    ∀ ψ ∈ C :: Δ, ψ ∈ C :: D :: E :: Δ := by
  intro ψ hψ
  simp only [List.mem_cons] at hψ ⊢
  tauto

/-- Congruence for `∧`. -/
theorem and (h₁ : Interd X Δ A A') (h₂ : Interd X Δ B B') :
    Interd X Δ (A.and B) (A'.and B') := by
  have hA : DerivX X (A.and B :: Δ) A :=
    DerivX.andE₁ (φ := A) (ψ := B) (DerivX.hyp (by simp))
  have hB : DerivX X (A.and B :: Δ) B :=
    DerivX.andE₂ (φ := A) (ψ := B) (DerivX.hyp (by simp))
  have hA' : DerivX X (A'.and B' :: Δ) A' :=
    DerivX.andE₁ (φ := A') (ψ := B') (DerivX.hyp (by simp))
  have hB' : DerivX X (A'.and B' :: Δ) B' :=
    DerivX.andE₂ (φ := A') (ψ := B') (DerivX.hyp (by simp))
  exact ⟨DerivX.andI (DerivX.cut hA (h₁.1.rename memShift))
      (DerivX.cut hB (h₂.1.rename memShift)),
    DerivX.andI (DerivX.cut hA' (h₁.2.rename memShift))
      (DerivX.cut hB' (h₂.2.rename memShift))⟩

/-- Congruence for `∨`. -/
theorem or (h₁ : Interd X Δ A A') (h₂ : Interd X Δ B B') :
    Interd X Δ (A.or B) (A'.or B') := by
  constructor
  · exact DerivX.orE (φ := A) (ψ := B) (DerivX.hyp (by simp))
      (DerivX.orI₁ (φ := A') (ψ := B') (h₁.1.rename memShift))
      (DerivX.orI₂ (φ := A') (ψ := B') (h₂.1.rename memShift))
  · exact DerivX.orE (φ := A') (ψ := B') (DerivX.hyp (by simp))
      (DerivX.orI₁ (φ := A) (ψ := B) (h₁.2.rename memShift))
      (DerivX.orI₂ (φ := A) (ψ := B) (h₂.2.rename memShift))

/-- Congruence for `⊃`. -/
theorem imp (h₁ : Interd X Δ A A') (h₂ : Interd X Δ B B') :
    Interd X Δ (A.ifThen B) (A'.ifThen B') := by
  constructor
  · refine DerivX.deduction (DerivX.cut (φ := B) ?_ (h₂.1.rename memShift₂))
    exact DerivX.mp (φ := A) (ψ := B) (DerivX.hyp (by simp))
      (h₁.2.rename memShift)
  · refine DerivX.deduction (DerivX.cut (φ := B') ?_ (h₂.2.rename memShift₂))
    exact DerivX.mp (φ := A') (ψ := B') (DerivX.hyp (by simp))
      (h₁.1.rename memShift)

/-- Congruence for `◯`. -/
theorem box (h : Interd X Δ A A') : Interd X Δ (somehow A) (somehow A') :=
  ⟨box_mono h.1, box_mono h.2⟩

/-- Monotone in the axiom set. -/
theorem mono {X' : PLLFormula → Prop} (hX : ∀ θ, X θ → X' θ)
    (h : Interd X Δ A B) : Interd X' Δ A B :=
  ⟨h.1.mono hX, h.2.mono hX⟩

end Interd

/-! ### Absorption helpers: comparable representatives -/

variable {X : PLLFormula → Prop} {Δ : List PLLFormula} {P Q : PLLFormula}

/-- If `P ⊢ Q` then `P ∧ Q ⊣⊢ P`. -/
theorem and_absorb_left (h : DerivX X (P :: Δ) Q) : Interd X Δ (P.and Q) P :=
  ⟨DerivX.andE₁ (φ := P) (ψ := Q) (DerivX.hyp (by simp)),
    DerivX.andI (DerivX.hyp (by simp)) h⟩

/-- If `Q ⊢ P` then `P ∧ Q ⊣⊢ Q`. -/
theorem and_absorb_right (h : DerivX X (Q :: Δ) P) : Interd X Δ (P.and Q) Q :=
  ⟨DerivX.andE₂ (φ := P) (ψ := Q) (DerivX.hyp (by simp)),
    DerivX.andI h (DerivX.hyp (by simp))⟩

/-- If `P ⊢ Q` then `P ∨ Q ⊣⊢ Q`. -/
theorem or_absorb_left (h : DerivX X (P :: Δ) Q) : Interd X Δ (P.or Q) Q :=
  ⟨DerivX.orE (φ := P) (ψ := Q) (DerivX.hyp (by simp))
      (h.rename Interd.memShift) (DerivX.hyp (by simp)),
    DerivX.orI₂ (φ := P) (ψ := Q) (DerivX.hyp (by simp))⟩

/-- If `Q ⊢ P` then `P ∨ Q ⊣⊢ P`. -/
theorem or_absorb_right (h : DerivX X (Q :: Δ) P) : Interd X Δ (P.or Q) P :=
  ⟨DerivX.orE (φ := P) (ψ := Q) (DerivX.hyp (by simp))
      (DerivX.hyp (by simp)) (h.rename Interd.memShift),
    DerivX.orI₁ (φ := P) (ψ := Q) (DerivX.hyp (by simp))⟩

/-- If `P ⊢ Q` then `P ⊃ Q ⊣⊢ ⊤`. -/
theorem imp_top (h : DerivX X (P :: Δ) Q) : Interd X Δ (P.ifThen Q) truePLL :=
  ⟨DerivX.top, (DerivX.deduction h).rename (fun _ hψ =>
    List.mem_cons_of_mem _ hψ)⟩

/-! ## 4. The chain-classification engine -/

/-- **The engine.**  A finite list of representatives closed under the four
connectives, up to interderivability over `Δ`, exhausts the variable-free
fragment. -/
theorem chain_classify {n : ℕ} (rep : Fin n → PLLFormula)
    (hbot : ∃ i, Interd X Δ falsePLL (rep i))
    (hand : ∀ i j, ∃ k, Interd X Δ ((rep i).and (rep j)) (rep k))
    (hor : ∀ i j, ∃ k, Interd X Δ ((rep i).or (rep j)) (rep k))
    (himp : ∀ i j, ∃ k, Interd X Δ ((rep i).ifThen (rep j)) (rep k))
    (hbox : ∀ i, ∃ k, Interd X Δ (somehow (rep i)) (rep k)) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X Δ A (rep i) := by
  intro A hA
  induction A with
  | prop a => exact hA.elim
  | falsePLL => exact hbot
  | and A B ihA ihB =>
      obtain ⟨i, hi⟩ := ihA hA.1
      obtain ⟨j, hj⟩ := ihB hA.2
      obtain ⟨k, hk⟩ := hand i j
      exact ⟨k, (Interd.and hi hj).trans hk⟩
  | or A B ihA ihB =>
      obtain ⟨i, hi⟩ := ihA hA.1
      obtain ⟨j, hj⟩ := ihB hA.2
      obtain ⟨k, hk⟩ := hor i j
      exact ⟨k, (Interd.or hi hj).trans hk⟩
  | ifThen A B ihA ihB =>
      obtain ⟨i, hi⟩ := ihA hA.1
      obtain ⟨j, hj⟩ := ihB hA.2
      obtain ⟨k, hk⟩ := himp i j
      exact ⟨k, (Interd.imp hi hj).trans hk⟩
  | somehow A ih =>
      obtain ⟨i, hi⟩ := ih hA
      obtain ⟨k, hk⟩ := hbox i
      exact ⟨k, (Interd.box hi).trans hk⟩

/-- **The engine, chain form.**  Representatives listed in increasing order:
`∧` and `∨` are then min and max, and `⊃` needs only the descending pairs. -/
theorem chain_classify_le {n : ℕ} (rep : Fin n → PLLFormula)
    (hmono : ∀ i j : Fin n, i ≤ j → DerivX X (rep i :: Δ) (rep j))
    (hbot : ∃ i, Interd X Δ falsePLL (rep i))
    (htop : ∃ i, Interd X Δ truePLL (rep i))
    (himp : ∀ i j : Fin n, j ≤ i →
      ∃ k, Interd X Δ ((rep i).ifThen (rep j)) (rep k))
    (hbox : ∀ i, ∃ k, Interd X Δ (somehow (rep i)) (rep k)) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X Δ A (rep i) := by
  refine chain_classify rep hbot ?_ ?_ ?_ hbox
  · intro i j
    rcases le_total i j with h | h
    · exact ⟨i, and_absorb_left (hmono i j h)⟩
    · exact ⟨j, and_absorb_right (hmono j i h)⟩
  · intro i j
    rcases le_total i j with h | h
    · exact ⟨j, or_absorb_left (hmono i j h)⟩
    · exact ⟨i, or_absorb_right (hmono j i h)⟩
  · intro i j
    rcases le_total j i with h | h
    · exact himp i j h
    · obtain ⟨t, ht⟩ := htop
      exact ⟨t, (imp_top (hmono i j h)).trans ht⟩

/-! ## 5. The three branch dichotomies

The three hypotheses are `¬◯⊥`, `◯⊥` and `¬¬◯⊥`.  Each is a **closed**
formula, so hypothesis form and axiom form agree, exactly as in
`PLLNoFall.lean`. -/

/-- `◯⊥`. -/
abbrev boxBot : PLLFormula := somehow falsePLL

/-- `¬¬◯⊥`. -/
abbrev nnbot : PLLFormula := notPLL (notPLL boxBot)

/-- Two representatives: `⊥`, `⊤`. -/
def rep2 (i : Fin 2) : PLLFormula := if i.val = 0 then falsePLL else truePLL

/-- Three representatives: `⊥`, `◯⊥`, `⊤`. -/
def rep3 (i : Fin 3) : PLLFormula :=
  if i.val = 0 then falsePLL else if i.val = 1 then boxBot else truePLL

@[simp] theorem rep2_zero : rep2 0 = falsePLL := rfl
@[simp] theorem rep2_one : rep2 1 = truePLL := rfl
@[simp] theorem rep3_zero : rep3 0 = falsePLL := rfl
@[simp] theorem rep3_one : rep3 1 = boxBot := rfl
@[simp] theorem rep3_two : rep3 2 = truePLL := rfl

theorem varFree_boxBot : VarFree boxBot := trivial

theorem varFree_nnbot : VarFree nnbot := ⟨⟨trivial, trivial⟩, trivial⟩

theorem varFree_rep2 (i : Fin 2) : VarFree (rep2 i) := by
  fin_cases i
  exacts [trivial, NoFall.varFree_truePLL]

theorem varFree_rep3 (i : Fin 3) : VarFree (rep3 i) := by
  fin_cases i
  exacts [trivial, trivial, NoFall.varFree_truePLL]

/-- `⊥ ⊢ φ`, in hypothesis form. -/
theorem bot_imp (φ : PLLFormula) : DerivX X (falsePLL :: Δ) φ :=
  DerivX.exfalso (DerivX.hyp (by simp)) φ

/-- `⊤` is a representative in the two-element list. -/
theorem interd_top2 : Interd X Δ truePLL (rep2 1) := Interd.refl

/-- `◯⊤ ⊣⊢ ⊤`. -/
theorem box_top : Interd X Δ (somehow truePLL) truePLL :=
  ⟨DerivX.top, DerivX.unit DerivX.top⟩

/-- `⊤ ⊃ P ⊣⊢ P`. -/
theorem top_imp (P : PLLFormula) : Interd X Δ (truePLL.ifThen P) P :=
  ⟨DerivX.mp (φ := truePLL) (ψ := P) (DerivX.hyp (by simp)) DerivX.top,
    DerivX.deduction (DerivX.hyp (by simp))⟩

/-- Monotonicity of the two-element list. -/
theorem mono2 (i j : Fin 2) (h : i ≤ j) : DerivX X (rep2 i :: Δ) (rep2 j) := by
  fin_cases i <;> fin_cases j
  · exact DerivX.hyp (by simp)
  · exact bot_imp _
  · exact absurd h (by decide : ¬ ((1 : Fin 2) ≤ (0 : Fin 2)))
  · exact DerivX.hyp (by simp)

/-- Monotonicity of the three-element list. -/
theorem mono3 (i j : Fin 3) (h : i ≤ j) : DerivX X (rep3 i :: Δ) (rep3 j) := by
  fin_cases i <;> fin_cases j
  · exact DerivX.hyp (by simp)
  · exact bot_imp _
  · exact bot_imp _
  · exact absurd h (by decide : ¬ ((1 : Fin 3) ≤ (0 : Fin 3)))
  · exact DerivX.hyp (by simp)
  · exact DerivX.top
  · exact absurd h (by decide : ¬ ((2 : Fin 3) ≤ (0 : Fin 3)))
  · exact absurd h (by decide : ¬ ((2 : Fin 3) ≤ (1 : Fin 3)))
  · exact DerivX.hyp (by simp)

/-! ### (a) Under `¬◯⊥`: two classes -/

/-- Under the hypothesis `¬◯⊥` the variable-free fragment is `{⊥, ⊤}`.
This is `PLLNoFall.varfree_dichotomy` re-proved through the engine, in the
`Interd` form the combination step needs. -/
theorem dich_nobot (hΔ : NoFall.nobot ∈ Δ) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X Δ A (rep2 i) := by
  refine chain_classify_le rep2 mono2 ⟨0, Interd.refl⟩ ⟨1, Interd.refl⟩ ?_ ?_
  · intro i j _
    fin_cases i <;> fin_cases j
    · exact ⟨1, imp_top (bot_imp _)⟩
    · exact ⟨1, imp_top (bot_imp _)⟩
    · exact ⟨0, top_imp falsePLL⟩
    · exact ⟨1, imp_top (DerivX.hyp (by simp))⟩
  · intro i
    fin_cases i
    · -- `◯⊥ ⊣⊢ ⊥` under `¬◯⊥`
      exact ⟨0, ⟨DerivX.mp (φ := boxBot) (ψ := falsePLL)
        (DerivX.hyp (List.mem_cons_of_mem _ hΔ))
        (DerivX.hyp (by simp)), bot_imp _⟩⟩
    · exact ⟨1, box_top⟩

/-! ### (b) Under `◯⊥`: two classes -/

/-- Under the hypothesis `◯⊥` the variable-free fragment is `{⊥, ⊤}`:
everything `◯`-ed is `⊤`. -/
theorem dich_bot (hΔ : boxBot ∈ Δ) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X Δ A (rep2 i) := by
  refine chain_classify_le rep2 mono2 ⟨0, Interd.refl⟩ ⟨1, Interd.refl⟩ ?_ ?_
  · intro i j _
    fin_cases i <;> fin_cases j
    · exact ⟨1, imp_top (bot_imp _)⟩
    · exact ⟨1, imp_top (bot_imp _)⟩
    · exact ⟨0, top_imp falsePLL⟩
    · exact ⟨1, imp_top (DerivX.hyp (by simp))⟩
  · intro i
    fin_cases i
    · -- `◯⊥ ⊣⊢ ⊤` under `◯⊥`
      exact ⟨1, ⟨DerivX.top, DerivX.hyp (List.mem_cons_of_mem _ hΔ)⟩⟩
    · exact ⟨1, box_top⟩

/-! ### (c) Under `¬¬◯⊥`: three classes -/

/-- `◯◯⊥ ⊣⊢ ◯⊥` — the multiplication of the monad, hypothesis form. -/
theorem box_boxBot : Interd X Δ (somehow boxBot) boxBot :=
  ⟨DerivX.of_nd (.laxElim (φ := boxBot) (.iden (by simp)) (.iden (by simp))),
    DerivX.unit (DerivX.hyp (by simp))⟩

/-- Under the hypothesis `¬¬◯⊥` the variable-free fragment is `{⊥, ◯⊥, ⊤}`:
the three-element chain, with `◯⊥` strictly between. -/
theorem dich_nnbot (hΔ : nnbot ∈ Δ) :
    ∀ A : PLLFormula, VarFree A → ∃ i, Interd X Δ A (rep3 i) := by
  have hneg : Interd X Δ (boxBot.ifThen falsePLL) falsePLL :=
    ⟨DerivX.mp (φ := boxBot.ifThen falsePLL) (ψ := falsePLL)
      (DerivX.hyp (List.mem_cons_of_mem _ hΔ))
      (DerivX.hyp (by simp)), bot_imp _⟩
  refine chain_classify_le rep3 mono3 ⟨0, Interd.refl⟩ ⟨2, Interd.refl⟩ ?_ ?_
  · intro i j _
    fin_cases i <;> fin_cases j
    · exact ⟨2, imp_top (bot_imp _)⟩
    · exact ⟨2, imp_top (bot_imp _)⟩
    · exact ⟨2, imp_top (bot_imp _)⟩
    · exact ⟨0, hneg⟩
    · exact ⟨2, imp_top (DerivX.hyp (by simp))⟩
    · exact ⟨2, imp_top DerivX.top⟩
    · exact ⟨0, top_imp falsePLL⟩
    · exact ⟨1, top_imp boxBot⟩
    · exact ⟨2, imp_top (DerivX.hyp (by simp))⟩
  · intro i
    fin_cases i
    · exact ⟨1, Interd.refl⟩
    · exact ⟨1, box_boxBot⟩
    · exact ⟨2, box_top⟩

/-! ## 6. Two-branch combination

The two rungs below are both proved by splitting on a provable disjunction
(`◯⊥ ∨ ¬◯⊥` classically, `¬◯⊥ ∨ ¬¬◯⊥` under linearity), classifying inside
each branch, and gluing.  The gluing step is this lemma. -/

/-- **Two-branch combination.**  Given a provable case split `P ∨ Q`, a
classification of `A` under `P`, one under `Q`, and bridges connecting the
branch representatives with the global ones, `A` is classified globally. -/
theorem combine {P Q A : PLLFormula} {m n : ℕ} {repP : Fin m → PLLFormula}
    {repQ : Fin n → PLLFormula} {rep : Fin m → Fin n → PLLFormula}
    {i : Fin m} {j : Fin n}
    (hsplit : ∀ Θ : List PLLFormula, DerivX X Θ (P.or Q))
    (b1 : DerivX X [repP i, P] (rep i j)) (b1' : DerivX X [rep i j, P] (repP i))
    (b2 : DerivX X [repQ j, Q] (rep i j)) (b2' : DerivX X [rep i j, Q] (repQ j))
    (h1 : Interd X [P] A (repP i)) (h2 : Interd X [Q] A (repQ j)) :
    Interd X [] A (rep i j) := by
  constructor
  · refine DerivX.orE (φ := P) (ψ := Q) (hsplit [A]) ?_ ?_
    · exact DerivX.cut (φ := repP i)
        (h1.1.rename (by intro θ hθ; simp at hθ ⊢; tauto))
        (b1.rename (by intro θ hθ; simp at hθ ⊢; tauto))
    · exact DerivX.cut (φ := repQ j)
        (h2.1.rename (by intro θ hθ; simp at hθ ⊢; tauto))
        (b2.rename (by intro θ hθ; simp at hθ ⊢; tauto))
  · refine DerivX.orE (φ := P) (ψ := Q) (hsplit [rep i j]) ?_ ?_
    · exact DerivX.cut (φ := repP i)
        (b1'.rename (by intro θ hθ; simp at hθ ⊢; tauto))
        (h1.2.rename (by intro θ hθ; simp at hθ ⊢; tauto))
    · exact DerivX.cut (φ := repQ j)
        (b2'.rename (by intro θ hθ; simp at hθ ⊢; tauto))
        (h2.2.rename (by intro θ hθ; simp at hθ ⊢; tauto))

/-! ## 7. Soundness over models validating the axioms -/

/-- **Soundness** of `DerivX X` over any constraint model at which every
`X`-axiom is forced everywhere. -/
theorem sound {C : ConstraintModel} (hax : ∀ θ, X θ → ∀ w : C.W, C.force w θ)
    {Γ : List PLLFormula} {φ : PLLFormula} (h : DerivX X Γ φ) (w : C.W)
    (hΓ : ∀ ψ ∈ Γ, C.force w ψ) : C.force w φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  refine soundness p C w ?_
  intro ψ hψ
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact hax ψ (hL ψ hψ) w
  · exact hΓ ψ hψ

/-- The countermodel form: a world forcing `P` but not `Q` refutes `P ⊢ Q`. -/
theorem not_deriv_of_countermodel {C : ConstraintModel}
    (hax : ∀ θ, X θ → ∀ w : C.W, C.force w θ) {P Q : PLLFormula} {w : C.W}
    (hP : C.force w P) (hQ : ¬ C.force w Q) : ¬ DerivX X [P] Q := by
  intro h
  exact hQ (sound hax h w (by intro ψ hψ; simp at hψ; subst hψ; exact hP))

end SchemeExt
end PLLND
