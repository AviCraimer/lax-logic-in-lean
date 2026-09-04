import LaxLogic.PLLNoFall

/-!
# ◯-normalisation for PCLL + `¬◯⊥`, and the IPC calibration

Groundwork for uniform interpolation for PCLL + `¬◯⊥` (system
`NoFall.DerivUNoFall` of `PLLNoFall.lean`).  Two structural facts carry every
syntactic route:

1. **`◯` is a lattice homomorphism** (`obBot`, `obAnd`, `obOr`, `obOb`): in
   PCLL + `¬◯⊥` the modality commutes with `∧`, `∨`, `⊥` and is idempotent.
   (`∧` and idempotence hold already in PLL; `∨` is the distribution scheme
   plus monotonicity; `⊥` is the axiom.)  Consequently every formula is
   interderivable with one in **◯-normal form** — `◯` applied only to atoms
   and implications (`nf`, `nf_equiv`, `nf_normal`), and derivability is
   invariant under normalisation (`nf_iff`).  A sequent calculus and a
   Pitts-style interpolant computation for this logic need only speak about
   normal forms, where the `◯∨`- and `◯⊥`-cases have been compiled away.

2. **The `◯`-free fragment is exactly IPC** (`derivUNoFall_iff_IPLND`): on
   `◯`-free sequents, PCLL + `¬◯⊥` proves neither more nor less than
   intuitionistic propositional logic.  Forward: the erasure translation of
   `PLLNDCore.lean` sends the axiom to `⊥ ⊃ ⊥` and each distribution
   instance to `(A ∨ B) ⊃ (A ∨ B)`, both trivially derivable, and they strip
   off.  Backward: `IPLND` embeds into `LaxND`.  This calibrates the uniform
   interpolation problem: full UI for PCLL + `¬◯⊥` contains full UI for IPC
   (Pitts' theorem), so nothing cheaper than a Pitts-style computation can
   close it.

The interderivability relation `EquivNF` and its congruence kit
(`and_congr`, `or_congr`, `imp_congr`, `ob_congr`) are the rewriting
infrastructure used throughout.
-/

open PLLFormula

namespace PLLND
namespace NoFall

open ConfluentU

/-! ## 1. Interderivability and the entailment kit -/

/-- Composition of entailments: from `[X] ⊢ Y` and `Γ ⊢ X`, `Γ ⊢ Y`. -/
theorem comp {Γ : List PLLFormula} {X Y : PLLFormula}
    (h₁ : DerivUNoFall [X] Y) (h₂ : DerivUNoFall Γ X) : DerivUNoFall Γ Y :=
  DerivUNoFall.mp ((DerivUNoFall.deduction h₁).rename (by simp)) h₂

theorem andI {Γ : List PLLFormula} {A B : PLLFormula}
    (h₁ : DerivUNoFall Γ A) (h₂ : DerivUNoFall Γ B) :
    DerivUNoFall Γ (A.and B) :=
  DerivUNoFall.mp (DerivUNoFall.mp (DerivUNoFall.of_nd
    (.impIntro (.impIntro (.andIntro (.iden (by simp)) (.iden (by simp))))))
    h₁) h₂

/-- `∨`-elimination at `DerivUNoFall` level. -/
theorem orE {Γ : List PLLFormula} {A B C : PLLFormula}
    (h₀ : DerivUNoFall Γ (A.or B))
    (h₁ : DerivUNoFall (A :: Γ) C) (h₂ : DerivUNoFall (B :: Γ) C) :
    DerivUNoFall Γ C := by
  have base : DerivUNoFall Γ
      ((A.or B).ifThen ((A.ifThen C).ifThen ((B.ifThen C).ifThen C))) :=
    DerivUNoFall.of_nd (.impIntro (.impIntro (.impIntro
      (.orElim (φ := A) (ψ := B) (.iden (by simp))
        (.impElim (φ := A) (.iden (by simp)) (.iden (by simp)))
        (.impElim (φ := B) (.iden (by simp)) (.iden (by simp)))))))
  exact ((base.mp h₀).mp h₁.deduction).mp h₂.deduction

/-- `◯` is monotone on entailments. -/
theorem ob_mono {A B : PLLFormula} (h : DerivUNoFall [A] B) :
    DerivUNoFall [somehow A] (somehow B) := by
  have d : DerivUNoFall [somehow A] (A.ifThen B) :=
    (DerivUNoFall.deduction h).rename (by simp)
  have base : DerivUNoFall [somehow A]
      ((A.ifThen B).ifThen (somehow B)) :=
    DerivUNoFall.of_nd (.impIntro (.laxElim (φ := A) (ψ := B)
      (.iden (by simp))
      (.laxIntro (.impElim (φ := A) (.iden (by simp)) (.iden (by simp))))))
  exact base.mp d

/-- Interderivability in PCLL + `¬◯⊥`. -/
def EquivNF (A B : PLLFormula) : Prop :=
  DerivUNoFall [A] B ∧ DerivUNoFall [B] A

namespace EquivNF

theorem refl (A : PLLFormula) : EquivNF A A :=
  ⟨.hyp (by simp), .hyp (by simp)⟩

theorem symm {A B : PLLFormula} (h : EquivNF A B) : EquivNF B A :=
  ⟨h.2, h.1⟩

theorem trans {A B C : PLLFormula} (h₁ : EquivNF A B) (h₂ : EquivNF B C) :
    EquivNF A C :=
  ⟨comp h₂.1 h₁.1, comp h₁.2 h₂.2⟩

end EquivNF

theorem and_congr {A A' B B' : PLLFormula}
    (hA : EquivNF A A') (hB : EquivNF B B') :
    EquivNF (A.and B) (A'.and B') := by
  constructor
  · exact andI (comp hA.1 (.of_nd (.andElim1 (ψ := B) (.iden (by simp)))))
      (comp hB.1 (.of_nd (.andElim2 (φ := A) (.iden (by simp)))))
  · exact andI (comp hA.2 (.of_nd (.andElim1 (ψ := B') (.iden (by simp)))))
      (comp hB.2 (.of_nd (.andElim2 (φ := A') (.iden (by simp)))))

theorem or_congr {A A' B B' : PLLFormula}
    (hA : EquivNF A A') (hB : EquivNF B B') :
    EquivNF (A.or B) (A'.or B') := by
  constructor
  · exact orE (A := A) (B := B) (.hyp (by simp))
      (comp (.of_nd (.orIntro1 (.iden (by simp)))) (comp hA.1 (.hyp (by simp))))
      (comp (.of_nd (.orIntro2 (.iden (by simp)))) (comp hB.1 (.hyp (by simp))))
  · exact orE (A := A') (B := B') (.hyp (by simp))
      (comp (.of_nd (.orIntro1 (.iden (by simp)))) (comp hA.2 (.hyp (by simp))))
      (comp (.of_nd (.orIntro2 (.iden (by simp)))) (comp hB.2 (.hyp (by simp))))

theorem imp_mono {A A' B B' : PLLFormula}
    (hA : DerivUNoFall [A'] A) (hB : DerivUNoFall [B] B') :
    DerivUNoFall [A.ifThen B] (A'.ifThen B') := by
  refine DerivUNoFall.deduction ?_
  have h₁ : DerivUNoFall (A' :: [A.ifThen B]) A := hA.rename (by simp)
  have h₂ : DerivUNoFall (A' :: [A.ifThen B]) B :=
    DerivUNoFall.mp (.hyp (by simp)) h₁
  exact comp hB h₂

theorem imp_congr {A A' B B' : PLLFormula}
    (hA : EquivNF A A') (hB : EquivNF B B') :
    EquivNF (A.ifThen B) (A'.ifThen B') :=
  ⟨imp_mono hA.2 hB.1, imp_mono hA.1 hB.2⟩

theorem ob_congr {A B : PLLFormula} (h : EquivNF A B) :
    EquivNF (somehow A) (somehow B) :=
  ⟨ob_mono h.1, ob_mono h.2⟩

/-! ## 2. The lattice-homomorphism laws -/

/-- `◯⊥ ≡ ⊥` — the axiom. -/
theorem obBot : EquivNF (somehow falsePLL) falsePLL :=
  ⟨.mp .nobot_ax (.hyp (by simp)), .exfalso (.hyp (by simp)) _⟩

/-- `◯(A ∧ B) ≡ ◯A ∧ ◯B` — the strong-monad laws (PLL already). -/
theorem obAnd {A B : PLLFormula} :
    EquivNF (somehow (A.and B)) ((somehow A).and (somehow B)) := by
  constructor
  · exact andI (ob_mono (.of_nd (.andElim1 (ψ := B) (.iden (by simp)))))
      (ob_mono (.of_nd (.andElim2 (φ := A) (.iden (by simp)))))
  · exact DerivUNoFall.of_nd
      (.laxElim (φ := A) (ψ := A.and B)
        (.andElim1 (ψ := somehow B) (.iden (by simp)))
        (.laxElim (φ := B) (ψ := A.and B)
          (.andElim2 (φ := somehow A) (.iden (by simp)))
          (.laxIntro (.andIntro (.iden (by simp)) (.iden (by simp))))))

/-- `◯(A ∨ B) ≡ ◯A ∨ ◯B` — the distribution scheme (this is its single
point of use in the normalisation). -/
theorem obOr {A B : PLLFormula} :
    EquivNF (somehow (A.or B)) ((somehow A).or (somehow B)) := by
  constructor
  · exact DerivUNoFall.mp (.of_derivU (DerivU.dist A B)) (.hyp (by simp))
  · exact orE (A := somehow A) (B := somehow B) (.hyp (by simp))
      (comp (X := somehow A)
        (ob_mono (.of_nd (.orIntro1 (.iden (by simp))))) (.hyp (by simp)))
      (comp (X := somehow B)
        (ob_mono (.of_nd (.orIntro2 (.iden (by simp))))) (.hyp (by simp)))

/-- `◯◯A ≡ ◯A` — idempotence (PLL already). -/
theorem obOb {A : PLLFormula} :
    EquivNF (somehow (somehow A)) (somehow A) :=
  ⟨.of_nd (.laxElim (φ := somehow A) (ψ := A) (.iden (by simp))
      (.iden (by simp))),
   .of_nd (.laxIntro (.iden (by simp)))⟩

/-! ## 3. The ◯-normal form -/

/-- Apply `◯` to a formula, pushing it through `⊥`, `∧`, `∨` and collapsing
`◯◯`; it comes to rest on atoms and implications. -/
def obApp : PLLFormula → PLLFormula
  | .prop a => (PLLFormula.prop a).somehow
  | .falsePLL => .falsePLL
  | .and A B => (obApp A).and (obApp B)
  | .or A B => (obApp A).or (obApp B)
  | .ifThen A B => (A.ifThen B).somehow
  | .somehow A => A.somehow

/-- ◯-normal form: every `◯` sits on an atom or an implication. -/
def nf : PLLFormula → PLLFormula
  | .prop a => .prop a
  | .falsePLL => .falsePLL
  | .and A B => (nf A).and (nf B)
  | .or A B => (nf A).or (nf B)
  | .ifThen A B => (nf A).ifThen (nf B)
  | .somehow A => obApp (nf A)

/-- The normal-form shape predicate. -/
def ObNormal : PLLFormula → Prop
  | .prop _ => True
  | .falsePLL => True
  | .and A B => ObNormal A ∧ ObNormal B
  | .or A B => ObNormal A ∧ ObNormal B
  | .ifThen A B => ObNormal A ∧ ObNormal B
  | .somehow (.prop _) => True
  | .somehow (.ifThen A B) => ObNormal A ∧ ObNormal B
  | .somehow _ => False

theorem obApp_equiv : ∀ A : PLLFormula, EquivNF (obApp A) A.somehow
  | .prop _ => .refl _
  | .falsePLL => obBot.symm
  | .and A B =>
      (and_congr (obApp_equiv A) (obApp_equiv B)).trans obAnd.symm
  | .or A B =>
      (or_congr (obApp_equiv A) (obApp_equiv B)).trans obOr.symm
  | .ifThen _ _ => .refl _
  | .somehow _ => obOb.symm

/-- **Normalisation is sound**: `nf A` is interderivable with `A`. -/
theorem nf_equiv : ∀ A : PLLFormula, EquivNF (nf A) A
  | .prop _ => .refl _
  | .falsePLL => .refl _
  | .and A B => and_congr (nf_equiv A) (nf_equiv B)
  | .or A B => or_congr (nf_equiv A) (nf_equiv B)
  | .ifThen A B => imp_congr (nf_equiv A) (nf_equiv B)
  | .somehow A => (obApp_equiv (nf A)).trans (ob_congr (nf_equiv A))

theorem obApp_normal : ∀ {A : PLLFormula}, ObNormal A → ObNormal (obApp A)
  | .prop _, _ => trivial
  | .falsePLL, _ => trivial
  | .and _ _, h => ⟨obApp_normal h.1, obApp_normal h.2⟩
  | .or _ _, h => ⟨obApp_normal h.1, obApp_normal h.2⟩
  | .ifThen _ _, h => h
  | .somehow _, h => h

/-- **Normalisation lands in normal form.** -/
theorem nf_normal : ∀ A : PLLFormula, ObNormal (nf A)
  | .prop _ => trivial
  | .falsePLL => trivial
  | .and A B => ⟨nf_normal A, nf_normal B⟩
  | .or A B => ⟨nf_normal A, nf_normal B⟩
  | .ifThen A B => ⟨nf_normal A, nf_normal B⟩
  | .somehow A => obApp_normal (nf_normal A)

/-! ## 4. Derivability is invariant under normalisation -/

/-- Simultaneous cut: replace the whole context by one that entails it. -/
theorem ctx_entail : ∀ {Γ Γ' : List PLLFormula} {C : PLLFormula},
    (∀ A ∈ Γ, DerivUNoFall Γ' A) → DerivUNoFall Γ C → DerivUNoFall Γ' C
  | [], _, _, _, hd => hd.rename (by simp)
  | A :: Γ, _, _, H, hd =>
      DerivUNoFall.mp
        (ctx_entail (fun B hB => H B (List.mem_cons_of_mem _ hB)) hd.deduction)
        (H A (List.mem_cons_self ..))

/-- **Derivability is invariant under ◯-normalisation** (both context and
conclusion). -/
theorem nf_iff (Γ : List PLLFormula) (C : PLLFormula) :
    DerivUNoFall Γ C ↔ DerivUNoFall (Γ.map nf) (nf C) := by
  constructor
  · intro h
    refine comp (nf_equiv C).2 (ctx_entail (fun A hA => ?_) h)
    exact comp (nf_equiv A).1 (.hyp (List.mem_map.mpr ⟨A, hA, rfl⟩))
  · intro h
    refine comp (nf_equiv C).1 (ctx_entail (fun B hB => ?_) h)
    obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hB
    exact comp (nf_equiv A).2 (.hyp hA)

/-! ## 5. The ◯-free fragment is exactly IPC -/

/-- Renaming for `IPLND` (weakening, exchange, contraction in one). -/
theorem _root_.PLLND.IPLND.rename : ∀ {Γ Γ' : List PLLFormula} {φ : PLLFormula},
    (∀ ψ ∈ Γ, ψ ∈ Γ') → IPLND Γ φ → IPLND Γ' φ := by
  intro Γ Γ' φ H h
  induction h generalizing Γ' with
  | iden h => exact .iden (H _ h)
  | falsoElim φ _ ih => exact .falsoElim φ (ih H)
  | impIntro _ ih =>
      refine .impIntro (ih ?_)
      intro ψ h
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (H ψ h)
  | impElim _ _ ih₁ ih₂ => exact .impElim (ih₁ H) (ih₂ H)
  | andIntro _ _ ih₁ ih₂ => exact .andIntro (ih₁ H) (ih₂ H)
  | andElim1 _ ih => exact .andElim1 (ih H)
  | andElim2 _ ih => exact .andElim2 (ih H)
  | orIntro1 _ ih => exact .orIntro1 (ih H)
  | orIntro2 _ ih => exact .orIntro2 (ih H)
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      refine .orElim (ih₀ H) (ih₁ ?_) (ih₂ ?_) <;>
        · intro ψ h
          rcases List.mem_cons.mp h with rfl | h
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (H ψ h)

/-- `IPLND` embeds into `LaxND`. -/
theorem _root_.PLLND.IPLND.toLax {Γ : List PLLFormula} {φ : PLLFormula}
    (h : IPLND Γ φ) : Nonempty (LaxND Γ φ) := by
  induction h with
  | iden h => exact ⟨.iden h⟩
  | falsoElim φ _ ih => obtain ⟨p⟩ := ih; exact ⟨.falsoElim φ p⟩
  | impIntro _ ih => obtain ⟨p⟩ := ih; exact ⟨.impIntro p⟩
  | impElim _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂; exact ⟨.impElim p₁ p₂⟩
  | andIntro _ _ ih₁ ih₂ =>
      obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂; exact ⟨.andIntro p₁ p₂⟩
  | andElim1 _ ih => obtain ⟨p⟩ := ih; exact ⟨.andElim1 p⟩
  | andElim2 _ ih => obtain ⟨p⟩ := ih; exact ⟨.andElim2 p⟩
  | orIntro1 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro1 p⟩
  | orIntro2 _ ih => obtain ⟨p⟩ := ih; exact ⟨.orIntro2 p⟩
  | orElim _ _ _ ih₀ ih₁ ih₂ =>
      obtain ⟨p₀⟩ := ih₀; obtain ⟨p₁⟩ := ih₁; obtain ⟨p₂⟩ := ih₂
      exact ⟨.orElim p₀ p₁ p₂⟩

/-- Strip a prefix of `[]`-derivable formulas off an `IPLND` context. -/
theorem _root_.PLLND.IPLND.strip : ∀ {Δ Γ : List PLLFormula} {C : PLLFormula},
    (∀ θ ∈ Δ, IPLND [] θ) → IPLND (Δ ++ Γ) C → IPLND Γ C
  | [], _, _, _, h => h
  | θ :: Δ, Γ, C, H, h =>
      have h' : IPLND (Δ ++ Γ) (θ.ifThen C) := .impIntro h
      have h'' : IPLND Γ (θ.ifThen C) :=
        IPLND.strip (fun τ hτ => H τ (List.mem_cons_of_mem _ hτ)) h'
      .impElim h'' ((H θ (List.mem_cons_self ..)).rename (by simp))

/-- **The ◯-free fragment of PCLL + `¬◯⊥` is exactly IPC**: on `◯`-free
sequents the extension proves precisely the `IPLND`-derivable ones.  Forward
by erasure (the axiom erases to `⊥ ⊃ ⊥`, a distribution instance to
`(A ∨ B) ⊃ (A ∨ B)`); backward by embedding. -/
theorem derivUNoFall_iff_IPLND {Γ : List PLLFormula} {C : PLLFormula}
    (hC : isIPL C) (hΓ : ∀ ψ ∈ Γ, isIPL ψ) :
    DerivUNoFall Γ C ↔ IPLND Γ C := by
  constructor
  · rintro ⟨L, hL, ⟨p⟩⟩
    have h := conservativity_prop p
    rw [erase_eq_self_of_isIPL C hC, List.map_append, List.map_cons,
      map_erase_eq_self Γ hΓ] at h
    have hax : ∀ θ ∈ (L.map erase ++ [erase nobot]), IPLND [] θ := by
      intro θ hθ
      rcases List.mem_append.mp hθ with hθ | hθ
      · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hθ
        obtain ⟨A, B, rfl⟩ := hL τ hτ
        exact .impIntro (.iden (by simp [erase]))
      · simp only [List.mem_singleton] at hθ
        subst hθ
        exact .impIntro (.iden (by simp [erase]))
    refine IPLND.strip hax ?_
    simpa [List.append_assoc] using h
  · intro h
    obtain ⟨p⟩ := h.toLax
    exact .of_nd p

end NoFall
end PLLND

/-! ### Axiom audit -/

/-- info: 'PLLND.NoFall.nf_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.nf_equiv

/-- info: 'PLLND.NoFall.nf_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.nf_iff

/-- info: 'PLLND.NoFall.derivUNoFall_iff_IPLND' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.NoFall.derivUNoFall_iff_IPLND

/-! ## 6. The uniform-interpolation specification layer

The target of the programme, stated once, with the one-variable theorems of
`PLLNoFall.lean` repackaged as its base instances.  `IsExUIOn T φ E` is the
∃-side Pitts specification with the test class abstracted: for the full
theorem `T = PFree p` (all `p`-free formulas); the proved one-variable case
is the instance `T = VarFree`, which on the one-variable language coincides
with `PFree p`. -/

namespace PLLND.NoFall

/-- `p` does not occur. -/
def PFree (p : String) : PLLFormula → Prop
  | .prop a => a ≠ p
  | .falsePLL => True
  | .and A B => PFree p A ∧ PFree p B
  | .or A B => PFree p A ∧ PFree p B
  | .ifThen A B => PFree p A ∧ PFree p B
  | .somehow A => PFree p A

theorem PFree.of_varFree {p : String} {A : PLLFormula} (h : VarFree A) :
    PFree p A := by
  induction A with
  | prop a => exact h.elim
  | falsePLL => exact trivial
  | and A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | or A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | ifThen A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | somehow A ih => exact ih h

/-- The ∃-side uniform-interpolation specification over a test class `T`:
`E` is in `T`, is a consequence of `φ`, and for every `ψ ∈ T`,
`φ ⊢ ψ` iff `E ⊢ ψ`. -/
def IsExUIOn (T : PLLFormula → Prop) (φ E : PLLFormula) : Prop :=
  T E ∧ DerivUNoFall [φ] E ∧
    ∀ ψ, T ψ → (DerivUNoFall [φ] ψ ↔ DerivUNoFall [E] ψ)

/-- The ∀-side specification over a test class `T`. -/
def IsAllUIOn (T : PLLFormula → Prop) (φ A : PLLFormula) : Prop :=
  T A ∧ DerivUNoFall [A] φ ∧
    ∀ ψ, T ψ → (DerivUNoFall [ψ] φ ↔ DerivUNoFall [ψ] A)

/-- The one-variable theorem, repackaged: every `φ` has a variable-free
∃-interpolant. -/
theorem exUI_varFree (φ : PLLFormula) : ∃ E, IsExUIOn VarFree φ E :=
  exUI φ

/-- The one-variable theorem, repackaged: every `φ` has a variable-free
∀-interpolant. -/
theorem allUI_varFree (φ : PLLFormula) : ∃ A, IsAllUIOn VarFree φ A :=
  allUI φ

/-- Interpolants for a given test class are unique up to
interderivability. -/
theorem IsExUIOn.unique {T : PLLFormula → Prop} {φ E E' : PLLFormula}
    (h : IsExUIOn T φ E) (h' : IsExUIOn T φ E') : EquivNF E E' :=
  ⟨(h.2.2 E' h'.1).mp h'.2.1, (h'.2.2 E h.1).mp h.2.1⟩

theorem IsAllUIOn.unique {T : PLLFormula → Prop} {φ A A' : PLLFormula}
    (h : IsAllUIOn T φ A) (h' : IsAllUIOn T φ A') : EquivNF A A' :=
  ⟨(h'.2.2 A h.1).mp h.2.1, (h.2.2 A' h'.1).mp h'.2.1⟩

/-- **The open target of the programme** (stated, not asserted): uniform
interpolation for PCLL + `¬◯⊥` in full — every variable eliminable against
all `p`-free formulas. -/
def UniformInterpolation : Prop :=
  ∀ (p : String) (φ : PLLFormula),
    (∃ E, IsExUIOn (PFree p) φ E) ∧ (∃ A, IsAllUIOn (PFree p) φ A)

end PLLND.NoFall
