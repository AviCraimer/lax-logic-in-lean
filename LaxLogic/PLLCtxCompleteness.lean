import LaxLogic.PLLFiniteModel
import LaxLogic.PLLTheorems

/-!
# Context-completeness for PLL (Fairtlough–Mendler, TYPES 2000, Theorem 6)

Reference: Matt Fairtlough & Michael Mendler, *On the Logical Content of
Computational Type Theory: A Solution to Curry's Problem*, TYPES 2000,
LNCS 2277, pp. 63–78.

## Phase-1 target statement (located)

**Theorem 6.**  For every lax proposition `φ`,
  `PLL ⊢ φ   ⟺   ∀ C ∈ 𝕊,  IPL ⊢ φ^C`
where
* a *basic constraint* is `[K,L]φ := K ⊃ (φ ∨ L)` (`K,L` arbitrary IPL formulas);
* a *standard constraint* `C ∈ 𝕊` is a finite conjunction `⨅_{i<n} [Kᵢ,Lᵢ]`
  (depth `n`; depth-0 = `⊤ = [false,false]`);
* `φ^C` is `φ` with **every** subformula `◯ψ` replaced by `C[ψ^C]` — the *same*
  `C` at every `◯` (independent expansion is unsound, paper footnote p.2).

## What the codebase already provides (verified in Phase 1)

* `PLLND.ConstraintModel` (`LaxLogic/PLLKripke.lean`) is **exactly** the paper's
  Def 3/4: `(W, Ri, Rm, F, V)` with `Rm ⊆ Ri`, `F` `Ri`-hereditary, `V`
  hereditary and full on `F`, and the ◯-clause
  `force w (◯φ) = ∀ v, Ri w v → ∃ u, Rm v u ∧ force u φ`.
  (Codebase uses *preorders*, the paper *partial orders*; immaterial for
  soundness/completeness/FMP.)
* `PLLND.soundness`, `PLLND.completeness`, `PLLND.consequence_iff_derivable`
  (`LaxLogic/PLLCompleteness.lean`) = the paper's cited **Theorem 5** (F&M 1997).
* `PLLND.finite_model_property` (`LaxLogic/PLLFiniteModel.lean`) = **finite**
  constraint-model completeness (F&M Thm 4.6) — the finite-model input Theorem 6's
  completeness direction needs.
* `LaxND.rename`/`weaken` (structural), `iff_congr_*`, `strong_extensionality`,
  `conservativity` (PLL conservative over IPL) — `PLLNDCore`/`PLLTheorems`.

## This file

The **soundness direction** of Theorem 6 (the reusable tool, priority 1):
`PLL ⊢ φ  ⟹  IPL ⊢ φ^C` for every standard constraint `C`, in full sequent form
`LaxND Γ φ → LaxND (Γ.map (·^C)) (φ^C)` (`translate`).  This is the "each context
provides a sound interpretation of CTT" content, mechanised for arbitrary standard
constraints.  Because `φ^C` is `◯`-free when `C`'s `K,L` are, it is a genuine IPL
proof (via `conservativity`).

The **completeness direction** (Lemma 7: express `◯` over a finite model as a single
standard constraint) is the harder half; its status is tracked at the end of the file.

## Paper-formalisation status (Fairtlough–Mendler, TYPES 2000, LNCS 2277)

| Result                                 | Status (this file / codebase)                       |
|----------------------------------------|-----------------------------------------------------|
| **Thm 5** (soundness+completeness)     | codebase `PLLND.consequence_iff_derivable`          |
| Kripke models (Def 3/4)                | codebase `PLLND.ConstraintModel`                    |
| **Thm 6** (context-completeness)       | ✔ `thm6` (both directions, `Lemma 7` = `lemma7`)    |
| **Lemma 7** (◯ as one constraint)      | ✔ `lemma7` (preorder-correct, finiteness only)      |
| **Lemma 8** (depth-`n` ⇒ `χ_m^C`)      | ✔ `lemma8` / `lemma8_valid` (semantic)              |
| **Lemma 9** (`χ_m` non-theorem)        | ✔ `lemma9` (explicit ℕ-model family + bisimulation) |
| **Corollary 10** (finite ⊄ complete)   | ✔ `corollary10`                                     |
| **Thm 2** (𝕊 a Boolean algebra)        | ✔ `thm2_boolean_algebra` (both complement laws,     |
|                                        |   complement `Cbar` = powerset-free De Morgan join, |
|                                        |   `compl_unique`); bundled `BooleanAlgebra CQuot`   |
| λ-terms `C_I,C_M,C_S,C_Ext` (§1)       | ◯ derivation-level realisers `unitC`/`bindC` only   |

Every headline theorem is `sorry`-free (`#print axioms` at end of file: only
`propext`/`Quot.sound`/`Classical.choice`).

**§7 (not formalised, recorded per project thread).**  The paper's final section
represents `◯` abstractly: the algebraic counterpart of `◯` on a complete Heyting
algebra `H` is a *nucleus*, and the nuclei on `H` themselves form a cHA `𝒩(H) =
(N(H), ≤, ∧, →, ⋁)` — the *assembly* of `H`.  For a finite `Υ M*` this `𝒩(Υ M*)`
is a finite Boolean algebra, syntactically the constraint algebra `𝕊` of Thm 2.
This is the entry point of the project's nucleus/assembly-tower thread.
-/

open PLLFormula

namespace PLLND
namespace Ctx

/-! ## Standard constraints and the constraint substitution `φ^C` -/

/-- A basic constraint `[K,L]` acts on `x` as `K ⊃ (x ∨ L)`. -/
def basic (K L x : PLLFormula) : PLLFormula := K.ifThen (x.or L)

/-- A standard constraint is a finite list of `(K,L)` pairs.  It acts on `x` as the
conjunction `⋀ᵢ (Kᵢ ⊃ (x ∨ Lᵢ))`; the empty list is depth-0 `⊤`. -/
abbrev StdCtx := List (PLLFormula × PLLFormula)

/-- `C[x]` — the standard constraint `C` applied to `x`. -/
def applyC : StdCtx → PLLFormula → PLLFormula
  | [], _ => truePLL
  | (K, L) :: rest, x => (basic K L x).and (applyC rest x)

/-- The constraint substitution `φ^C`: replace every `◯ψ` by `C[ψ^C]`. -/
def subC (C : StdCtx) : PLLFormula → PLLFormula
  | .prop a     => .prop a
  | .falsePLL   => .falsePLL
  | .and φ ψ    => .and (subC C φ) (subC C ψ)
  | .or φ ψ     => .or (subC C φ) (subC C ψ)
  | .ifThen φ ψ => .ifThen (subC C φ) (subC C ψ)
  | .somehow φ  => applyC C (subC C φ)

/-! ## The C-monad structure of a standard constraint in IPL

Each standard constraint `C` is a strong monad on IPL: it supports a `unit`
`A ⊢ C[A]` and a Kleisli `bind` `Γ ⊢ C[A]`, `A::Γ ⊢ C[B]` ⟹ `Γ ⊢ C[B]`.  These
are exactly what the `◯`-rules (`laxIntro`, `laxElim`) translate to. -/

/-- `⊤` is derivable in any context. -/
def truePLL_intro (Δ : List PLLFormula) : LaxND Δ truePLL :=
  .impIntro (.iden (List.mem_cons_self ..))

/-- **Unit** `A ⊢ C[A]`: the translation of `◯I`.  (Paper's `C_I`.) -/
def unitC (C : StdCtx) {Δ : List PLLFormula} {A : PLLFormula}
    (p : LaxND Δ A) : LaxND Δ (applyC C A) := by
  induction C with
  | nil => exact truePLL_intro Δ
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      exact .andIntro (.impIntro (.orIntro1 (p.weaken K))) ih

/-- **Bind** `Γ ⊢ C[A]`, `A::Γ ⊢ C[B]`  ⟹  `Γ ⊢ C[B]`: the translation of `◯E`.
For a conjunction of basic constraints the bind is componentwise. -/
def bindC (C : StdCtx) {Δ : List PLLFormula} {A B : PLLFormula}
    (h1 : LaxND Δ (applyC C A)) (h2 : LaxND (A :: Δ) (applyC C B)) :
    LaxND Δ (applyC C B) := by
  induction C with
  | nil => exact truePLL_intro Δ
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      refine .andIntro ?_ (ih h1.andElim2 h2.andElim2)
      -- goal: LaxND Δ (basic K L B) = LaxND Δ (K ⊃ (B ∨ L))
      apply LaxND.impIntro
      -- context K :: Δ, goal B ∨ L
      have hA : LaxND (K :: Δ) (A.or L) :=
        .impElim (h1.andElim1.weaken K) (.iden (List.mem_cons_self ..))
      refine .orElim hA ?_ ?_
      · -- case A: context A :: K :: Δ
        have hKB : LaxND (A :: K :: Δ) (K.ifThen (B.or L)) :=
          h2.andElim1.rename (by
            intro ψ hψ
            rcases List.mem_cons.mp hψ with rfl | h
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
        exact .impElim hKB (.iden (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      · -- case L: context L :: K :: Δ
        exact .orIntro2 (.iden (List.mem_cons_self ..))

/-! ## Soundness direction of Theorem 6 -/

/-- **Theorem 6, soundness direction (sequent form).**  Every standard constraint
`C` gives a sound interpretation of PLL in IPL: a PLL derivation `Γ ⊢ φ` translates
to an IPL derivation `Γ^C ⊢ φ^C`. -/
def translate (C : StdCtx) : {Γ : List PLLFormula} → {φ : PLLFormula} →
    LaxND Γ φ → LaxND (Γ.map (subC C)) (subC C φ)
  | _, _, .iden h        => .iden (List.mem_map_of_mem h)
  | _, _, .falsoElim φ p => .falsoElim (subC C φ) (translate C p)
  | _, _, .impIntro p    => .impIntro (translate C p)
  | _, _, .impElim p₁ p₂ => .impElim (translate C p₁) (translate C p₂)
  | _, _, .andIntro p₁ p₂ => .andIntro (translate C p₁) (translate C p₂)
  | _, _, .andElim1 p    => .andElim1 (translate C p)
  | _, _, .andElim2 p    => .andElim2 (translate C p)
  | _, _, .orIntro1 p    => .orIntro1 (translate C p)
  | _, _, .orIntro2 p    => .orIntro2 (translate C p)
  | _, _, .orElim p₀ p₁ p₂ => .orElim (translate C p₀) (translate C p₁) (translate C p₂)
  | _, _, .laxIntro p    => unitC C (translate C p)
  | _, _, .laxElim p₁ p₂ => bindC C (translate C p₁) (translate C p₂)

/-- **Theorem 6, soundness direction (closed form).**  If `PLL ⊢ φ` then
`IPL ⊢ φ^C` for every standard constraint `C`. -/
theorem thm6_soundness (C : StdCtx) {φ : PLLFormula}
    (h : Nonempty (LaxND [] φ)) : Nonempty (LaxND [] (subC C φ)) :=
  h.elim fun p => ⟨translate C p⟩

/-- Contrapositive, the form used to refute PLL-entailments: if some standard
constraint `C` makes `φ^C` IPL-**un**provable, then `φ` is not a PLL theorem. -/
theorem not_provable_of_subC (C : StdCtx) {φ : PLLFormula}
    (h : ¬ Nonempty (LaxND [] (subC C φ))) : ¬ Nonempty (LaxND [] φ) :=
  fun hp => h (thm6_soundness C hp)

/-! ## `φ^C` is genuinely IPL (◯-free) when `C` is

The paper's `K,L` range over IPL formulas.  When they do, `φ^C` contains no `◯`,
so `LaxND [] (subC C φ)` is a genuine IPL proof (via `PLLND.conservativity`). -/

/-- A standard constraint is IPL when all its `K,L` are `◯`-free. -/
def CtxIsIPL (C : StdCtx) : Prop := ∀ p ∈ C, isIPL p.1 ∧ isIPL p.2

theorem applyC_isIPL {C : StdCtx} (hC : CtxIsIPL C) {x : PLLFormula}
    (hx : isIPL x) : isIPL (applyC C x) := by
  induction C with
  | nil => exact ⟨trivial, trivial⟩
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hKL := hC (K, L) (List.mem_cons_self ..)
      refine ⟨⟨hKL.1, hx, hKL.2⟩, ih (fun p hp => hC p (List.mem_cons_of_mem _ hp))⟩

/-- If every `K,L` in `C` is `◯`-free, then `φ^C` is `◯`-free for every `φ`. -/
theorem subC_isIPL {C : StdCtx} (hC : CtxIsIPL C) : ∀ φ, isIPL (subC C φ)
  | .prop _     => trivial
  | .falsePLL   => trivial
  | .and φ ψ    => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .or φ ψ     => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .ifThen φ ψ => ⟨subC_isIPL hC φ, subC_isIPL hC ψ⟩
  | .somehow φ  => applyC_isIPL hC (subC_isIPL hC φ)

end Ctx
end PLLND

#print axioms PLLND.Ctx.thm6_soundness

/-! ============================================================================
# Completeness direction of Theorem 6

The plan (Fairtlough–Mendler, TYPES 2000, Lemma 7 + Thm 6 completeness):

1. `PLL ⊬ φ` ⟹ (FMP) a **finite** constraint model `M` with a world refuting `φ`.
2. **Semantic completion** `M*`: adjoin a fresh atom `α_w` per world `w`, forced
   at `x` iff `Ri w x` (or `x` fallible).  `M*` agrees with `M` on old atoms.
3. **Lemma 7**: over `M*`, `◯ψ` is forced exactly where the single standard
   constraint `C = ⨅_{u∈Stab} [α_u , ⋁_{u'∈iSucc u} α_{u'}]` applied to `ψ` is.
4. **Congruence**: replacing every `◯` by `C[·]` (i.e. `subC C`) preserves forcing
   in `M*`.  Hence `M* ⊭ subC C φ`, so `PLL ⊬ subC C φ` (soundness), and since
   `subC C φ` is `◯`-free this is `IPL ⊬ φ^C`.

The definitions are adapted to the codebase's **preorders** (the paper uses
partial orders): `Stab` = `Rm`-maximal *cluster* (`∀ t, Rm u t → Rm t u`) and
`iSucc` carries an explicit strictness clause (`¬ Ri v u`).  With these, Lemma 7
needs only **finiteness**, no antisymmetry.
============================================================================ -/

namespace PLLND
namespace Ctx

open Classical

/-! ## Section A — finite-preorder combinatorics (antisymmetry-free)

Two facts about a reflexive-transitive relation `R` on a finite type:
reaching a maximal cluster, and factoring a strict step through a cover. -/

/-- In a finite preorder, every nonempty set has an `R`-minimal *cluster*
element: some `m ∈ S` with no element of `S` strictly below it. -/
theorem exists_min_strict {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (S : Set W) (hS : S.Nonempty) :
    ∃ m ∈ S, ∀ x ∈ S, R x m → R m x := by
  classical
  let Rlt : W → W → Prop := fun a b => R a b ∧ ¬ R b a
  haveI : IsTrans W Rlt :=
    ⟨fun a b c ⟨hab, hba⟩ ⟨hbc, _⟩ => ⟨htrans hab hbc, fun hca => hba (htrans hbc hca)⟩⟩
  haveI : IsIrrefl W Rlt := ⟨fun _ ⟨h, hn⟩ => hn h⟩
  have hwf : WellFounded Rlt := Finite.wellFounded_of_trans_of_irrefl Rlt
  obtain ⟨m, hmS, hmin⟩ := hwf.has_min S hS
  refine ⟨m, hmS, fun x hxS hxm => ?_⟩
  by_contra hmx
  exact hmin x hxS ⟨hxm, hmx⟩

/-- From any `v`, a maximal cluster is reachable: `∃ u, R v u ∧ ∀ t, R u t → R t u`. -/
theorem exists_max_cluster {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c) (v : W) :
    ∃ u, R v u ∧ ∀ t, R u t → R t u := by
  obtain ⟨m, hmS, hmin⟩ :=
    exists_min_strict (W := W) (fun a b => R b a) hrefl
      (fun hab hbc => htrans hbc hab) {u | R v u} ⟨v, hrefl v⟩
  refine ⟨m, hmS, fun t hmt => ?_⟩
  exact hmin t (htrans hmS hmt) hmt

/-- A strict `R`-step `R u v`, `¬ R v u` factors through a *cover* of `u`: an
immediate strict successor `u'` (in the cluster sense) with `R u' v`. -/
theorem exists_cover {W : Type} [Finite W] (R : W → W → Prop)
    (hrefl : ∀ x, R x x) (htrans : ∀ {a b c}, R a b → R b c → R a c)
    (u v : W) (huv : R u v) (hvu : ¬ R v u) :
    ∃ u', (R u u' ∧ ¬ R u' u ∧ ∀ t, R u t → R t u' → R t u ∨ R u' t) ∧ R u' v := by
  obtain ⟨m, hmB, hmin⟩ :=
    exists_min_strict (W := W) R hrefl htrans
      {t | R u t ∧ ¬ R t u ∧ R t v} ⟨v, huv, hvu, hrefl v⟩
  obtain ⟨hum, hmu, hmv⟩ := hmB
  refine ⟨m, ⟨hum, hmu, fun t hut htm => ?_⟩, hmv⟩
  by_cases htu : R t u
  · exact Or.inl htu
  · exact Or.inr (hmin t ⟨hut, htu, htrans htm hmv⟩ htm)

/-! ## Section B — the semantic completion `M*` -/

/-- The propositional atoms occurring in a formula. -/
def atoms : PLLFormula → Finset String
  | .prop a     => {a}
  | .falsePLL   => ∅
  | .and φ ψ    => atoms φ ∪ atoms ψ
  | .or φ ψ     => atoms φ ∪ atoms ψ
  | .ifThen φ ψ => atoms φ ∪ atoms ψ
  | .somehow φ  => atoms φ

/-- A finite type admits an injective naming by strings avoiding any given finite
set — the fresh atoms `α_w` of the completion. -/
theorem exists_freshNames (M : ConstraintModel) [Finite M.W] (A : Finset String) :
    ∃ f : M.W → String, Function.Injective f ∧ ∀ w, f w ∉ A := by
  classical
  have hInf : Infinite {s : String // s ∉ A} := by
    have h : ({s : String | s ∈ A}).Finite := A.finite_toSet
    exact (h.infinite_compl).to_subtype
  letI := Fintype.ofFinite M.W
  let e : M.W ≃ Fin (Fintype.card M.W) := Fintype.equivFin M.W
  let g : M.W → ℕ := fun w => (e w).val
  have hg : Function.Injective g := fun a b hab => e.injective (Fin.val_injective hab)
  let ne : ℕ ↪ {s : String // s ∉ A} := Infinite.natEmbedding _
  refine ⟨fun w => (ne (g w)).val, fun a b hab => ?_, fun w => (ne (g w)).property⟩
  exact hg (ne.injective (Subtype.ext hab))

section Completion

open Classical

variable (M : ConstraintModel) [Finite M.W] (φ₀ : PLLFormula)

/-- The fresh naming `α_·` for the completion, avoiding `atoms φ₀`. -/
noncomputable def nm : M.W → String := (exists_freshNames M (atoms φ₀)).choose

theorem nm_inj : Function.Injective (nm M φ₀) :=
  (exists_freshNames M (atoms φ₀)).choose_spec.1

theorem nm_fresh (w : M.W) : nm M φ₀ w ∉ atoms φ₀ :=
  (exists_freshNames M (atoms φ₀)).choose_spec.2 w

/-- Valuation of the completion: at fresh names `nm w`, force `{x | Ri w x} ∪ F`
(the up-set of `w`, closed under `F` for fullness); elsewhere unchanged. -/
noncomputable def Vstar : String → Set M.W := fun s =>
  if h : ∃ w, nm M φ₀ w = s then {x | M.Ri h.choose x ∨ x ∈ M.F} else M.V s

theorem Vstar_name (w : M.W) :
    Vstar M φ₀ (nm M φ₀ w) = {x | M.Ri w x ∨ x ∈ M.F} := by
  have hex : ∃ w', nm M φ₀ w' = nm M φ₀ w := ⟨w, rfl⟩
  have hw : hex.choose = w := nm_inj M φ₀ hex.choose_spec
  simp only [Vstar, dif_pos hex, hw]

theorem Vstar_eq_of_not_range {a : String} (h : ¬ ∃ w, nm M φ₀ w = a) :
    Vstar M φ₀ a = M.V a := by
  simp only [Vstar, dif_neg h]

theorem Vstar_hered : ∀ {a : String} {x y : M.W},
    M.Ri x y → x ∈ Vstar M φ₀ a → y ∈ Vstar M φ₀ a := by
  intro a x y hxy hx
  by_cases h : ∃ w, nm M φ₀ w = a
  · rw [Vstar, dif_pos h] at hx ⊢
    rcases hx with h1 | h2
    · exact Or.inl (M.trans_i h1 hxy)
    · exact Or.inr (M.hered_F hxy h2)
  · rw [Vstar, dif_neg h] at hx ⊢
    exact M.hered_V hxy hx

theorem Vstar_full : ∀ {a : String} {x : M.W}, x ∈ M.F → x ∈ Vstar M φ₀ a := by
  intro a x hx
  by_cases h : ∃ w, nm M φ₀ w = a
  · rw [Vstar, dif_pos h]; exact Or.inr hx
  · rw [Vstar, dif_neg h]; exact M.full_F hx

/-- The semantic completion `M*`: `M` with the enriched valuation. -/
noncomputable def Mstar : ConstraintModel :=
  { M with V := Vstar M φ₀, hered_V := Vstar_hered M φ₀, full_F := Vstar_full M φ₀ }

@[simp] theorem Mstar_W : (Mstar M φ₀).W = M.W := rfl
@[simp] theorem Mstar_Ri : (Mstar M φ₀).Ri = M.Ri := rfl
@[simp] theorem Mstar_Rm : (Mstar M φ₀).Rm = M.Rm := rfl
@[simp] theorem Mstar_F : (Mstar M φ₀).F = M.F := rfl

/-- The fresh propositional variable `α_w`. -/
noncomputable def alpha (w : M.W) : PLLFormula := PLLFormula.prop (nm M φ₀ w)

/-- Characterisation of `α_w` in `M*` (`property (a)`): forced at `x` iff `Ri w x`
(or `x` fallible). -/
theorem force_alpha (w x : M.W) :
    (Mstar M φ₀).force x (alpha M φ₀ w) ↔ M.Ri w x ∨ x ∈ M.F := by
  have h1 : (Mstar M φ₀).force x (alpha M φ₀ w) = (x ∈ Vstar M φ₀ (nm M φ₀ w)) := rfl
  rw [h1, Vstar_name]
  exact Iff.rfl

/-- Coincidence (`property (b)`): `M*` agrees with `M` on any formula whose atoms
avoid the fresh names — in particular on `φ₀` and its subformulas. -/
theorem force_coincide : ∀ (ψ : PLLFormula), (∀ w, nm M φ₀ w ∉ atoms ψ) →
    ∀ (x : M.W), ((Mstar M φ₀).force x ψ ↔ M.force x ψ) := by
  intro ψ
  induction ψ with
  | prop a =>
      intro hψ x
      have hnr : ¬ ∃ w, nm M φ₀ w = a := by
        rintro ⟨w, rfl⟩
        exact hψ w (Finset.mem_singleton_self _)
      have h1 : (Mstar M φ₀).force x (.prop a) = (x ∈ Vstar M φ₀ a) := rfl
      have h2 : M.force x (.prop a) = (x ∈ M.V a) := rfl
      rw [h1, h2, Vstar_eq_of_not_range M φ₀ hnr]
  | falsePLL => intro hψ x; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact and_congr (ihφ hφ x) (ihψ hψ' x)
  | or φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact or_congr (ihφ hφ x) (ihψ hψ' x)
  | ifThen φ ψ ihφ ihψ =>
      intro hψ x
      have hφ : ∀ w, nm M φ₀ w ∉ atoms φ := fun w hw =>
        hψ w (Finset.mem_union_left _ hw)
      have hψ' : ∀ w, nm M φ₀ w ∉ atoms ψ := fun w hw =>
        hψ w (Finset.mem_union_right _ hw)
      exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr (ihφ hφ v) (ihψ hψ' v))
  | somehow φ ih =>
      intro hψ x
      exact forall_congr' fun v =>
        imp_congr Iff.rfl (exists_congr fun u => and_congr Iff.rfl (ih hψ u))

end Completion

/-! ## Section C — Lemma 7 -/

/-- Forcing of a constraint conjunction `C[x]` is the conjunction of the basic
constraints, over any model. -/
theorem force_applyC_iff (D : ConstraintModel) (C : StdCtx) (x : PLLFormula)
    (w : D.W) :
    D.force w (applyC C x) ↔ ∀ p ∈ C, D.force w (basic p.1 p.2 x) := by
  induction C with
  | nil =>
      constructor
      · intro _ p hp; exact (List.not_mem_nil hp).elim
      · intro _; exact fun v _ hv => hv
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      have hstep : D.force w (applyC ((K, L) :: tl) x) ↔
          D.force w (basic K L x) ∧ D.force w (applyC tl x) := Iff.rfl
      rw [hstep, ih]
      constructor
      · rintro ⟨hb, hrest⟩ p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hb
        · exact hrest p hp
      · intro h
        exact ⟨h (K, L) (List.mem_cons_self ..), fun p hp => h p (List.mem_cons_of_mem _ hp)⟩

/-- Finite disjunction of a list of formulas (empty = `⊥`). -/
def bigOr : List PLLFormula → PLLFormula
  | []       => .falsePLL
  | q :: rest => q.or (bigOr rest)

/-- Forcing of `bigOr L`: some disjunct is forced, or the world is fallible
(the empty disjunction `⊥` is still forced at fallible worlds). -/
theorem force_bigOr_iff (D : ConstraintModel) (L : List PLLFormula) (w : D.W) :
    D.force w (bigOr L) ↔ (∃ q ∈ L, D.force w q) ∨ w ∈ D.F := by
  induction L with
  | nil =>
      constructor
      · intro h; exact Or.inr h
      · rintro (⟨q, hq, _⟩ | h)
        · exact (List.not_mem_nil hq).elim
        · exact h
  | cons q rest ih =>
      have hstep : D.force w (bigOr (q :: rest)) ↔
          D.force w q ∨ D.force w (bigOr rest) := Iff.rfl
      rw [hstep, ih]
      constructor
      · rintro (hq | (⟨q', hq', hf'⟩ | hF))
        · exact Or.inl ⟨q, List.mem_cons_self .., hq⟩
        · exact Or.inl ⟨q', List.mem_cons_of_mem _ hq', hf'⟩
        · exact Or.inr hF
      · rintro (⟨q', hq', hf'⟩ | hF)
        · rcases List.mem_cons.mp hq' with rfl | hq'
          · exact Or.inl hf'
          · exact Or.inr (Or.inl ⟨q', hq', hf'⟩)
        · exact Or.inr (Or.inr hF)

section Lemma7

open Classical

attribute [local instance] Classical.propDecidable

variable (M : ConstraintModel) [Fintype M.W] (φ₀ : PLLFormula)

/-- A world is **stable** if it is `Rm`-maximal *up to cluster*: every `Rm`-successor
maps back.  (Preorder-correct form of the paper's "no proper modal successor".) -/
def Stab (u : M.W) : Prop := ∀ t, M.Rm u t → M.Rm t u

/-- `v` is an **immediate successor** (cover) of `u`: strictly `Ri`-above with
nothing strictly in between (up to cluster). -/
def iSucc (u v : M.W) : Prop :=
  M.Ri u v ∧ ¬ M.Ri v u ∧ ∀ t, M.Ri u t → M.Ri t v → M.Ri t u ∨ M.Ri v t

/-- The disjunction `⋁_{u'∈iSucc u} α_{u'}` (empty = `⊥`). -/
noncomputable def Ldis (u : M.W) : PLLFormula :=
  bigOr ((Finset.univ.filter (iSucc M u)).toList.map (alpha M φ₀))

/-- The single standard constraint `C = ⨅_{u∈Stab} [α_u , ⋁_{u'∈iSucc u} α_{u'}]`. -/
noncomputable def C0 : StdCtx :=
  (Finset.univ.filter (Stab M)).toList.map (fun u => (alpha M φ₀ u, Ldis M φ₀ u))

/-- Forcing of `Ldis u` in `M*`: some cover's variable is forced, or fallible. -/
theorem force_Ldis (u w : M.W) :
    (Mstar M φ₀).force w (Ldis M φ₀ u) ↔
      (∃ u', iSucc M u u' ∧ (Mstar M φ₀).force w (alpha M φ₀ u')) ∨ w ∈ M.F := by
  rw [Ldis, force_bigOr_iff]
  constructor
  · rintro (⟨q, hq, hfq⟩ | hF)
    · rw [List.mem_map] at hq
      obtain ⟨u', hu', rfl⟩ := hq
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu'
      exact Or.inl ⟨u', hu', hfq⟩
    · exact Or.inr hF
  · rintro (⟨u', hu', hf⟩ | hF)
    · refine Or.inl ⟨alpha M φ₀ u', ?_, hf⟩
      rw [List.mem_map]
      have hmem : u' ∈ (Finset.univ.filter (iSucc M u)).toList := by
        simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu'
      exact ⟨u', hmem, rfl⟩
    · exact Or.inr hF

/-- Forcing of `C[ψ]` in `M*`, unfolded over stable worlds. -/
theorem force_applyC_C0 (ψ : PLLFormula) (w : M.W) :
    (Mstar M φ₀).force w (applyC (C0 M φ₀) ψ) ↔
      ∀ u, Stab M u →
        (Mstar M φ₀).force w (basic (alpha M φ₀ u) (Ldis M φ₀ u) ψ) := by
  rw [force_applyC_iff]
  constructor
  · intro h u hu
    apply h (alpha M φ₀ u, Ldis M φ₀ u)
    rw [C0, List.mem_map]
    have hmem : u ∈ (Finset.univ.filter (Stab M)).toList := by
      simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]; exact hu
    exact ⟨u, hmem, rfl⟩
  · intro h p hp
    rw [C0, List.mem_map] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    simp only [Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact h u hu

/-- **Lemma 7.**  Over the completion `M*`, the modality `◯ψ` is forced exactly
where the single standard constraint `C0` applied to `ψ` is forced.  Uses only
finiteness (reachable maximal cluster + cover factorization), no antisymmetry. -/
theorem lemma7 (ψ : PLLFormula) (w : M.W) :
    (Mstar M φ₀).force w (.somehow ψ) ↔
      (Mstar M φ₀).force w (applyC (C0 M φ₀) ψ) := by
  constructor
  · -- (⟹)
    intro hSom
    rw [force_applyC_C0]
    intro u hu v hwv hav
    rw [force_alpha] at hav
    show (Mstar M φ₀).force v ψ ∨ (Mstar M φ₀).force v (Ldis M φ₀ u)
    rcases hav with hRiuv | hvF
    · by_cases hvu : M.Ri v u
      · -- v is in u's cluster: use stability of u
        have hRiwu : M.Ri w u := M.trans_i hwv hvu
        obtain ⟨z, hzrm, hzf⟩ := hSom u hRiwu
        have hzu : M.Ri z u := M.sub_mi (hu z hzrm)
        have hfu : (Mstar M φ₀).force u ψ := (Mstar M φ₀).force_hered hzu hzf
        exact Or.inl ((Mstar M φ₀).force_hered hRiuv hfu)
      · -- v strictly above u: factor through a cover
        obtain ⟨u', hcov, hu'v⟩ := exists_cover M.Ri M.refl_i M.trans_i u v hRiuv hvu
        refine Or.inr ?_
        rw [force_Ldis]
        refine Or.inl ⟨u', hcov, ?_⟩
        rw [force_alpha]
        exact Or.inl hu'v
    · exact Or.inl ((Mstar M φ₀).force_of_fallible hvF)
  · -- (⟸)
    intro hC
    rw [force_applyC_C0] at hC
    intro v hwv
    -- reach a stable world u above v
    obtain ⟨u, hvu_rm, hStab_u⟩ :=
      exists_max_cluster M.Rm M.refl_m M.trans_m v
    have hRiwu : M.Ri w u := M.trans_i hwv (M.sub_mi hvu_rm)
    have hau : (Mstar M φ₀).force u (alpha M φ₀ u) := by
      rw [force_alpha]; exact Or.inl (M.refl_i u)
    have hstep : (Mstar M φ₀).force u ψ ∨ (Mstar M φ₀).force u (Ldis M φ₀ u) :=
      hC u hStab_u u hRiwu hau
    have hfin : (Mstar M φ₀).force u ψ := by
      rcases hstep with hψ | hLdis
      · exact hψ
      · rw [force_Ldis] at hLdis
        rcases hLdis with ⟨u', hisucc, halpha⟩ | huF
        · rw [force_alpha] at halpha
          rcases halpha with hriu' | huF
          · exact absurd hriu' hisucc.2.1
          · exact (Mstar M φ₀).force_of_fallible huF
        · exact (Mstar M φ₀).force_of_fallible huF
    exact ⟨u, hvu_rm, hfin⟩

/-- **Congruence under uniform `◯`-replacement.**  Substituting `C0[·]` for every
`◯` (i.e. `subC (C0 M φ₀)`) preserves forcing in `M*` — structural induction with
Lemma 7 at each `◯`. -/
theorem force_subC_C0 : ∀ (ψ : PLLFormula) (w : M.W),
    (Mstar M φ₀).force w (subC (C0 M φ₀) ψ) ↔ (Mstar M φ₀).force w ψ := by
  intro ψ
  induction ψ with
  | prop a => intro w; exact Iff.rfl
  | falsePLL => intro w; exact Iff.rfl
  | and φ ψ ihφ ihψ => intro w; exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ => intro w; exact or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      exact forall_congr' fun v => imp_congr Iff.rfl (imp_congr (ihφ v) (ihψ v))
  | somehow φ ih =>
      intro w
      have h1 : (Mstar M φ₀).force w (subC (C0 M φ₀) (.somehow φ)) ↔
          (Mstar M φ₀).force w (.somehow (subC (C0 M φ₀) φ)) :=
        (lemma7 M φ₀ (subC (C0 M φ₀) φ) w).symm
      rw [h1]
      exact forall_congr' fun v =>
        imp_congr Iff.rfl (exists_congr fun u => and_congr Iff.rfl (ih u))

end Lemma7

/-! ## Section D — the completeness direction of Theorem 6 -/

/-- **Theorem 6, completeness direction.**  If every standard-constraint expansion
`φ^C` is IPL-provable, then `φ` is a PLL theorem.  (Contrapositive: a finite
countermodel `M ⊭ φ`, completed to `M*`, refutes the single constraint `C0`, and
`subC C0 φ` being `◯`-free this is an IPL refutation.) -/
theorem thm6_completeness {φ : PLLFormula}
    (h : ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ))) : Nonempty (LaxND [] φ) := by
  by_contra hnp
  rw [finite_model_property] at hnp
  push_neg at hnp
  obtain ⟨M, hMfin, w₀, hw₀⟩ := hnp
  haveI : Finite M.W := hMfin
  haveI : Fintype M.W := Fintype.ofFinite M.W
  -- `M*` agrees with `M` on `φ`, so `M* ⊭ φ`:
  have hcoin : (Mstar M φ).force w₀ φ ↔ M.force w₀ φ :=
    force_coincide M φ φ (fun w => nm_fresh M φ w) w₀
  have hMstar_nf : ¬ (Mstar M φ).force w₀ φ := fun hf => hw₀ (hcoin.mp hf)
  -- congruence: `M* ⊭ subC C0 φ`:
  have hsub : ¬ (Mstar M φ).force w₀ (subC (C0 M φ) φ) := fun hf =>
    hMstar_nf ((force_subC_C0 M φ φ w₀).mp hf)
  -- but the hypothesis makes `subC C0 φ` provable, hence valid in `M*` — contradiction:
  obtain ⟨p⟩ := h (C0 M φ)
  exact hsub (soundness_valid p (Mstar M φ) w₀)

/-- **Theorem 6** (full context-completeness).  `PLL ⊢ φ` iff every standard
constraint expansion `φ^C` is IPL-provable.  (`subC C φ` is `◯`-free when `C`'s
`K,L` are — `subC_isIPL` — so `Nonempty (LaxND [] (subC C φ))` is genuine IPL
provability via `conservativity`; the witness `C0` built in the completeness proof
has propositional `K,L`, so `CtxIsIPL (C0 M φ)` holds.) -/
theorem thm6 {φ : PLLFormula} :
    Nonempty (LaxND [] φ) ↔ ∀ C : StdCtx, Nonempty (LaxND [] (subC C φ)) :=
  ⟨fun h C => thm6_soundness C h, thm6_completeness⟩

end Ctx
end PLLND

#print axioms PLLND.Ctx.thm6

/-! ============================================================================
# Section E — Corollary 10: no finite set of standard constraints is complete

Fairtlough–Mendler, TYPES 2000, §6 (pp. 12–13): Lemmas 8, 9 and Corollary 10.

The *characteristic schemes* `χ_m` (distinct propositional variables `p₁,p₂,…`):
  χ₀       = ◯false
  χ_{m+1}  = ◯(◯p_{m+1} ⊃ (p_{m+1} ∨ χ_m))

* **Lemma 8**  every standard constraint `C` of depth `n` makes `χ_m^C` an IPL
  theorem for all `m ≥ n`.
* **Lemma 9**  for every `m` there is a constraint model refuting `χ_m`, so `χ_m`
  is not a PLL theorem.
* **Corollary 10**  no finite `𝔻 ⊆ 𝕊` is complete: `χ_m` (with `m = sup` of the
  depths in `𝔻`) is expanded to an IPL theorem by every `C ∈ 𝔻`, yet is not a PLL
  theorem.

Both lemmas are proved *semantically* through `valid_iff_provable`
(`(∀ C w, C.force w φ) ↔ Nonempty (LaxND [] φ)`): Lemma 9 exhibits an explicit
refuting model, Lemma 8 proves validity of `subC C χ_m` in every model.
============================================================================ -/

namespace PLLND
namespace Ctx

open PLLFormula

/-! ## The characteristic schemes `χ_m` -/

/-- Distinct propositional names `p₁, p₂, …` (an injective `ℕ ↪ String`). -/
noncomputable def pname : ℕ → String := fun i => Infinite.natEmbedding String i

theorem pname_inj : Function.Injective pname := by
  intro a b h
  exact (Infinite.natEmbedding String).injective h

/-- The propositional variable `p_i`. -/
noncomputable def pvar (i : ℕ) : PLLFormula := .prop (pname i)

/-- The characteristic schemes `χ_m` (Fairtlough–Mendler p. 12). -/
noncomputable def chi : ℕ → PLLFormula
  | 0     => .somehow .falsePLL
  | (m+1) => .somehow (.ifThen (.somehow (pvar (m+1))) (.or (pvar (m+1)) (chi m)))

/-! ## Lemma 9 — the refuting models `M_m`

Following the paper we use one model per `m`.  To make the *suffix isomorphism*
`M_{m+1}(2) ≅ M_m` painless we put every `M_m` on the carrier `ℕ` (only the
valuation depends on `m`); the isomorphism then becomes translation-by-2, and the
inductive step of `M_m ⊭ χ_m` is a shift-by-2 bisimulation. -/

/-- Modal accessibility of `M_k`: the diagonal together with the "odd ↦ successor"
edges `2j+1 ⊑ₘ 2j+2`.  (`a % 2 = 1` keeps everything in linear-arithmetic range,
so `omega` handles all the modal bookkeeping.) -/
def Rmrel (a b : ℕ) : Prop := a = b ∨ (a % 2 = 1 ∧ b = a + 1)

/-- Valuation of `M_k`: `p_i` holds at world `j` iff `2k+2 ≤ j + 2i`
(equivalently `j ≥ 2(k+1-i)`; written additively to stay on ℕ).  Paper:
`V(2r)=V(2r+1)={p_{k-r+1},…,p_k}`. -/
noncomputable def Vval (k : ℕ) : String → Set ℕ :=
  fun s => { j | ∀ i, pname i = s → 2 * k + 2 ≤ j + 2 * i }

/-- The linear constraint model `M_k`: carrier `ℕ`, `⊑ᵢ = ≤`, `⊑ₘ = Rmrel`,
no fallible worlds, valuation `Vval k`.  Marked `@[reducible]` so that the world
type `(Mmod k).W` is transparently `ℕ` for instance resolution and `omega`. -/
@[reducible] noncomputable def Mmod (k : ℕ) : ConstraintModel where
  W := ℕ
  Ri := (· ≤ ·)
  Rm := Rmrel
  F := ∅
  V := Vval k
  refl_i := fun w => le_refl w
  trans_i := by intro a b c h1 h2; exact le_trans h1 h2
  refl_m := fun _ => Or.inl rfl
  trans_m := by
    intro a b c hab hbc
    rcases hab with rfl | ⟨ha, rfl⟩
    · exact hbc
    · rcases hbc with rfl | ⟨hb, rfl⟩
      · exact Or.inr ⟨ha, rfl⟩
      · exfalso; omega
  sub_mi := by
    intro a b h
    rcases h with rfl | ⟨_, rfl⟩
    · exact le_refl a
    · exact Nat.le_succ a
  hered_F := by intro a b _ h; exact absurd h (Set.notMem_empty a)
  hered_V := by
    intro a b c hbc hb
    simp only [Vval, Set.mem_setOf_eq] at hb ⊢
    intro i hi; have := hb i hi; omega
  full_F := by intro a b h; exact absurd h (Set.notMem_empty b)

/-- Valuation characterisation: `p_i` is forced at `j` in `M_k` iff `2k+2 ≤ j+2i`. -/
theorem force_pvar (k i j : ℕ) :
    (Mmod k).force j (pvar i) ↔ 2 * k + 2 ≤ j + 2 * i := by
  show j ∈ Vval k (pname i) ↔ _
  simp only [Vval, Set.mem_setOf_eq]
  constructor
  · intro h; exact h i rfl
  · intro h i' hi'; obtain rfl := pname_inj hi'; exact h

/-- `0` has no proper modal successor: `0 ⊑ₘ u` forces `u = 0`. -/
theorem Rm_zero {u : ℕ} (h : Rmrel 0 u) : u = 0 := by
  rcases h with rfl | ⟨h, _⟩
  · rfl
  · exact absurd h (by decide)

/-- `1 ⊨ ◯p_{m+1}` in `M_{m+1}`: from every `v ≥ 1` a world forcing `p_{m+1}`
(i.e. a world `≥ 2`) is `⊑ₘ`-reachable. -/
theorem force_box_pvar (m : ℕ) :
    (Mmod (m+1)).force 1 (.somehow (pvar (m+1))) := by
  show ∀ v : ℕ, (1:ℕ) ≤ v → ∃ u, Rmrel v u ∧ (Mmod (m+1)).force u (pvar (m+1))
  intro v hv
  by_cases hv2 : 2 ≤ v
  · exact ⟨v, Or.inl rfl, (force_pvar (m+1) (m+1) v).mpr (by omega)⟩
  · have hv1 : v = 1 := by omega
    subst hv1
    exact ⟨2, Or.inr ⟨by decide, rfl⟩, (force_pvar (m+1) (m+1) 2).mpr (by omega)⟩

/-- **Suffix isomorphism as a shift-by-2 bisimulation.**  `M_{m+1}` at world `t+2`
forces exactly what `M_m` forces at world `t`.  (The suffix of `M_{m+1}` starting at
`2` is `M_m`.) -/
theorem bisim (m : ℕ) (φ : PLLFormula) :
    ∀ t : ℕ, (Mmod (m+1)).force (t+2) φ ↔ (Mmod m).force t φ := by
  induction φ with
  | prop a =>
      intro t
      show (t+2) ∈ Vval (m+1) a ↔ t ∈ Vval m a
      simp only [Vval, Set.mem_setOf_eq]
      constructor
      · intro h i hi; have := h i hi; omega
      · intro h i hi; have := h i hi; omega
  | falsePLL =>
      intro t
      show ((t+2) ∈ (∅ : Set ℕ)) ↔ (t ∈ (∅ : Set ℕ))
      simp
  | and φ ψ ihφ ihψ => intro t; exact and_congr (ihφ t) (ihψ t)
  | or φ ψ ihφ ihψ => intro t; exact or_congr (ihφ t) (ihψ t)
  | ifThen φ ψ ihφ ihψ =>
      intro t
      constructor
      · intro h
        replace h : ∀ v : ℕ, t + 2 ≤ v →
            (Mmod (m+1)).force v φ → (Mmod (m+1)).force v ψ := h
        show ∀ v : ℕ, t ≤ v → (Mmod m).force v φ → (Mmod m).force v ψ
        intro v hv hφ
        exact (ihψ v).mp (h (v+2) (by omega) ((ihφ v).mpr hφ))
      · intro h
        replace h : ∀ v : ℕ, t ≤ v →
            (Mmod m).force v φ → (Mmod m).force v ψ := h
        show ∀ v : ℕ, t + 2 ≤ v → (Mmod (m+1)).force v φ → (Mmod (m+1)).force v ψ
        intro v hv hφ
        obtain ⟨s, rfl⟩ : ∃ s, v = s + 2 := ⟨v - 2, by omega⟩
        exact (ihψ s).mpr (h s (by omega) ((ihφ s).mp hφ))
  | somehow φ ih =>
      intro t
      constructor
      · intro h
        replace h : ∀ v : ℕ, t + 2 ≤ v →
            ∃ u : ℕ, Rmrel v u ∧ (Mmod (m+1)).force u φ := h
        show ∀ v : ℕ, t ≤ v → ∃ u : ℕ, Rmrel v u ∧ (Mmod m).force u φ
        intro v hv
        obtain ⟨u, hRm, hu⟩ := h (v + 2) (by omega)
        have hu2 : 2 ≤ u := by rcases hRm with h1 | ⟨_, h1⟩ <;> omega
        obtain ⟨r, rfl⟩ : ∃ r, u = r + 2 := ⟨u - 2, by omega⟩
        refine ⟨r, ?_, (ih r).mp hu⟩
        rcases hRm with h1 | ⟨h1, h2⟩
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, by omega⟩
      · intro h
        replace h : ∀ v : ℕ, t ≤ v →
            ∃ u : ℕ, Rmrel v u ∧ (Mmod m).force u φ := h
        show ∀ v : ℕ, t + 2 ≤ v → ∃ u : ℕ, Rmrel v u ∧ (Mmod (m+1)).force u φ
        intro v hv
        obtain ⟨s, rfl⟩ : ∃ s, v = s + 2 := ⟨v - 2, by omega⟩
        obtain ⟨r, hRm, hr⟩ := h s (by omega)
        refine ⟨r + 2, ?_, (ih r).mpr hr⟩
        rcases hRm with rfl | ⟨h1, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨by omega, by omega⟩

/-- `M_m ⊭ χ_m` at world `0`, by induction on `m` (Fairtlough–Mendler p. 13). -/
theorem chi_not_forced : ∀ m, ¬ (Mmod m).force 0 (chi m) := by
  intro m
  induction m with
  | zero =>
      intro h
      obtain ⟨u, _, hu⟩ := h 0 (le_refl 0)
      exact absurd hu (Set.notMem_empty u)
  | succ m ih =>
      intro h
      obtain ⟨u, hRm0u, hψ⟩ := h 0 (le_refl (0 : ℕ))
      obtain rfl := Rm_zero hRm0u
      have h1 : (Mmod (m+1)).force 1 ((pvar (m+1)).or (chi m)) :=
        hψ 1 (Nat.zero_le 1) (force_box_pvar m)
      rcases h1 with hp | hchi
      · have := (force_pvar (m+1) (m+1) 1).mp hp
        omega
      · have h2 : (Mmod (m+1)).force 2 (chi m) :=
          (Mmod (m+1)).force_hered (show (Mmod (m+1)).Ri 1 2 from Nat.le_succ 1) hchi
        exact ih ((bisim m (chi m) 0).mp h2)

/-- **Lemma 9.**  `χ_m` is refuted by the model `M_m`, hence is not a PLL theorem. -/
theorem lemma9 (m : ℕ) : ¬ Nonempty (LaxND [] (chi m)) := by
  intro hp
  exact chi_not_forced m (valid_iff_provable.mpr hp (Mmod m) 0)

/-! ## Lemma 8 — every depth-`≤ m` constraint validates `χ_m`

Proved semantically: `subC C χ_m` is forced in **every** constraint model, so it is
a PLL (hence, being `◯`-free, an IPL) theorem by `valid_iff_provable`.  The paper's
"interval-drop" step becomes the substitution-congruence `force_subC_drop`: under a
world where `L` is hereditarily forced, the basic constraint `[K,L]` is vacuous, so
dropping it from `C` does not change what `subC C φ` forces. -/

/-- One-step unfolding of `subC C (χ_{m+1})`. -/
theorem subC_chi_succ (C : StdCtx) (m : ℕ) :
    subC C (chi (m+1)) =
      applyC C (.ifThen (applyC C (pvar (m+1)))
        (.or (pvar (m+1)) (subC C (chi m)))) := rfl

/-- **Substitution-drop congruence.**  If `L` is hereditarily forced from `u`, then
the constraint `[K,L]` is vacuous there, so `subC (s ++ (K,L) :: t) φ` and
`subC (s ++ t) φ` are forced at exactly the same worlds `≥ u`. -/
theorem force_subC_drop (D : ConstraintModel) (K L : PLLFormula) (s t : StdCtx)
    (u : D.W) (hL : ∀ x, D.Ri u x → D.force x L) :
    ∀ (φ : PLLFormula) (v : D.W), D.Ri u v →
      (D.force v (subC (s ++ (K, L) :: t) φ) ↔ D.force v (subC (s ++ t) φ)) := by
  intro φ
  induction φ with
  | prop a => intro v _; exact Iff.rfl
  | falsePLL => intro v _; exact Iff.rfl
  | and φ ψ ihφ ihψ => intro v hv; exact and_congr (ihφ v hv) (ihψ v hv)
  | or φ ψ ihφ ihψ => intro v hv; exact or_congr (ihφ v hv) (ihψ v hv)
  | ifThen φ ψ ihφ ihψ =>
      intro v hv
      constructor
      · intro h w hvw hφ
        exact (ihψ w (D.trans_i hv hvw)).mp (h w hvw ((ihφ w (D.trans_i hv hvw)).mpr hφ))
      · intro h w hvw hφ
        exact (ihψ w (D.trans_i hv hvw)).mpr (h w hvw ((ihφ w (D.trans_i hv hvw)).mp hφ))
  | somehow φ ih =>
      intro v hv
      show D.force v (applyC (s ++ (K, L) :: t) (subC (s ++ (K, L) :: t) φ)) ↔
           D.force v (applyC (s ++ t) (subC (s ++ t) φ))
      rw [force_applyC_iff, force_applyC_iff]
      have key : ∀ (p : PLLFormula × PLLFormula),
          (D.force v (basic p.1 p.2 (subC (s ++ (K, L) :: t) φ)) ↔
           D.force v (basic p.1 p.2 (subC (s ++ t) φ))) := by
        intro p
        constructor
        · intro hb x hvx hK
          rcases hb x hvx hK with hX | hL'
          · exact Or.inl ((ih x (D.trans_i hv hvx)).mp hX)
          · exact Or.inr hL'
        · intro hb x hvx hK
          rcases hb x hvx hK with hX | hL'
          · exact Or.inl ((ih x (D.trans_i hv hvx)).mpr hX)
          · exact Or.inr hL'
      have hKLtrue : D.force v (basic K L (subC (s ++ (K, L) :: t) φ)) := by
        intro x hvx _
        exact Or.inr (hL x (D.trans_i hv hvx))
      constructor
      · intro hall p hp
        have hpC : p ∈ s ++ (K, L) :: t := by
          rcases List.mem_append.mp hp with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
        exact (key p).mp (hall p hpC)
      · intro hall p hp
        rcases List.mem_append.mp hp with h | h
        · exact (key p).mpr (hall p (List.mem_append_left _ h))
        · rcases List.mem_cons.mp h with rfl | h
          · exact hKLtrue
          · exact (key p).mpr (hall p (List.mem_append_right _ h))

/-- **Lemma 8 (semantic form).**  Every standard constraint `C` of depth `≤ m`
makes `subC C χ_m` valid in every constraint model. -/
theorem lemma8_valid : ∀ (m : ℕ) (C : StdCtx), C.length ≤ m →
    ∀ (D : ConstraintModel) (w : D.W), D.force w (subC C (chi m)) := by
  intro m
  induction m with
  | zero =>
      intro C hC D w
      obtain rfl : C = [] := by
        cases C with
        | nil => rfl
        | cons a as => simp only [List.length_cons] at hC; omega
      exact fun v _ hv => hv
  | succ m ih =>
      intro C hC D w
      rw [subC_chi_succ, force_applyC_iff]
      intro p hp
      obtain ⟨K, L⟩ := p
      intro v hwv hK
      left
      intro u hvu hCp
      rw [force_applyC_iff] at hCp
      have hKu : D.force u K := D.force_hered hvu hK
      rcases (hCp (K, L) hp) u (D.refl_i u) hKu with hpm | hLu
      · exact Or.inl hpm
      · refine Or.inr ?_
        obtain ⟨s, t, rfl⟩ := List.append_of_mem hp
        have hlen : (s ++ t).length ≤ m := by
          simp only [List.length_append, List.length_cons] at hC ⊢
          omega
        have hC' : D.force u (subC (s ++ t) (chi m)) := ih (s ++ t) hlen D u
        have hLher : ∀ x, D.Ri u x → D.force x L := fun x hx => D.force_hered hx hLu
        exact (force_subC_drop D K L s t u hLher (chi m) u (D.refl_i u)).mpr hC'

/-- **Lemma 8.**  A standard constraint `C` of depth `n` makes `χ_m` (after
expansion `χ_m^C`) an IPL theorem, for every `m ≥ n`. -/
theorem lemma8 (C : StdCtx) (m : ℕ) (h : C.length ≤ m) :
    Nonempty (LaxND [] (subC C (chi m))) :=
  valid_iff_provable.mp (fun D w => lemma8_valid m C h D w)

/-- **Corollary 10.**  No finite set of standard constraints is complete for PLL:
for every finite `𝔻 ⊆ 𝕊` there is a formula `φ` — namely `χ_m` with `m` the maximum
depth in `𝔻` — that every `C ∈ 𝔻` expands to an IPL theorem `φ^C`, yet `φ` is not a
PLL theorem. -/
theorem corollary10 (𝔻 : Finset StdCtx) :
    ∃ φ : PLLFormula,
      (∀ C ∈ 𝔻, Nonempty (LaxND [] (subC C φ))) ∧ ¬ Nonempty (LaxND [] φ) := by
  refine ⟨chi (𝔻.sup List.length), ?_, lemma9 _⟩
  intro C hC
  exact lemma8 C (𝔻.sup List.length) (Finset.le_sup hC)

/-! ============================================================================
# Section F — Theorem 2: the Boolean algebra of standard constraints

Fairtlough–Mendler, TYPES 2000, §3 (pp. 5–7).  Constraints are taken *up to
equivalence*: `C ≡ D` iff `C[x] ⊣⊢_IPL D[x]` for all `x`, and `C ≤ D` iff
`C[x] ⊃ D[x]` is IPL-valid for all `x`.  We use the equivalent *semantic*
formulations (`Cequiv`, `Cle`); `Cle_iff_provable` certifies they coincide with
the paper's provability definitions.

Operations (Def 1, pp. 5–7):
* meet   `C ⊓ D`  = `Cmeet` = list append (componentwise conjunction of actions);
* join   `C ⊔ D`  = `Cjoin` = pairwise product `⨅_{i,j} [Kᵢ∧Kⱼ, Lᵢ∨Lⱼ]`;
* top    `⊤ = []`  (`⊤[x] ≡ true`), bottom `⊥ = [true,false]` (`⊥[x] ≡ x`). -/

/-- Meet `C ⊓ D`: componentwise conjunction of actions, i.e. list append. -/
def Cmeet (C D : StdCtx) : StdCtx := C ++ D

/-- Join `C ⊔ D` (Def 1): the pairwise product `⨅_{i,j} [K₁ᵢ∧K₂ⱼ, L₁ᵢ∨L₂ⱼ]`. -/
def Cjoin (C D : StdCtx) : StdCtx :=
  C.flatMap (fun p => D.map (fun q => (p.1.and q.1, p.2.or q.2)))

/-- Top `⊤` (`⊤[x] ≡ true`): the depth-0 constraint. -/
def Ctop : StdCtx := []

/-- Bottom `⊥ = [true,false]` (`⊥[x] ≡ x`): the identity modality. -/
def Cbot : StdCtx := [(truePLL, falsePLL)]

/-- `C ≤ D`: `C[x] ⊃ D[x]` holds at every world of every model, for all `x`. -/
def Cle (C D : StdCtx) : Prop :=
  ∀ (M : ConstraintModel) (w : M.W) (x : PLLFormula),
    M.force w (applyC C x) → M.force w (applyC D x)

/-- `C ≡ D`: `C[x] ⊣⊢ D[x]` at every world of every model, for all `x`. -/
def Cequiv (C D : StdCtx) : Prop :=
  ∀ (M : ConstraintModel) (w : M.W) (x : PLLFormula),
    M.force w (applyC C x) ↔ M.force w (applyC D x)

/-! ## `Cle`/`Cequiv` order structure, and faithfulness to provability -/

theorem Cequiv.rfl' (C : StdCtx) : Cequiv C C := fun _ _ _ => Iff.rfl
theorem Cequiv.symm {C D} (h : Cequiv C D) : Cequiv D C := fun M w x => (h M w x).symm
theorem Cequiv.trans {C D E} (h1 : Cequiv C D) (h2 : Cequiv D E) : Cequiv C E :=
  fun M w x => (h1 M w x).trans (h2 M w x)
theorem Cle.rfl' (C : StdCtx) : Cle C C := fun _ _ _ h => h
theorem Cle.trans {C D E} (h1 : Cle C D) (h2 : Cle D E) : Cle C E :=
  fun M w x h => h2 M w x (h1 M w x h)
theorem Cequiv_iff_le {C D} : Cequiv C D ↔ Cle C D ∧ Cle D C := by
  constructor
  · intro h; exact ⟨fun M w x => (h M w x).mp, fun M w x => (h M w x).mpr⟩
  · rintro ⟨h1, h2⟩ M w x; exact ⟨h1 M w x, h2 M w x⟩

/-- **Faithfulness of `Cle`.**  The semantic order coincides with the paper's:
`C ≤ D` iff `C[x] ⊃ D[x]` is IPL-provable for every `x`. -/
theorem Cle_iff_provable (C D : StdCtx) :
    Cle C D ↔ ∀ x, Nonempty (LaxND [] ((applyC C x).ifThen (applyC D x))) := by
  constructor
  · intro h x
    rw [← valid_iff_provable]
    intro M w v hwv hCx
    exact h M v x hCx
  · intro h M w x hCx
    obtain ⟨p⟩ := h x
    exact (valid_iff_provable.mpr ⟨p⟩ M w) w (M.refl_i w) hCx

/-! ## Action-forcing helpers for the operations -/

theorem force_basic (M : ConstraintModel) (K L x : PLLFormula) (w : M.W) :
    M.force w (basic K L x) ↔
      ∀ v, M.Ri w v → M.force v K → (M.force v x ∨ M.force v L) :=
  Iff.rfl

theorem force_Cmeet (M : ConstraintModel) (C D : StdCtx) (x : PLLFormula) (w : M.W) :
    M.force w (applyC (Cmeet C D) x) ↔
      M.force w (applyC C x) ∧ M.force w (applyC D x) := by
  rw [Cmeet, force_applyC_iff, force_applyC_iff, force_applyC_iff]
  exact List.forall_mem_append

theorem force_Cjoin (M : ConstraintModel) (C D : StdCtx) (x : PLLFormula) (w : M.W) :
    M.force w (applyC (Cjoin C D) x) ↔
      ∀ p ∈ C, ∀ q ∈ D, M.force w (basic (p.1.and q.1) (p.2.or q.2) x) := by
  rw [Cjoin, force_applyC_iff]
  constructor
  · intro h p hp q hq
    exact h _ (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩)
  · intro h r hr
    obtain ⟨p, hp, hr2⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr2
    exact h p hp q hq

/-- The monad `unit`, semantically: `x` forces `C[x]` (so `x ⊃ C[x]` is valid). -/
theorem unit_sem (M : ConstraintModel) (C : StdCtx) (x : PLLFormula) (w : M.W)
    (h : M.force w x) : M.force w (applyC C x) := by
  rw [force_applyC_iff]; intro p _
  exact fun v hwv _ => Or.inl (M.force_hered hwv h)

theorem force_Ctop (M : ConstraintModel) (x : PLLFormula) (w : M.W) :
    M.force w (applyC Ctop x) := fun v _ hv => hv

theorem force_Cbot (M : ConstraintModel) (x : PLLFormula) (w : M.W) :
    M.force w (applyC Cbot x) ↔ M.force w x := by
  rw [Cbot, force_applyC_iff]
  constructor
  · intro h
    rcases (h (truePLL, falsePLL) (List.mem_cons_self ..)) w (M.refl_i w)
      (fun v _ hv => hv) with hx | hf
    · exact hx
    · exact M.force_of_fallible hf
  · intro hx p _
    exact fun v hwv _ => Or.inl (M.force_hered hwv hx)

/-! ## Meet `⊓` is a commutative idempotent monoid with bounds and is the meet -/

theorem meet_comm (C D : StdCtx) : Cequiv (Cmeet C D) (Cmeet D C) := by
  intro M w x; rw [force_Cmeet, force_Cmeet]; exact and_comm

theorem meet_assoc (C D E : StdCtx) :
    Cequiv (Cmeet (Cmeet C D) E) (Cmeet C (Cmeet D E)) := by
  intro M w x; simp only [force_Cmeet]; rw [and_assoc]

theorem meet_idem (C : StdCtx) : Cequiv (Cmeet C C) C := by
  intro M w x; rw [force_Cmeet]; exact and_self_iff

theorem meet_top (C : StdCtx) : Cequiv (Cmeet C Ctop) C := by
  intro M w x; simp only [Cmeet, Ctop, List.append_nil]

theorem meet_bot (C : StdCtx) : Cequiv (Cmeet C Cbot) Cbot := by
  intro M w x
  simp only [force_Cmeet, force_Cbot]
  exact ⟨fun h => h.2, fun hx => ⟨unit_sem M C x w hx, hx⟩⟩

theorem meet_le_left (C D : StdCtx) : Cle (Cmeet C D) C :=
  fun M w x h => ((force_Cmeet M C D x w).mp h).1

theorem meet_le_right (C D : StdCtx) : Cle (Cmeet C D) D :=
  fun M w x h => ((force_Cmeet M C D x w).mp h).2

theorem le_meet {C D E : StdCtx} (h1 : Cle E C) (h2 : Cle E D) : Cle E (Cmeet C D) :=
  fun M w x h => (force_Cmeet M C D x w).mpr ⟨h1 M w x h, h2 M w x h⟩

theorem le_iff_meet {C D : StdCtx} : Cle C D ↔ Cequiv (Cmeet C D) C := by
  constructor
  · intro h M w x
    rw [force_Cmeet]
    exact ⟨fun hh => hh.1, fun hh => ⟨hh, h M w x hh⟩⟩
  · intro h M w x hC
    exact ((force_Cmeet M C D x w).mp ((h M w x).mpr hC)).2

/-! ## Join `⊔` — upper bounds, commutativity, and the least-upper-bound direction -/

theorem le_join_left (C D : StdCtx) : Cle C (Cjoin C D) := by
  intro M w x h
  rw [force_Cjoin]; intro p hp q _ v hwv hpq
  rcases ((force_applyC_iff M C x w).mp h p hp) v hwv hpq.1 with hx | hLp
  · exact Or.inl hx
  · exact Or.inr (Or.inl hLp)

theorem le_join_right (C D : StdCtx) : Cle D (Cjoin C D) := by
  intro M w x h
  rw [force_Cjoin]; intro p _ q hq v hwv hpq
  rcases ((force_applyC_iff M D x w).mp h q hq) v hwv hpq.2 with hx | hLq
  · exact Or.inl hx
  · exact Or.inr (Or.inr hLq)

theorem join_comm (C D : StdCtx) : Cequiv (Cjoin C D) (Cjoin D C) := by
  have key : ∀ (C D : StdCtx), Cle (Cjoin C D) (Cjoin D C) := by
    intro C D M w x h
    rw [force_Cjoin] at h; rw [force_Cjoin]
    intro q hq p hp v hwv hqp
    rcases (h p hp q hq) v hwv ⟨hqp.2, hqp.1⟩ with hx | hL
    · exact Or.inl hx
    · exact Or.inr (Or.comm.mp hL)
  intro M w x; exact ⟨key C D M w x, key D C M w x⟩

/-- **`C ≤ D` iff `C ⊔ D ≡ D`** — the join adjunction, whose hard direction
instantiates `C ≤ D` at the proposition `x ∨ q.2`. -/
theorem join_eq_right_of_le {C D : StdCtx} (h : Cle C D) : Cequiv (Cjoin C D) D := by
  intro M w x
  constructor
  · intro hJ
    rw [force_applyC_iff]; intro q hq v hwv hq1
    have hCy : M.force v (applyC C (x.or q.2)) := by
      rw [force_applyC_iff]; intro p hp v' hvv' hp1
      rw [force_Cjoin] at hJ
      have hq1' : M.force v' q.1 := M.force_hered hvv' hq1
      rcases (hJ p hp q hq) v' (M.trans_i hwv hvv') ⟨hp1, hq1'⟩ with hx | hL
      · exact Or.inl (Or.inl hx)
      · rcases hL with hp2 | hq2
        · exact Or.inr hp2
        · exact Or.inl (Or.inr hq2)
    rcases ((force_applyC_iff M D (x.or q.2) v).mp (h M v (x.or q.2) hCy) q hq)
      v (M.refl_i v) hq1 with hxy | hq2
    · exact hxy
    · exact Or.inr hq2
  · intro hD; exact le_join_right C D M w x hD

theorem le_iff_join {C D : StdCtx} : Cle C D ↔ Cequiv (Cjoin C D) D := by
  constructor
  · exact join_eq_right_of_le
  · intro h; exact Cle.trans (le_join_left C D) (Cequiv_iff_le.mp h).1

theorem join_idem (C : StdCtx) : Cequiv (Cjoin C C) C :=
  join_eq_right_of_le (Cle.rfl' C)

theorem le_top (C : StdCtx) : Cle C Ctop := fun M w x _ => force_Ctop M x w

theorem bot_le (C : StdCtx) : Cle Cbot C := by
  intro M w x h
  exact unit_sem M C x w ((force_Cbot M x w).mp h)

theorem join_top (C : StdCtx) : Cequiv (Cjoin C Ctop) Ctop :=
  join_eq_right_of_le (le_top C)

theorem join_bot (C : StdCtx) : Cequiv (Cjoin C Cbot) C :=
  Cequiv.trans (join_comm C Cbot) (join_eq_right_of_le (bot_le C))

/-- Triple characterisation of a left-nested join. -/
theorem force_Cjoin_left (M : ConstraintModel) (C D E : StdCtx) (x : PLLFormula)
    (w : M.W) :
    M.force w (applyC (Cjoin (Cjoin C D) E) x) ↔
      ∀ p ∈ C, ∀ q ∈ D, ∀ e ∈ E,
        M.force w (basic ((p.1.and q.1).and e.1) ((p.2.or q.2).or e.2) x) := by
  rw [force_Cjoin]
  constructor
  · intro h p hp q hq e he
    exact h (p.1.and q.1, p.2.or q.2)
      (List.mem_flatMap.mpr ⟨p, hp, List.mem_map.mpr ⟨q, hq, rfl⟩⟩) e he
  · intro h r hr e he
    obtain ⟨p, hp, hr2⟩ := List.mem_flatMap.mp hr
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr2
    exact h p hp q hq e he

/-- Triple characterisation of a right-nested join. -/
theorem force_Cjoin_right (M : ConstraintModel) (C D E : StdCtx) (x : PLLFormula)
    (w : M.W) :
    M.force w (applyC (Cjoin C (Cjoin D E)) x) ↔
      ∀ p ∈ C, ∀ q ∈ D, ∀ e ∈ E,
        M.force w (basic (p.1.and (q.1.and e.1)) (p.2.or (q.2.or e.2)) x) := by
  rw [force_Cjoin]
  constructor
  · intro h p hp q hq e he
    exact h p hp (q.1.and e.1, q.2.or e.2)
      (List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨e, he, rfl⟩⟩)
  · intro h p hp s hs
    obtain ⟨q, hq, hs2⟩ := List.mem_flatMap.mp hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs2
    exact h p hp q hq e he

theorem join_assoc (C D E : StdCtx) :
    Cequiv (Cjoin (Cjoin C D) E) (Cjoin C (Cjoin D E)) := by
  intro M w x
  rw [force_Cjoin_left, force_Cjoin_right]
  constructor
  · intro h p hp q hq e he v hwv hK
    rcases h p hp q hq e he v hwv ⟨⟨hK.1, hK.2.1⟩, hK.2.2⟩ with hx | hL
    · exact Or.inl hx
    · rcases hL with hpq | he2
      · rcases hpq with hp2 | hq2
        · exact Or.inr (Or.inl hp2)
        · exact Or.inr (Or.inr (Or.inl hq2))
      · exact Or.inr (Or.inr (Or.inr he2))
  · intro h p hp q hq e he v hwv hK
    rcases h p hp q hq e he v hwv ⟨hK.1.1, hK.1.2, hK.2⟩ with hx | hL
    · exact Or.inl hx
    · rcases hL with hp2 | hqe
      · exact Or.inr (Or.inl (Or.inl hp2))
      · rcases hqe with hq2 | he2
        · exact Or.inr (Or.inl (Or.inr hq2))
        · exact Or.inr (Or.inr he2)

/-! ## Absorption and distributivity — `𝕊` is a bounded distributive lattice -/

theorem absorb_meet_join (C D : StdCtx) : Cequiv (Cmeet C (Cjoin C D)) C := by
  intro M w x
  rw [force_Cmeet]
  exact ⟨fun h => h.1, fun h => ⟨h, le_join_left C D M w x h⟩⟩

theorem absorb_join_meet (C D : StdCtx) : Cequiv (Cjoin C (Cmeet C D)) C :=
  Cequiv.trans (join_comm C (Cmeet C D)) (join_eq_right_of_le (meet_le_left C D))

/-- **Dual distributivity** `C ⊔ (D ⊓ E) ≡ (C ⊔ D) ⊓ (C ⊔ E)` — "immediate from
Definition 1": `∀ q ∈ D ++ E` splits into `∀ q ∈ D` and `∀ q ∈ E`. -/
theorem join_meet_distrib (C D E : StdCtx) :
    Cequiv (Cjoin C (Cmeet D E)) (Cmeet (Cjoin C D) (Cjoin C E)) := by
  intro M w x
  rw [force_Cmeet, force_Cjoin, force_Cjoin, force_Cjoin, Cmeet]
  constructor
  · intro h
    exact ⟨fun p hp q hq => h p hp q (List.mem_append_left _ hq),
           fun p hp q hq => h p hp q (List.mem_append_right _ hq)⟩
  · rintro ⟨h1, h2⟩ p hp q hq
    rcases List.mem_append.mp hq with hqD | hqE
    · exact h1 p hp q hqD
    · exact h2 p hp q hqE

/-! ## Complements of the generators (atomic constraints)

The generators of `𝕊` (p. 6) are the disjunctive atoms `L ↦ [true, L]` and their
implicational complements `[L, false]`.  We verify these are genuine Boolean
complements: `[true,L] ⊓ [L,false] ≡ ⊥` and `[true,L] ⊔ [L,false] ≡ ⊤`.  (The
general complement for *arbitrary* `C` is `Cbar` in Section F.2 below — the
powerset-free De Morgan join, not the paper's `2^|I|`-fold meet normal form.) -/

/-- Forcing of a single basic constraint `[K,L]`. -/
theorem force_single (M : ConstraintModel) (K L x : PLLFormula) (w : M.W) :
    M.force w (applyC [(K, L)] x) ↔ M.force w (basic K L x) := by
  rw [force_applyC_iff]
  constructor
  · intro h; exact h (K, L) (List.mem_cons_self ..)
  · intro h p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h
    · cases hp

/-- Disjunctive atom `L = [true, L]` (`L[x] ≡ x ∨ L`). -/
def Catom (L : PLLFormula) : StdCtx := [(truePLL, L)]
/-- Its implicational complement `L̄ = [L, false]` (`L̄[x] ≡ L ⊃ x`). -/
def CatomBar (L : PLLFormula) : StdCtx := [(L, falsePLL)]

/-- Generators are complemented, part 1: `L ⊓ L̄ ≡ ⊥`. -/
theorem atom_meet_bar (L : PLLFormula) :
    Cequiv (Cmeet (Catom L) (CatomBar L)) Cbot := by
  intro M w x
  rw [force_Cmeet, force_Cbot, Catom, CatomBar, force_single, force_single]
  constructor
  · rintro ⟨h1, h2⟩
    rcases h1 w (M.refl_i w) (fun v _ hv => hv) with hx | hL
    · exact hx
    · rcases h2 w (M.refl_i w) hL with hx | hf
      · exact hx
      · exact M.force_of_fallible hf
  · intro hx
    exact ⟨fun v hwv _ => Or.inl (M.force_hered hwv hx),
           fun v hwv _ => Or.inl (M.force_hered hwv hx)⟩

/-- Generators are complemented, part 2: `L ⊔ L̄ ≡ ⊤`. -/
theorem atom_join_bar (L : PLLFormula) :
    Cequiv (Cjoin (Catom L) (CatomBar L)) Ctop := by
  intro M w x
  rw [force_Cjoin, Catom, CatomBar]
  constructor
  · intro _; exact force_Ctop M x w
  · intro _ p hp q hq v hwv hK
    rcases List.mem_cons.mp hp with rfl | hp
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr (Or.inl hK.2)
      · cases hq
    · cases hp

/-! ## Theorem 2 — summary

The laws below establish that `𝕊`, ordered by `Cle` (mod `Cequiv`), is a **bounded
distributive lattice** with meet `⊓`, join `⊔`, bounds `⊥ ≤ · ≤ ⊤`, whose
generators are complemented.  Full Boolean complementation for arbitrary `C` is
completed in Section F.2 (`thm2_boolean_algebra`, `compl_inf`, `compl_sup`). -/
theorem thm2_bounded_distributive_lattice :
    (∀ C D, Cequiv (Cmeet C D) (Cmeet D C)) ∧
    (∀ C D E, Cequiv (Cmeet (Cmeet C D) E) (Cmeet C (Cmeet D E))) ∧
    (∀ C, Cequiv (Cmeet C C) C) ∧
    (∀ C D, Cequiv (Cjoin C D) (Cjoin D C)) ∧
    (∀ C D E, Cequiv (Cjoin (Cjoin C D) E) (Cjoin C (Cjoin D E))) ∧
    (∀ C, Cequiv (Cjoin C C) C) ∧
    (∀ C D, Cequiv (Cmeet C (Cjoin C D)) C) ∧
    (∀ C D, Cequiv (Cjoin C (Cmeet C D)) C) ∧
    (∀ C D E, Cequiv (Cjoin C (Cmeet D E)) (Cmeet (Cjoin C D) (Cjoin C E))) ∧
    (∀ C, Cequiv (Cmeet C Ctop) C) ∧
    (∀ C, Cequiv (Cjoin C Cbot) C) ∧
    (∀ C, Cequiv (Cmeet C Cbot) Cbot) ∧
    (∀ C, Cequiv (Cjoin C Ctop) Ctop) ∧
    (∀ L, Cequiv (Cmeet (Catom L) (CatomBar L)) Cbot) ∧
    (∀ L, Cequiv (Cjoin (Catom L) (CatomBar L)) Ctop) :=
  ⟨meet_comm, meet_assoc, meet_idem, join_comm, join_assoc, join_idem,
   absorb_meet_join, absorb_join_meet, join_meet_distrib, meet_top, join_bot,
   meet_bot, join_top, atom_meet_bar, atom_join_bar⟩

/-! ============================================================================
# Section F.2 — Theorem 2 completed: `𝕊` is a (finitary) Boolean algebra

Fairtlough–Mendler, TYPES 2000, §3 (pp. 6–7).  We upgrade the bounded distributive
lattice `thm2_bounded_distributive_lattice` to a full **Boolean algebra** by exhibiting,
for every standard constraint `C`, a complement `C̄ = Cbar C ∈ 𝕊` with

  `C ⊓ C̄ ≡ ⊥`  (`compl_inf`)   and   `C ⊔ C̄ ≡ ⊤`  (`compl_sup`).

The paper's explicit complement `C̄ = ⨅_{A⊆I}[⋀_{a∈A}Lₐ, ⋁_{b∈I∖A}Kᵦ]` is the `2^|I|`
*normal form*; we avoid the powerset.  By Definition 1 a basic `[K,L] = [K,⊥] ⊔ [⊤,L]`,
so by De Morgan `[K,L]‾ = [⊤,K] ⊓ [L,⊥]` (a 2-basic constraint), and the complement of a
meet is the join of complements:  `Cbar (⨅ᵢ[Kᵢ,Lᵢ]) := ⨆ᵢ ([⊤,Kᵢ] ⊓ [Lᵢ,⊥])`
(a `foldr ⊔ ⊥`).  This stays inside `𝕊` (a join of standard constraints is standard) and
equals the powerset form up to `≈`, but never normalises.  `𝕊` is only *finitary* (finite
meets/joins), so it is an **incomplete** Boolean algebra — the intended result. -/

/-! ## Congruence of `⊔` and the least-upper-bound property

The whole complement induction rewrites under `⊔`, so we first record that `⊔` respects
`≈`.  The crux is left-monotonicity `A ≤ A' ⟹ A⊔B ≤ A'⊔B`, proved by the same
proposition-enlargement trick (`x ↦ x ∨ q.2`) as `join_eq_right_of_le`; congruence and the
LUB property (`join_lub`) then follow algebraically. -/

/-- Meet respects `≈` (immediate, since `(C⊓D)[x] ⊣⊢ C[x] ∧ D[x]`). -/
theorem meet_congr {A A' B B' : StdCtx} (hA : Cequiv A A') (hB : Cequiv B B') :
    Cequiv (Cmeet A B) (Cmeet A' B') := by
  intro M w x
  rw [force_Cmeet, force_Cmeet]
  exact and_congr (hA M w x) (hB M w x)

/-- **Left-monotonicity of `⊔`.**  `A ≤ A'` gives `A ⊔ B ≤ A' ⊔ B`.  Proof: to certify the
`(p', q)`-conjunct of `(A'⊔B)[x]` at `v`, build `A[x ∨ q.2]` at `v` from the join
hypothesis, transport it along `A ≤ A'`, and read off the `p'`-conjunct. -/
theorem join_mono_left {A A' B : StdCtx} (h : Cle A A') :
    Cle (Cjoin A B) (Cjoin A' B) := by
  intro M w x hJ
  have hJ' := (force_Cjoin M A B x w).mp hJ
  rw [force_Cjoin]
  intro p' hp' q hq v hwv hpq
  have hAy : M.force v (applyC A (x.or q.2)) := by
    rw [force_applyC_iff]
    intro p hp v' hvv' hp1
    have hq1' : M.force v' q.1 := M.force_hered hvv' hpq.2
    rcases hJ' p hp q hq v' (M.trans_i hwv hvv') ⟨hp1, hq1'⟩ with hx | hL
    · exact Or.inl (Or.inl hx)
    · rcases hL with hp2 | hq2
      · exact Or.inr hp2
      · exact Or.inl (Or.inr hq2)
  have hA'y : M.force v (applyC A' (x.or q.2)) := h M v (x.or q.2) hAy
  rcases (force_applyC_iff M A' (x.or q.2) v).mp hA'y p' hp' v (M.refl_i v) hpq.1
    with hxy | hp'2
  · rcases hxy with hx | hq2
    · exact Or.inl hx
    · exact Or.inr (Or.inr hq2)
  · exact Or.inr (Or.inl hp'2)

/-- Right-monotonicity of `⊔`, by commutativity. -/
theorem join_mono_right {A B B' : StdCtx} (h : Cle B B') :
    Cle (Cjoin A B) (Cjoin A B') :=
  Cle.trans (Cequiv_iff_le.mp (join_comm A B)).1
    (Cle.trans (join_mono_left h) (Cequiv_iff_le.mp (join_comm B' A)).1)

/-- `⊔` is monotone in both arguments. -/
theorem join_mono {A A' B B' : StdCtx} (h1 : Cle A A') (h2 : Cle B B') :
    Cle (Cjoin A B) (Cjoin A' B') :=
  Cle.trans (join_mono_left h1) (join_mono_right h2)

/-- **`⊔` respects `≈`** — the congruence the complement induction rewrites with. -/
theorem join_congr {A A' B B' : StdCtx} (hA : Cequiv A A') (hB : Cequiv B B') :
    Cequiv (Cjoin A B) (Cjoin A' B') :=
  Cequiv_iff_le.mpr
    ⟨join_mono (Cequiv_iff_le.mp hA).1 (Cequiv_iff_le.mp hB).1,
     join_mono (Cequiv_iff_le.mp hA).2 (Cequiv_iff_le.mp hB).2⟩

/-- **Least-upper-bound property of `⊔`.**  `C ≤ E`, `D ≤ E` ⟹ `C ⊔ D ≤ E`. -/
theorem join_lub {C D E : StdCtx} (h1 : Cle C E) (h2 : Cle D E) :
    Cle (Cjoin C D) E :=
  Cle.trans (join_mono h1 h2) (Cequiv_iff_le.mp (join_idem E)).1

/-- **Meet distributes over join** `A ⊓ (B ⊔ C) ≡ (A⊓B) ⊔ (A⊓C)` — the second
distributive law (the dual `join_meet_distrib` is already proved).  Direct from
Definition 1: every conjunct of the right-hand join is a monotone weakening of a conjunct
supplied by `A[x]` (when its index lies in `A`) or by `(B⊔C)[x]` (indices in `B×C`). -/
theorem meet_join_distrib (A B C : StdCtx) :
    Cequiv (Cmeet A (Cjoin B C)) (Cjoin (Cmeet A B) (Cmeet A C)) := by
  intro M w x
  rw [force_Cmeet, force_applyC_iff, force_Cjoin, force_Cjoin]
  constructor
  · rintro ⟨hA, hBC⟩ p hp q hq v hwv hpq
    rcases List.mem_append.mp hp with hpA | hpB
    · rcases (hA p hpA) v hwv hpq.1 with hx | hp2
      · exact Or.inl hx
      · exact Or.inr (Or.inl hp2)
    · rcases List.mem_append.mp hq with hqA | hqC
      · rcases (hA q hqA) v hwv hpq.2 with hx | hq2
        · exact Or.inl hx
        · exact Or.inr (Or.inr hq2)
      · exact (hBC p hpB q hqC) v hwv hpq
  · intro h
    refine ⟨fun a ha v hwv ha1 => ?_, fun b hb c hc v hwv hbc => ?_⟩
    · rcases (h a (List.mem_append_left _ ha) a (List.mem_append_left _ ha)) v hwv
        ⟨ha1, ha1⟩ with hx | ha2
      · exact Or.inl hx
      · exact Or.inr (ha2.elim id id)
    · exact (h b (List.mem_append_right _ hb) c (List.mem_append_right _ hc)) v hwv hbc

/-! ## The complement `C̄` and its two Boolean laws -/

/-- Complement of a single basic constraint: `[K,L]‾ = [⊤,K] ⊓ [L,⊥]`, the 2-basic
standard constraint `[(⊤,K),(L,⊥)]` (De Morgan applied to `[K,L] = [K,⊥] ⊔ [⊤,L]`). -/
def basicBar (p : PLLFormula × PLLFormula) : StdCtx :=
  [(truePLL, p.1), (p.2, falsePLL)]

/-- The complement `C̄` of a standard constraint `C = ⨅ᵢ [Kᵢ,Lᵢ]`: the finite join
`⨆ᵢ [Kᵢ,Lᵢ]‾` (`foldr ⊔ ⊥`).  A join of standard constraints, hence standard. -/
def Cbar : StdCtx → StdCtx
  | []        => Cbot
  | p :: rest => Cjoin (basicBar p) (Cbar rest)

/-- **Single-basic complement, meet law:** `[K,L] ⊓ [K,L]‾ ≡ ⊥`.  Semantically, the three
conjuncts `K⊃(x∨L)`, `⊤⊃(x∨K)`, `L⊃(x∨⊥)` force `x` outright (chase `x∨K`, then `x∨L`,
then `x∨⊥`), and conversely `x` forces each. -/
theorem single_meet_bar (p : PLLFormula × PLLFormula) :
    Cequiv (Cmeet [p] (basicBar p)) Cbot := by
  obtain ⟨K, L⟩ := p
  intro M w x
  rw [force_Cbot, force_applyC_iff]
  constructor
  · intro h
    have hKL := h (K, L) (by simp [Cmeet, basicBar])
    have hK  := h (truePLL, K) (by simp [Cmeet, basicBar])
    have hL  := h (L, falsePLL) (by simp [Cmeet, basicBar])
    rcases hK w (M.refl_i w) (fun v _ hv => hv) with hx | hKw
    · exact hx
    · rcases hKL w (M.refl_i w) hKw with hx | hLw
      · exact hx
      · rcases hL w (M.refl_i w) hLw with hx | hf
        · exact hx
        · exact M.force_of_fallible hf
  · intro hx q _
    exact fun v hwv _ => Or.inl (M.force_hered hwv hx)

/-- **Single-basic complement, join law:** `[K,L] ⊔ [K,L]‾ ≡ ⊤`.  Every pairwise conjunct
`(K∧⊤)⊃(x∨L∨K)` and `(K∧L)⊃(x∨L∨⊥)` is a tautology (the antecedent supplies `K`, resp.
`L`, already among the disjuncts), so the join acts as `⊤`. -/
theorem single_join_bar (p : PLLFormula × PLLFormula) :
    Cequiv (Cjoin [p] (basicBar p)) Ctop := by
  obtain ⟨K, L⟩ := p
  intro M w x
  rw [force_Cjoin]
  constructor
  · intro _; exact force_Ctop M x w
  · intro _ pp hpp q hq v hwv hpq
    obtain rfl := List.mem_singleton.mp hpp
    rcases List.mem_cons.mp hq with rfl | hq2
    · exact Or.inr (Or.inr hpq.1)
    · rcases List.mem_cons.mp hq2 with rfl | hq3
      · exact Or.inr (Or.inl hpq.2)
      · cases hq3

/-- `C ⊓ C̄ ≤ ⊥` by induction on `C`.  For `C = [p] ⊓ R` with `C̄ = p̄ ⊔ R̄`, distribute the
meet over the join and bound each summand: `([p]⊓R)⊓p̄ ≤ [p]⊓p̄ ≡ ⊥` (single-basic law) and
`([p]⊓R)⊓R̄ ≤ R⊓R̄ ≡ ⊥` (induction hypothesis). -/
theorem compl_inf_le (C : StdCtx) : Cle (Cmeet C (Cbar C)) Cbot := by
  induction C with
  | nil => exact Cle.rfl' Cbot
  | cons p rest ih =>
      show Cle (Cmeet (Cmeet [p] rest) (Cjoin (basicBar p) (Cbar rest))) Cbot
      have hX : Cle (Cmeet (Cmeet [p] rest) (basicBar p)) Cbot :=
        Cle.trans
          (le_meet (Cle.trans (meet_le_left _ _) (meet_le_left _ _)) (meet_le_right _ _))
          (Cequiv_iff_le.mp (single_meet_bar p)).1
      have hY : Cle (Cmeet (Cmeet [p] rest) (Cbar rest)) Cbot :=
        Cle.trans
          (le_meet (Cle.trans (meet_le_left _ _) (meet_le_right _ _)) (meet_le_right _ _))
          ih
      exact Cle.trans
        (Cequiv_iff_le.mp (meet_join_distrib (Cmeet [p] rest) (basicBar p) (Cbar rest))).1
        (join_lub hX hY)

/-- **Complement law (meet):** `C ⊓ C̄ ≡ ⊥`.  With `⊥ ≤ C ⊓ C̄` always (`bot_le`). -/
theorem compl_inf (C : StdCtx) : Cequiv (Cmeet C (Cbar C)) Cbot :=
  Cequiv_iff_le.mpr ⟨compl_inf_le C, bot_le _⟩

/-- `⊤ ≤ C ⊔ C̄` by induction on `C`.  For `C = [p] ⊓ R` with `C̄ = p̄ ⊔ R̄`, commute and
distribute the join over the meet: `⊤ ≡ [p]⊔p̄ ≤ (p̄⊔R̄)⊔[p]` (single-basic law) and
`⊤ ≡ R⊔R̄ ≤ (p̄⊔R̄)⊔R` (induction hypothesis) bound the two meet factors. -/
theorem compl_sup_ge (C : StdCtx) : Cle Ctop (Cjoin C (Cbar C)) := by
  induction C with
  | nil => exact Cle.rfl' Ctop
  | cons p rest ih =>
      show Cle Ctop (Cjoin (Cmeet [p] rest) (Cjoin (basicBar p) (Cbar rest)))
      have hP : Cle Ctop (Cjoin (Cjoin (basicBar p) (Cbar rest)) [p]) :=
        Cle.trans (Cequiv_iff_le.mp (single_join_bar p)).2
          (join_lub (le_join_right _ _)
            (Cle.trans (le_join_left (basicBar p) (Cbar rest))
              (le_join_left (Cjoin (basicBar p) (Cbar rest)) [p])))
      have hR : Cle Ctop (Cjoin (Cjoin (basicBar p) (Cbar rest)) rest) :=
        Cle.trans ih
          (join_lub (le_join_right _ _)
            (Cle.trans (le_join_right (basicBar p) (Cbar rest))
              (le_join_left (Cjoin (basicBar p) (Cbar rest)) rest)))
      have equiv : Cequiv (Cjoin (Cmeet [p] rest) (Cjoin (basicBar p) (Cbar rest)))
          (Cmeet (Cjoin (Cjoin (basicBar p) (Cbar rest)) [p])
                 (Cjoin (Cjoin (basicBar p) (Cbar rest)) rest)) :=
        Cequiv.trans (join_comm (Cmeet [p] rest) (Cjoin (basicBar p) (Cbar rest)))
          (join_meet_distrib (Cjoin (basicBar p) (Cbar rest)) [p] rest)
      exact Cle.trans (le_meet hP hR) (Cequiv_iff_le.mp equiv).2

/-- **Complement law (join):** `C ⊔ C̄ ≡ ⊤`.  With `C ⊔ C̄ ≤ ⊤` always (`le_top`). -/
theorem compl_sup (C : StdCtx) : Cequiv (Cjoin C (Cbar C)) Ctop :=
  Cequiv_iff_le.mpr ⟨le_top _, compl_sup_ge C⟩

/-! ## Theorem 2 — the Boolean algebra of standard constraints -/

/-- **Theorem 2 (Fairtlough–Mendler, TYPES 2000, §3).**  The standard constraints `𝕊`,
ordered by `Cle` modulo `Cequiv`, form a **Boolean algebra**: a bounded distributive
lattice (meet `⊓`, join `⊔`, bounds `⊥ ≤ · ≤ ⊤`, *both* distributive laws) in which every
`C` has a complement `C̄ = Cbar C ∈ 𝕊` satisfying `C ⊓ C̄ ≡ ⊥` and `C ⊔ C̄ ≡ ⊤`.

`𝕊` carries only *finitary* meets and joins (`Cmeet`, `Cjoin` are binary), so this is an
**incomplete** Boolean algebra — the intended result: the *complete* Boolean algebras are
the fixpoints of the assembly tower, whereas the syntactic constraint algebra is finitary.
The complement `Cbar` avoids the paper's `2^|I|` powerset normal form (it is a `foldr ⊔ ⊥`
of the 2-basic De Morgan duals `[Kᵢ,Lᵢ]‾ = [⊤,Kᵢ] ⊓ [Lᵢ,⊥]`), yet agrees with it up to `≈`. -/
theorem thm2_boolean_algebra :
    -- bounded distributive lattice (both distributive laws)
    (∀ C D, Cequiv (Cmeet C D) (Cmeet D C)) ∧
    (∀ C D E, Cequiv (Cmeet (Cmeet C D) E) (Cmeet C (Cmeet D E))) ∧
    (∀ C, Cequiv (Cmeet C C) C) ∧
    (∀ C D, Cequiv (Cjoin C D) (Cjoin D C)) ∧
    (∀ C D E, Cequiv (Cjoin (Cjoin C D) E) (Cjoin C (Cjoin D E))) ∧
    (∀ C, Cequiv (Cjoin C C) C) ∧
    (∀ C D, Cequiv (Cmeet C (Cjoin C D)) C) ∧
    (∀ C D, Cequiv (Cjoin C (Cmeet C D)) C) ∧
    (∀ C D E, Cequiv (Cjoin C (Cmeet D E)) (Cmeet (Cjoin C D) (Cjoin C E))) ∧
    (∀ C D E, Cequiv (Cmeet C (Cjoin D E)) (Cjoin (Cmeet C D) (Cmeet C E))) ∧
    (∀ C, Cequiv (Cmeet C Ctop) C) ∧
    (∀ C, Cequiv (Cjoin C Cbot) C) ∧
    (∀ C, Cequiv (Cmeet C Cbot) Cbot) ∧
    (∀ C, Cequiv (Cjoin C Ctop) Ctop) ∧
    -- Boolean complement: every `C` is complemented by `Cbar C`
    (∀ C, Cequiv (Cmeet C (Cbar C)) Cbot) ∧
    (∀ C, Cequiv (Cjoin C (Cbar C)) Ctop) :=
  ⟨meet_comm, meet_assoc, meet_idem, join_comm, join_assoc, join_idem,
   absorb_meet_join, absorb_join_meet, join_meet_distrib, meet_join_distrib,
   meet_top, join_bot, meet_bot, join_top, compl_inf, compl_sup⟩

/-! ## Uniqueness of complements (and hence `Cbar` respects `≈`)

The standard Boolean-algebra argument: if `B` complements `C` then
`B ≡ B ⊓ ⊤ ≡ B ⊓ (C ⊔ C̄) ≡ (B⊓C) ⊔ (B⊓C̄) ≡ ⊥ ⊔ (B⊓C̄) ≡ B ⊓ C̄`, and symmetrically
`C̄ ≡ B ⊓ C̄`; hence `B ≡ C̄`.  This makes the complement well-defined modulo `≈`. -/

/-- **Complements are unique.**  Any `B` with `C ⊓ B ≡ ⊥` and `C ⊔ B ≡ ⊤` equals `Cbar C`. -/
theorem compl_unique {C B : StdCtx} (hm : Cequiv (Cmeet C B) Cbot)
    (hj : Cequiv (Cjoin C B) Ctop) : Cequiv B (Cbar C) := by
  have hmb : Cequiv (Cmeet B C) Cbot := Cequiv.trans (meet_comm B C) hm
  have hcb : Cequiv (Cmeet (Cbar C) C) Cbot :=
    Cequiv.trans (meet_comm (Cbar C) C) (compl_inf C)
  have e1 : Cequiv B (Cmeet B (Cbar C)) :=
    Cequiv.trans (meet_top B).symm
     (Cequiv.trans (meet_congr (Cequiv.rfl' B) (compl_sup C).symm)
      (Cequiv.trans (meet_join_distrib B C (Cbar C))
       (Cequiv.trans (join_congr hmb (Cequiv.rfl' (Cmeet B (Cbar C))))
        (Cequiv.trans (join_comm Cbot (Cmeet B (Cbar C))) (join_bot (Cmeet B (Cbar C)))))))
  have e2 : Cequiv (Cbar C) (Cmeet B (Cbar C)) :=
    Cequiv.trans (meet_top (Cbar C)).symm
     (Cequiv.trans (meet_congr (Cequiv.rfl' (Cbar C)) hj.symm)
      (Cequiv.trans (meet_join_distrib (Cbar C) C B)
       (Cequiv.trans (join_congr hcb (Cequiv.rfl' (Cmeet (Cbar C) B)))
        (Cequiv.trans (join_comm Cbot (Cmeet (Cbar C) B))
         (Cequiv.trans (join_bot (Cmeet (Cbar C) B)) (meet_comm (Cbar C) B))))))
  exact Cequiv.trans e1 e2.symm

/-- **`Cbar` respects `≈`.**  `C ≡ C'` ⟹ `C̄ ≡ C̄'` (the complement is well-defined on
`𝕊/≈`): `C̄'` also complements `C` by transporting the two laws along `C ≡ C'`. -/
theorem compl_congr {C C' : StdCtx} (h : Cequiv C C') : Cequiv (Cbar C) (Cbar C') := by
  have hm : Cequiv (Cmeet C (Cbar C')) Cbot :=
    Cequiv.trans (meet_congr h (Cequiv.rfl' (Cbar C'))) (compl_inf C')
  have hj : Cequiv (Cjoin C (Cbar C')) Ctop :=
    Cequiv.trans (join_congr h (Cequiv.rfl' (Cbar C'))) (compl_sup C')
  exact (compl_unique hm hj).symm

/-! ## Bundled Mathlib `BooleanAlgebra` on the quotient `𝕊 = StdCtx/≈`

Every operation descends to the setoid quotient by its congruence lemma (`meet_congr`,
`join_congr`, `compl_congr`, and `Cle`'s respect for `≈`), and each `BooleanAlgebra` axiom
is the corresponding `Cle`/`Cequiv` fact.  `sdiff`/`himp` take Mathlib's defaults. -/

/-- Constraint-equivalence `≈` as a `Setoid` on standard constraints. -/
def stdSetoid : Setoid StdCtx where
  r := Cequiv
  iseqv := ⟨Cequiv.rfl', fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The constraint algebra `𝕊 = StdCtx / ≈`, carrying the Boolean-algebra instance below. -/
def CQuot : Type := Quotient stdSetoid

/-- Class of a standard constraint into `𝕊`. -/
def CQuot.mk (C : StdCtx) : CQuot := Quotient.mk stdSetoid C

/-- **Theorem 2, bundled.**  `𝕊 = StdCtx/≈` is a Mathlib `BooleanAlgebra`.  The lattice
data are the lifts of `Cmeet`/`Cjoin`, the complement is the lift of `Cbar`, bounds are
`⟦⊤⟧`/`⟦⊥⟧`, and every axiom reduces (on representatives) to a lemma proved above. -/
instance CQuot.instBooleanAlgebra : BooleanAlgebra CQuot where
  le x y := Quotient.liftOn₂ x y Cle fun _ _ _ _ ha hb => propext
    ⟨fun h => Cle.trans (Cequiv_iff_le.mp ha).2 (Cle.trans h (Cequiv_iff_le.mp hb).1),
     fun h => Cle.trans (Cequiv_iff_le.mp ha).1 (Cle.trans h (Cequiv_iff_le.mp hb).2)⟩
  sup x y := Quotient.liftOn₂ x y (fun a b => CQuot.mk (Cjoin a b))
    fun _ _ _ _ ha hb => Quotient.sound (join_congr ha hb)
  inf x y := Quotient.liftOn₂ x y (fun a b => CQuot.mk (Cmeet a b))
    fun _ _ _ _ ha hb => Quotient.sound (meet_congr ha hb)
  compl x := Quotient.liftOn x (fun a => CQuot.mk (Cbar a))
    fun _ _ ha => Quotient.sound (compl_congr ha)
  top := CQuot.mk Ctop
  bot := CQuot.mk Cbot
  le_refl := by rintro ⟨a⟩; exact Cle.rfl' a
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hbc; exact Cle.trans hab hbc
  le_antisymm := by rintro ⟨a⟩ ⟨b⟩ hab hba; exact Quotient.sound (Cequiv_iff_le.mpr ⟨hab, hba⟩)
  le_sup_left := by rintro ⟨a⟩ ⟨b⟩; exact le_join_left a b
  le_sup_right := by rintro ⟨a⟩ ⟨b⟩; exact le_join_right a b
  sup_le := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hac hbc; exact join_lub hac hbc
  inf_le_left := by rintro ⟨a⟩ ⟨b⟩; exact meet_le_left a b
  inf_le_right := by rintro ⟨a⟩ ⟨b⟩; exact meet_le_right a b
  le_inf := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ hab hac; exact le_meet hab hac
  le_sup_inf := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact (Cequiv_iff_le.mp (join_meet_distrib a b c)).2
  le_top := by rintro ⟨a⟩; exact le_top a
  bot_le := by rintro ⟨a⟩; exact bot_le a
  inf_compl_le_bot := by rintro ⟨a⟩; exact (Cequiv_iff_le.mp (compl_inf a)).1
  top_le_sup_compl := by rintro ⟨a⟩; exact (Cequiv_iff_le.mp (compl_sup a)).2

/-! ## Sanity checks -/

-- Theorem 2 complement laws on concrete small constraints (independent atoms `p₀,p₁`).
-- 1-basic `C = [p₀, p₁]` (i.e. `p₀ ⊃ (x ∨ p₁)`): complement is `[⊤,p₀] ⊓ [p₁,⊥]`.
example : Cbar [(pvar 0, pvar 1)] = Cjoin (basicBar (pvar 0, pvar 1)) Cbot := rfl
example : Cequiv (Cmeet [(pvar 0, pvar 1)] (Cbar [(pvar 0, pvar 1)])) Cbot :=
  compl_inf _
example : Cequiv (Cjoin [(pvar 0, pvar 1)] (Cbar [(pvar 0, pvar 1)])) Ctop :=
  compl_sup _
-- 2-basic `C = [p₀,p₁] ⊓ [p₂,p₃]`.
example : Cequiv
    (Cmeet [(pvar 0, pvar 1), (pvar 2, pvar 3)] (Cbar [(pvar 0, pvar 1), (pvar 2, pvar 3)]))
    Cbot := compl_inf _
example : Cequiv
    (Cjoin [(pvar 0, pvar 1), (pvar 2, pvar 3)] (Cbar [(pvar 0, pvar 1), (pvar 2, pvar 3)]))
    Ctop := compl_sup _

-- The bundled quotient `𝕊` is a genuine Mathlib `BooleanAlgebra`, and the class into it
-- carries the operations: `⟦C⟧ ⊔ ⟦D⟧ = ⟦C ⊔ D⟧`, `(⟦C⟧)ᶜ = ⟦C̄⟧`, bounds `⟦⊤⟧`/`⟦⊥⟧`.
example : BooleanAlgebra CQuot := inferInstance
example (C D : StdCtx) : CQuot.mk C ⊔ CQuot.mk D = CQuot.mk (Cjoin C D) := rfl
example (C D : StdCtx) : CQuot.mk C ⊓ CQuot.mk D = CQuot.mk (Cmeet C D) := rfl
example (C : StdCtx) : (CQuot.mk C)ᶜ = CQuot.mk (Cbar C) := rfl
example : (⊤ : CQuot) = CQuot.mk Ctop := rfl
example : (⊥ : CQuot) = CQuot.mk Cbot := rfl
-- The Boolean law `x ⊓ xᶜ = ⊥` now holds by Mathlib's generic API, via our complement.
example (C : StdCtx) : CQuot.mk C ⊓ (CQuot.mk C)ᶜ = ⊥ := inf_compl_eq_bot

-- Lemma 9 at `m = 0,1,2`: `χ₀, χ₁, χ₂` are concrete PLL non-theorems.
example : ¬ Nonempty (LaxND [] (chi 0)) := lemma9 0
example : ¬ Nonempty (LaxND [] (chi 1)) := lemma9 1
example : ¬ Nonempty (LaxND [] (chi 2)) := lemma9 2

-- Corollary 10 on a concrete finite constraint set `{⊤, ⊥}`.
example : ∃ φ : PLLFormula,
    (∀ C ∈ ({[], [(truePLL, falsePLL)]} : Finset StdCtx),
      Nonempty (LaxND [] (subC C φ))) ∧ ¬ Nonempty (LaxND [] φ) :=
  corollary10 {[], [(truePLL, falsePLL)]}

end Ctx
end PLLND

#print axioms PLLND.Ctx.lemma9
#print axioms PLLND.Ctx.lemma8
#print axioms PLLND.Ctx.corollary10
#print axioms PLLND.Ctx.thm2_bounded_distributive_lattice
#print axioms PLLND.Ctx.thm2_boolean_algebra
#print axioms PLLND.Ctx.compl_inf
#print axioms PLLND.Ctx.compl_sup
#print axioms PLLND.Ctx.compl_unique
#print axioms PLLND.Ctx.CQuot.instBooleanAlgebra
#print axioms PLLND.Ctx.Cle_iff_provable
