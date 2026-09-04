import LaxLogic.PLLSemUICtx

/-!
# The one-world residue obstruction: the general fails-half, PROVED

Route doc §0(m) certified, per instance, that frame-relative
constraint-commutation fails on chain3 and the fork — each time by the
SAME one-world countermodel.  This file proves the general lemma the
instances were pointing at.

**The residue model** `residue n₀`: one world, infallible, both
relations total, and exactly one atom `n₀` true.  At its point the
◯-clause trivialises, and — for a constraint `C` that is *named with a
residue pair* (`ResiduePair n₀ bad C`: some pair `(α_{n₀}, ⋁ covers)`
with covers named in `bad`, every other pair named in `bad`, and
`n₀ ∉ bad`) — the constraint application collapses to the identity
(`residue_applyC`), so the whole translation `subC C` evaluates as if
`◯` were erased.  Such a `C` is exactly what Lemma 7's recipe produces
from a finite model with a NON-FALLIBLE Rₘ-stable world named `n₀`
(the covers and the other stable worlds carry the other names).

**The obstruction** (`residue_obstruction`, engine form): if a p-free
IPL formula θ derives `X` and holds at the residue point, then any
`IsIPCAll`-value `A` of `X` also holds there (spec + soundness), so
`A :: Θ` cannot derive any formula the residue point refutes, for any
frame theory Θ true at the point.

**Headlines**: with θ := the diagram `n₀ ∧ ⋀_{a ∈ bad} ¬a`,

* `fails_half_boxp_imp_p` — row `∀p.(◯p⊃p) = ⊥`: any IPC ∀p-value `A`
  of `(◯p⊃p)^C` is CONSISTENT with every `n₀`-avoiding frame theory of
  negated atoms: `A :: Θ ⊬ ⊥`.  Since the translated PLL value is
  `⊥^C = ⊥`, frame-relative commutation fails.
* `fails_half_box_lob` — row `∀p.◯(◯p⊃p) = ◯⊥`: likewise
  `A :: Θ ⊬ (◯⊥)^C`.

Both are fully general in the constraint (only the `ResiduePair` shape
is used) and in the frame theory.  Together with the sandwich
(`PLLSemUICtx.lean`) this closes the circle: the constraint route
computes the substitution fragment exactly, and no frame theory over
the same names can bridge the `lowT`/`sideT` gap — the constraint POOL
itself must grow.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open Ctx

/-! ## The residue model -/

/-- One infallible world, total relations, exactly the atom `n₀` true. -/
def residue (n₀ : String) : ConstraintModel where
  W := PUnit
  Ri := fun _ _ => True
  Rm := fun _ _ => True
  F := ∅
  V := fun a => {_u : PUnit | a = n₀}
  refl_i := fun _ => trivial
  trans_i := fun _ _ => trivial
  refl_m := fun _ => trivial
  trans_m := fun _ _ => trivial
  sub_mi := fun _ => trivial
  hered_F := fun _ h => h.elim
  hered_V := fun _ h => h
  full_F := fun h => h.elim

theorem residue_force_prop {n₀ a : String} {u : PUnit} :
    (residue n₀).force u (.prop a) ↔ a = n₀ := Iff.rfl

theorem residue_force_bot {n₀ : String} {u : PUnit} :
    ¬ (residue n₀).force u .falsePLL := fun h => h

theorem residue_force_ifThen {n₀ : String} {A B : PLLFormula} {u : PUnit} :
    (residue n₀).force u (A.ifThen B) ↔
      ((residue n₀).force u A → (residue n₀).force u B) := by
  constructor
  · intro h ha
    exact h u trivial ha
  · intro h v _ ha
    cases v; cases u
    exact h ha

/-! ## Named constraints with a residue pair -/

/-- The shape Lemma 7's recipe gives a constraint at a model with a
non-fallible Rₘ-stable world named `n₀`: that world's pair is present
with its covers named in `bad`, every other pair is named in `bad`,
and `n₀ ∉ bad`. -/
structure ResiduePair (n₀ : String) (bad : List String) (C : StdCtx) : Prop where
  pair : ∃ Ls, ((PLLFormula.prop n₀, Ctx.bigOr Ls) ∈ C ∧
    ∀ x ∈ Ls, ∃ a ∈ bad, x = PLLFormula.prop a)
  named : ∀ kl ∈ C, kl.1 = PLLFormula.prop n₀ ∨ ∃ a ∈ bad, kl.1 = PLLFormula.prop a
  fresh : n₀ ∉ bad

/-- **The collapse**: at the residue point, applying a residue-paired
constraint is the identity — `C[x]` is forced iff `x` is. -/
theorem residue_applyC {n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) (x : PLLFormula) (u : PUnit) :
    (residue n₀).force u (applyC C x) ↔ (residue n₀).force u x := by
  constructor
  · intro hf
    obtain ⟨Ls, hmem, hLs⟩ := h.pair
    have hb := (force_applyC_iff (residue n₀) C x u).mp hf _ hmem
    have hxl := residue_force_ifThen.mp hb rfl
    rcases hxl with hx | hLor
    · exact hx
    · rcases (force_bigOr_iff (residue n₀) Ls u).mp hLor with ⟨q, hq, hqf⟩ | hF
      · obtain ⟨a, ha, rfl⟩ := hLs q hq
        exact absurd (residue_force_prop.mp hqf ▸ ha) h.fresh
      · exact hF.elim
  · intro hx
    refine (force_applyC_iff (residue n₀) C x u).mpr ?_
    rintro ⟨K, L⟩ hKL
    refine residue_force_ifThen.mpr fun hK => ?_
    exact Or.inl hx

/-- The translated `◯⊥` fails at the residue point. -/
theorem residue_not_subC_boxBot {n₀ : String} {bad : List String}
    {C : StdCtx} (h : ResiduePair n₀ bad C) {u : PUnit} :
    ¬ (residue n₀).force u (subC C PLLFormula.falsePLL.somehow) :=
  fun hf => residue_force_bot ((residue_applyC h _ u).mp hf)

/-! ## The diagram -/

/-- `¬a` as a formula. -/
def negA (a : String) : PLLFormula := (PLLFormula.prop a).ifThen .falsePLL

/-- The diagram of the residue point over the alphabet `n₀ :: bad`:
`⋀_{a ∈ bad} ¬a ∧ n₀`. -/
def diag (n₀ : String) (bad : List String) : PLLFormula :=
  bad.foldr (fun a acc => (negA a).and acc) (.prop n₀)

theorem diag_force_iff {n₀ : String} {bad : List String}
    (D : ConstraintModel) (w : D.W) :
    D.force w (diag n₀ bad) ↔
      (D.force w (.prop n₀) ∧ ∀ a ∈ bad, D.force w (negA a)) := by
  induction bad with
  | nil =>
      constructor
      · intro h
        exact ⟨h, fun a ha => absurd ha (List.not_mem_nil)⟩
      · intro h
        exact h.1
  | cons b bs ih =>
      constructor
      · rintro ⟨hb, hrest⟩
        obtain ⟨h₀, hall⟩ := ih.mp hrest
        refine ⟨h₀, fun a ha => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hb
        · exact hall a ha
      · rintro ⟨h₀, hall⟩
        exact ⟨hall b (List.mem_cons_self ..),
          ih.mpr ⟨h₀, fun a ha => hall a (List.mem_cons_of_mem _ ha)⟩⟩

theorem diag_pfree {p n₀ : String} {bad : List String}
    (hpn : p ≠ n₀) (hpb : p ∉ bad) : p ∉ (diag n₀ bad).atoms := by
  induction bad with
  | nil =>
      intro h
      exact hpn (by simpa [diag] using h)
  | cons b bs ih =>
      intro h
      have hb : p ≠ b := fun hpb' => hpb (hpb' ▸ List.mem_cons_self ..)
      have hbs : p ∉ bs := fun h' => hpb (List.mem_cons_of_mem _ h')
      rcases (by simpa [diag, negA] using h :
          p ∈ (PLLFormula.prop b).atoms ∨ p ∈ (diag n₀ bs).atoms) with h' | h'
      · exact hb (by simpa using h')
      · exact ih hbs h'

theorem diag_isIPL {n₀ : String} {bad : List String} :
    isIPL (diag n₀ bad) := by
  induction bad with
  | nil => trivial
  | cons b bs ih => exact ⟨⟨trivial, trivial⟩, ih⟩

/-- The residue point forces its own diagram. -/
theorem residue_diag {n₀ : String} {bad : List String} (hfr : n₀ ∉ bad) :
    (residue n₀).force PUnit.unit (diag n₀ bad) := by
  refine (diag_force_iff _ _).mpr ⟨rfl, fun a ha => ?_⟩
  refine residue_force_ifThen.mpr fun hpa => ?_
  exact absurd (residue_force_prop.mp hpa ▸ ha) hfr

/-! ## The diagram derives the translated rows (over ALL models) -/

/-- Core semantic step, row `◯p ⊃ p`: at any world of any model where
`n₀` holds and every `bad` atom is refuted, the translation
`(◯p⊃p)^C = C[p] ⊃ p` holds — a `C[p]`-world sees `p ∨ covers`; the
covers are `bad`-named, so forcing one makes the world fallible, and
fallible worlds force `p` anyway. -/
theorem sem_row1 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) (D : ConstraintModel) {w : D.W}
    (h₀ : D.force w (.prop n₀)) (hbad : ∀ a ∈ bad, D.force w (negA a)) :
    D.force w ((applyC C (.prop p)).ifThen (.prop p)) := by
  intro v hwv hv
  obtain ⟨Ls, hmem, hLs⟩ := h.pair
  have hb := (force_applyC_iff D C (.prop p) v).mp hv _ hmem
  have hpl := hb v (D.refl_i v) (D.force_hered hwv h₀)
  rcases hpl with hp | hLor
  · exact hp
  · rcases (force_bigOr_iff D Ls v).mp hLor with ⟨q, hq, hqf⟩ | hF
    · obtain ⟨a, ha, rfl⟩ := hLs q hq
      have hfall : D.force v .falsePLL :=
        D.force_hered hwv (hbad a ha) v (D.refl_i v) hqf
      exact D.force_of_fallible hfall
    · exact D.force_of_fallible hF

/-- The diagram derives `(◯p⊃p)^C`. -/
theorem diag_row1 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) :
    Nonempty (LaxND [diag n₀ bad]
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)))) := by
  refine completeness ?_
  intro D w hw
  have hd := (diag_force_iff D w).mp (hw _ (List.mem_singleton.mpr rfl))
  show D.force w ((applyC C (.prop p)).ifThen (.prop p))
  exact sem_row1 h D hd.1 hd.2

/-- The diagram derives `(◯(◯p⊃p))^C = C[(◯p⊃p)^C]`: the `n₀`-pairs
land in `sem_row1` one world up; the `bad`-named pairs are vacuous or
fallible. -/
theorem diag_row2 {p n₀ : String} {bad : List String} {C : StdCtx}
    (h : ResiduePair n₀ bad C) :
    Nonempty (LaxND [diag n₀ bad]
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow)) := by
  refine completeness ?_
  intro D w hw
  have hd := (diag_force_iff D w).mp (hw _ (List.mem_singleton.mpr rfl))
  show D.force w (applyC C ((applyC C (.prop p)).ifThen (.prop p)))
  refine (force_applyC_iff D C _ w).mpr ?_
  rintro ⟨K, L⟩ hKL
  intro v hwv hK
  rcases h.named _ hKL with hKn | ⟨a, ha, hKa⟩
  · refine Or.inl ?_
    exact sem_row1 h D (D.force_hered hwv hd.1)
      (fun a ha => D.force_hered hwv (hd.2 a ha))
  · have hKa' : K = PLLFormula.prop a := hKa
    subst hKa'
    have hfall : D.force v .falsePLL :=
      D.force_hered hwv (hd.2 a ha) v (D.refl_i v) hK
    exact D.force_of_fallible hfall

/-! ## The obstruction -/

/-- **Engine**: a p-free IPL premise θ that derives `X` and holds at
the residue point transports any `IsIPCAll`-value of `X` to the point
(spec + soundness); the point then blocks every derivation from
`A :: Θ` of anything it refutes. -/
theorem residue_obstruction {p n₀ : String} {X A ξ θ : PLLFormula}
    {Θ : List PLLFormula}
    (hA : IsIPCAll p isIPL X A)
    (hθp : p ∉ θ.atoms) (hθipl : isIPL θ)
    (hθX : Nonempty (LaxND [θ] X))
    (hθR : (residue n₀).force PUnit.unit θ)
    (hΘR : ∀ ψ ∈ Θ, (residue n₀).force PUnit.unit ψ)
    (hξR : ¬ (residue n₀).force PUnit.unit ξ) :
    ¬ Nonempty (LaxND (A :: Θ) ξ) := by
  rintro ⟨d⟩
  obtain ⟨dA⟩ := hA.greatest θ hθipl hθp hθX
  have hAR : (residue n₀).force PUnit.unit A :=
    soundness dA (residue n₀) PUnit.unit (fun ψ hψ => by
      rcases List.mem_singleton.mp hψ with rfl
      exact hθR)
  refine hξR (soundness d (residue n₀) PUnit.unit ?_)
  intro ψ hψ
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact hAR
  · exact hΘR ψ hψ

/-- Frame theories of `n₀`-avoiding negated atoms hold at the point. -/
theorem residue_theta {n₀ : String} {Θ : List PLLFormula}
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ∀ ψ ∈ Θ, (residue n₀).force PUnit.unit ψ := by
  intro ψ hψ
  obtain ⟨a, hne, rfl⟩ := hΘ ψ hψ
  exact residue_force_ifThen.mpr fun hpa =>
    absurd (residue_force_prop.mp hpa) hne

/-! ## The headlines: the general fails-half -/

/-- **General fails-half, row `∀p.(◯p⊃p) = ⊥`.**  For ANY constraint
`C` carrying a residue pair at `n₀` (the Lemma-7 shape at a
non-fallible Rₘ-stable world), ANY `IsIPCAll`-value `A` of the
translation `(◯p⊃p)^C`, and ANY frame theory `Θ` of `n₀`-avoiding
negated atoms (in particular the fallibility axioms):
`A :: Θ` is CONSISTENT.  The translated PLL value is
`(∀p.(◯p⊃p))^C = ⊥^C = ⊥`, so `A` is not `Θ`-equivalent to it —
frame-relative constraint-commutation FAILS, provably, at every such
constraint. -/
theorem fails_half_boxp_imp_p {p n₀ : String} {bad : List String}
    {C : StdCtx} {A : PLLFormula} {Θ : List PLLFormula}
    (h : ResiduePair n₀ bad C) (hpn : p ≠ n₀) (hpb : p ∉ bad)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p))) A)
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ¬ Nonempty (LaxND (A :: Θ) .falsePLL) :=
  residue_obstruction hA (diag_pfree hpn hpb) diag_isIPL (diag_row1 h)
    (residue_diag h.fresh) (residue_theta hΘ) residue_force_bot

/-- **General fails-half, row `∀p.◯(◯p⊃p) = ◯⊥`** (the Löb/sideways
row): likewise `A :: Θ ⊬ (◯⊥)^C`. -/
theorem fails_half_box_lob {p n₀ : String} {bad : List String}
    {C : StdCtx} {A : PLLFormula} {Θ : List PLLFormula}
    (h : ResiduePair n₀ bad C) (hpn : p ≠ n₀) (hpb : p ∉ bad)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) A)
    (hΘ : ∀ ψ ∈ Θ, ∃ a, a ≠ n₀ ∧ ψ = negA a) :
    ¬ Nonempty (LaxND (A :: Θ) (subC C PLLFormula.falsePLL.somehow)) :=
  residue_obstruction hA (diag_pfree hpn hpb) diag_isIPL (diag_row2 h)
    (residue_diag h.fresh) (residue_theta hΘ) (residue_not_subC_boxBot h)

/-! ## The certified instance, re-derived from the general lemma

chain3's Lemma-7 constraint `C = [(a0, a1 ∨ ⊥), (a2, ⊥)]` with frame
theory `Θ = [¬a2]` — the §0(m) instance, now a corollary. -/

/-- chain3's constraint. -/
def chain3C : StdCtx :=
  [(PLLFormula.prop "a0", Ctx.bigOr [PLLFormula.prop "a1"]),
   (PLLFormula.prop "a2", Ctx.bigOr [])]

theorem chain3C_residue : ResiduePair "a0" ["a1", "a2"] chain3C where
  pair := ⟨[PLLFormula.prop "a1"], List.mem_cons_self ..,
    fun x hx => ⟨"a1", List.mem_cons_self .., by
      simpa using List.mem_singleton.mp hx⟩⟩
  named := by
    intro kl hkl
    rcases List.mem_cons.mp hkl with rfl | hkl
    · exact Or.inl rfl
    · rcases List.mem_cons.mp hkl with rfl | hkl
      · exact Or.inr ⟨"a2", by simp, rfl⟩
      · exact absurd hkl (List.not_mem_nil)
  fresh := by simp

/-- The §0(m) chain3 certificate, generalised: EVERY IPC ∀p-value of
`(◯p⊃p)^{chain3C}` is consistent with the fallibility axiom `¬a2`. -/
theorem chain3_fails_half {A : PLLFormula}
    (hA : IsIPCAll "p" isIPL
      (subC chain3C ((PLLFormula.prop "p").somehow.ifThen (.prop "p"))) A) :
    ¬ Nonempty (LaxND [A, negA "a2"] .falsePLL) :=
  fails_half_boxp_imp_p chain3C_residue (by simp) (by simp) hA
    (fun ψ hψ => ⟨"a2", by simp, List.mem_singleton.mp hψ ▸ rfl⟩)

/-! ## The holds-half: fully-fallible (chain2-style) constraints

When EVERY Rₘ-stable world of the generating model is fallible, every
pair of the Lemma-7 constraint is named by a Θ-negated atom
(`ThetaNamed`).  Then Θ refutes every guard, so Θ derives EVERY
constraint application `C[x]` vacuously (`theta_applyC`) — and
frame-relative commutation HOLDS on both frame-changing rows:

* row `∀p.(◯p⊃p) = ⊥`: the spec's lower bound gives `A ⊢ C[p] ⊃ p`,
  Θ gives `C[p]`, so `A, Θ ⊢ p` — a p-free context deriving the atom
  p; substituting `p := ⊥` through the derivation (`substND`) lands
  `A, Θ ⊢ ⊥` (`holds_half_boxp_imp_p`);
* row `∀p.◯(◯p⊃p) = ◯⊥`: Θ derives the translated value `C[⊥]`
  outright, and (via the spec's greatest-property applied to the
  conjunction of Θ) Θ derives `A` itself — both directions of
  `A ≡_Θ (◯⊥)^C` (`holds_half_box_lob`).

Together with the fails-half above this is the full dichotomy for
Lemma-7-shaped constraints: commutation holds when all pair-names are
Θ-negated, and fails whenever some pair sits at a Θ-avoiding name
with `bad`-named covers. -/

/-- Every pair of `C` is named by a `Θ`-negated atom. -/
def ThetaNamed (Θ : List PLLFormula) (C : StdCtx) : Prop :=
  ∀ kl ∈ C, ∃ a, kl.1 = PLLFormula.prop a ∧ negA a ∈ Θ

/-- Composition (cut through `⊃`). -/
def compose {φ ψ : PLLFormula} {Δ : List PLLFormula}
    (d : LaxND [φ] ψ) (e : LaxND Δ φ) : LaxND Δ ψ :=
  .impElim ((LaxND.impIntro d).rename
    (fun _ h => absurd h List.not_mem_nil)) e

/-- Under `ThetaNamed`, any context that derives the Θ-negations
derives every constraint application: each guard is refuted. -/
theorem theta_applyC {Θ : List PLLFormula} {C : StdCtx}
    (hC : ThetaNamed Θ C) (x : PLLFormula) {Δ : List PLLFormula}
    (hsub : ∀ ψ ∈ Θ, Nonempty (LaxND Δ ψ)) :
    Nonempty (LaxND Δ (applyC C x)) := by
  induction C with
  | nil => exact ⟨truePLL_intro Δ⟩
  | cons hd tl ih =>
      obtain ⟨K, L⟩ := hd
      obtain ⟨a, hK, hmem⟩ := hC (K, L) (List.mem_cons_self ..)
      have hKa : K = PLLFormula.prop a := hK
      subst hKa
      obtain ⟨dneg⟩ := hsub _ hmem
      obtain ⟨dtl⟩ := ih (fun kl h => hC kl (List.mem_cons_of_mem _ h))
      refine ⟨.andIntro (.impIntro ?_) dtl⟩
      exact .falsoElim _
        (.impElim (dneg.weaken _) (.iden (List.mem_cons_self ..)))

/-- Conjunction of a context. -/
def andAll : List PLLFormula → PLLFormula
  | [] => truePLL
  | ψ :: Ψ => ψ.and (andAll Ψ)

theorem andAll_intro (Θ : List PLLFormula) {Δ : List PLLFormula}
    (h : ∀ ψ ∈ Θ, ψ ∈ Δ) : Nonempty (LaxND Δ (andAll Θ)) := by
  induction Θ with
  | nil => exact ⟨truePLL_intro Δ⟩
  | cons χ Ψ ih =>
      obtain ⟨d⟩ := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
      exact ⟨.andIntro (.iden (h _ (List.mem_cons_self ..))) d⟩

theorem andAll_proj {Θ : List PLLFormula} {ψ : PLLFormula} (h : ψ ∈ Θ) :
    Nonempty (LaxND [andAll Θ] ψ) := by
  induction Θ with
  | nil => exact absurd h List.not_mem_nil
  | cons χ Ψ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨(LaxND.iden (List.mem_singleton.mpr rfl)).andElim1⟩
      · obtain ⟨d⟩ := ih h
        exact ⟨compose d
          ((LaxND.iden (List.mem_singleton.mpr rfl)).andElim2)⟩

theorem andAll_pfree {p : String} {Θ : List PLLFormula}
    (h : ∀ ψ ∈ Θ, p ∉ ψ.atoms) : p ∉ (andAll Θ).atoms := by
  induction Θ with
  | nil => simp [andAll, truePLL]
  | cons χ Ψ ih =>
      intro hm
      rcases (by simpa [andAll] using hm :
          p ∈ χ.atoms ∨ p ∈ (andAll Ψ).atoms) with hm | hm
      · exact h χ (List.mem_cons_self ..) hm
      · exact ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)) hm

theorem andAll_isIPL {Θ : List PLLFormula}
    (h : ∀ ψ ∈ Θ, isIPL ψ) : isIPL (andAll Θ) := by
  induction Θ with
  | nil => exact ⟨trivial, trivial⟩
  | cons χ Ψ ih =>
      exact ⟨h χ (List.mem_cons_self ..),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))⟩

/-- Substitution `p := ⊥` fixes a p-free context. -/
theorem map_substP_of_pfree {p : String} {χ : PLLFormula}
    {L : List PLLFormula} (h : ∀ ψ ∈ L, p ∉ ψ.atoms) :
    L.map (substP p χ) = L := by
  induction L with
  | nil => rfl
  | cons φ Ψ ih =>
      simp only [List.map_cons]
      rw [substP_of_not_mem (h φ (List.mem_cons_self ..)),
        ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))]

/-- **Holds-half, row `∀p.(◯p⊃p) = ⊥`.**  For a fully-fallible
constraint (every pair Θ-negated), every `IsIPCAll`-value `A` of
`(◯p⊃p)^C` is Θ-EQUIVALENT to the translated PLL value `⊥`:
frame-relative commutation holds. -/
theorem holds_half_boxp_imp_p {p : String} {Θ : List PLLFormula}
    {C : StdCtx} {A : PLLFormula}
    (hC : ThetaNamed Θ C) (hΘp : ∀ ψ ∈ Θ, p ∉ ψ.atoms)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p))) A) :
    Nonempty (LaxND (A :: Θ) .falsePLL) ∧
    Nonempty (LaxND (.falsePLL :: Θ) A) := by
  constructor
  · obtain ⟨dlow⟩ := hA.lower
    have dlow' : LaxND (A :: Θ) ((applyC C (.prop p)).ifThen (.prop p)) :=
      dlow.rename (by
        intro ψ h
        rcases List.mem_singleton.mp h with rfl
        exact List.mem_cons_self ..)
    obtain ⟨dapp⟩ := theta_applyC hC (.prop p) (Δ := A :: Θ)
      (fun ψ h => ⟨.iden (List.mem_cons_of_mem _ h)⟩)
    have dp : LaxND (A :: Θ) (.prop p) := .impElim dlow' dapp
    have dsub := substND p .falsePLL dp
    rw [List.map_cons, substP_of_not_mem hA.pfree,
      map_substP_of_pfree hΘp] at dsub
    exact ⟨by simpa [substP] using dsub⟩
  · exact ⟨.falsoElim _ (.iden (List.mem_cons_self ..))⟩

/-- **Holds-half, row `∀p.◯(◯p⊃p) = ◯⊥`** (the Löb/sideways row):
both directions of `A ≡_Θ (◯⊥)^C` — Θ derives the translated value
outright, and derives `A` through the spec's greatest-property at the
conjunction of Θ. -/
theorem holds_half_box_lob {p : String} {Θ : List PLLFormula}
    {C : StdCtx} {A : PLLFormula}
    (hC : ThetaNamed Θ C) (hΘp : ∀ ψ ∈ Θ, p ∉ ψ.atoms)
    (hΘipl : ∀ ψ ∈ Θ, isIPL ψ)
    (hA : IsIPCAll p isIPL
      (subC C ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) A) :
    Nonempty (LaxND (A :: Θ) (subC C PLLFormula.falsePLL.somehow)) ∧
    Nonempty (LaxND (subC C PLLFormula.falsePLL.somehow :: Θ) A) := by
  constructor
  · obtain ⟨d⟩ := theta_applyC hC .falsePLL (Δ := A :: Θ)
      (fun ψ h => ⟨.iden (List.mem_cons_of_mem _ h)⟩)
    exact ⟨d⟩
  · -- [⋀Θ] ⊢ X₂ vacuously, so [⋀Θ] ⊢ A by the spec; recompose over Θ.
    obtain ⟨dX⟩ := theta_applyC hC
      ((applyC C (.prop p)).ifThen (.prop p)) (Δ := [andAll Θ])
      (fun ψ h => andAll_proj h)
    obtain ⟨dA⟩ := hA.greatest (andAll Θ) (andAll_isIPL hΘipl)
      (andAll_pfree hΘp) ⟨dX⟩
    obtain ⟨dand⟩ := andAll_intro Θ
      (Δ := subC C PLLFormula.falsePLL.somehow :: Θ)
      (fun ψ h => List.mem_cons_of_mem _ h)
    exact ⟨compose dA dand⟩

/-! ## The chain2 instance, re-derived from the general lemma

chain2's Lemma-7 constraint `C = [(a1, ⊥)]` (single stable world,
fallible) with frame theory `Θ = [¬a1]` — the §0(m) holds-instance,
now a corollary. -/

/-- chain2's constraint. -/
def chain2C : StdCtx := [(PLLFormula.prop "a1", Ctx.bigOr [])]

theorem chain2C_thetaNamed : ThetaNamed [negA "a1"] chain2C := by
  intro kl hkl
  rcases List.mem_cons.mp hkl with rfl | hkl
  · exact ⟨"a1", rfl, List.mem_cons_self ..⟩
  · exact absurd hkl List.not_mem_nil

/-- The §0(m) chain2 verdict, generalised: EVERY IPC ∀p-value of
`(◯p⊃p)^{chain2C}` is `[¬a1]`-equivalent to `⊥`. -/
theorem chain2_holds_half {A : PLLFormula}
    (hA : IsIPCAll "p" isIPL
      (subC chain2C ((PLLFormula.prop "p").somehow.ifThen (.prop "p"))) A) :
    Nonempty (LaxND [A, negA "a1"] .falsePLL) ∧
    Nonempty (LaxND [.falsePLL, negA "a1"] A) :=
  holds_half_boxp_imp_p chain2C_thetaNamed
    (by
      intro ψ hψ
      rcases List.mem_singleton.mp hψ with rfl
      simp [negA])
    hA

/-! ## The model level: Lemma 7's recipe `c0Of`, and the lifted dichotomy

Finite models as Boolean tables (worlds `0..n-1`), the Lemma-7
constraint `c0Of` — one pair `(α_u, ⋁{α_v : v an immediate strict
Rᵢ-successor of u})` per Rₘ-stable world `u`, with `α_w` an atom
naming `w` — and the fallibility frame theory `falAxioms`.  The two
shape lemmas: with every stable world fallible, `c0Of` is
`ThetaNamed`; at a non-fallible stable world it carries a
`ResiduePair`.  Composing with the two halves gives the MODEL-LEVEL
DICHOTOMY, one iff per frame-changing row:

    commutation relative to the fallibility axioms
      ⟺  every Rₘ-stable world of the model is fallible.

The naming `nm : Nat → String` is a parameter with an injectivity
hypothesis where needed (the codebase's own pattern — cf.
`exists_freshNames`/`nm_inj` in `PLLCtxCompleteness`); the probes'
naming `i ↦ "a‹i›"` is an instance. -/

/-- A finite model as tables (no frame laws assumed; the lift states
the ones it uses — only `Rᵢ`-reflexivity, for strictness of covers). -/
structure FinModel where
  n : Nat
  ri : Nat → Nat → Bool
  rm : Nat → Nat → Bool
  fal : Nat → Bool

def worldsOf (m : FinModel) : List Nat := List.range m.n

/-- `u` is Rₘ-stable: every Rₘ-successor sees back. -/
def stableB (m : FinModel) (u : Nat) : Bool :=
  (worldsOf m).all (fun t => !(m.rm u t) || m.rm t u)

/-- `v` is an immediate strict Rᵢ-successor (cover) of `u`. -/
def iSuccB (m : FinModel) (u v : Nat) : Bool :=
  m.ri u v && !(m.ri v u) &&
    (worldsOf m).all (fun t => !(m.ri u t) || !(m.ri t v) || (m.ri t u || m.ri v t))

/-- **Lemma 7's recipe**: one pair per stable world, guard = the
world's name, disjunction = the names of its covers. -/
def c0Of (nm : Nat → String) (m : FinModel) : StdCtx :=
  ((worldsOf m).filter (stableB m)).map (fun u =>
    (PLLFormula.prop (nm u),
      Ctx.bigOr (((worldsOf m).filter (iSuccB m u)).map
        (fun v => PLLFormula.prop (nm v)))))

/-- The fallibility frame theory: `¬α_w` for every fallible world. -/
def falAxioms (nm : Nat → String) (m : FinModel) : List PLLFormula :=
  ((worldsOf m).filter m.fal).map (fun w => negA (nm w))

/-- The names of all worlds other than `u₀`. -/
def badOf (nm : Nat → String) (m : FinModel) (u₀ : Nat) : List String :=
  ((worldsOf m).filter (fun v => v != u₀)).map nm

/-- **Shape lift, holds side**: all stable worlds fallible ⟹ every
pair of `c0Of` is named by a `falAxioms`-negated atom. -/
theorem c0Of_thetaNamed {nm : Nat → String} {m : FinModel}
    (h : ∀ u ∈ worldsOf m, stableB m u = true → m.fal u = true) :
    ThetaNamed (falAxioms nm m) (c0Of nm m) := by
  intro kl hkl
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkl
  have hu' := List.mem_filter.mp hu
  exact ⟨nm u, rfl,
    List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu'.1, h u hu'.1 hu'.2⟩, rfl⟩⟩

/-- **Shape lift, fails side**: a non-fallible stable world `u₀` gives
`c0Of` a residue pair at its name (covers are strict, hence ≠ u₀ under
Rᵢ-reflexivity; the other pairs are other-named; freshness by
injectivity of the naming). -/
theorem c0Of_residuePair {nm : Nat → String} (hnm : Function.Injective nm)
    {m : FinModel} (hrefl : ∀ w ∈ worldsOf m, m.ri w w = true)
    {u₀ : Nat} (hu₀ : u₀ ∈ worldsOf m)
    (hstab : stableB m u₀ = true) :
    ResiduePair (nm u₀) (badOf nm m u₀) (c0Of nm m) where
  pair := by
    refine ⟨((worldsOf m).filter (iSuccB m u₀)).map
      (fun v => PLLFormula.prop (nm v)),
      List.mem_map.mpr ⟨u₀, List.mem_filter.mpr ⟨hu₀, hstab⟩, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
    have hv' := List.mem_filter.mp hv
    refine ⟨nm v, List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv'.1, ?_⟩, rfl⟩, rfl⟩
    have hsucc := hv'.2
    simp only [iSuccB, Bool.and_eq_true, Bool.not_eq_true'] at hsucc
    refine bne_iff_ne.mpr ?_
    rintro rfl
    have hrr := hrefl v hv'.1
    rw [hsucc.1.2] at hrr
    exact Bool.false_ne_true hrr
  named := by
    intro kl hkl
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hkl
    have hu' := List.mem_filter.mp hu
    by_cases hcase : u = u₀
    · subst hcase; exact Or.inl rfl
    · exact Or.inr ⟨nm u,
        List.mem_map.mpr ⟨u, List.mem_filter.mpr ⟨hu'.1, bne_iff_ne.mpr hcase⟩, rfl⟩,
        rfl⟩
  fresh := by
    intro hmem
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp hmem
    have hv' := List.mem_filter.mp hv
    exact absurd (hnm hveq) (bne_iff_ne.mp hv'.2)

/-- `p` avoiding the naming keeps the fallibility axioms p-free. -/
theorem falAxioms_pfree {nm : Nat → String} {m : FinModel} {p : String}
    (hp : ∀ w ∈ worldsOf m, nm w ≠ p) :
    ∀ ψ ∈ falAxioms nm m, p ∉ ψ.atoms := by
  intro ψ hψ
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hψ
  have hw' := List.mem_filter.mp hw
  intro hmem
  have hpw : p = nm w := by simpa [negA] using hmem
  exact hp w hw'.1 hpw.symm

theorem falAxioms_isIPL {nm : Nat → String} {m : FinModel} :
    ∀ ψ ∈ falAxioms nm m, isIPL ψ := by
  intro ψ hψ
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hψ
  exact ⟨trivial, trivial⟩

/-- The fallibility axioms avoid the name of a non-fallible world. -/
theorem falAxioms_avoid {nm : Nat → String} (hnm : Function.Injective nm)
    {m : FinModel} {u₀ : Nat} (hfal : m.fal u₀ = false) :
    ∀ ψ ∈ falAxioms nm m, ∃ a, a ≠ nm u₀ ∧ ψ = negA a := by
  intro ψ hψ
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hψ
  have hw' := List.mem_filter.mp hw
  refine ⟨nm w, hnm.ne ?_, rfl⟩
  rintro rfl
  rw [hw'.2] at hfal
  exact Bool.true_eq_false.mp hfal

/-! ### The model-level dichotomy, one iff per frame-changing row -/

/-- **The dichotomy, row `∀p.(◯p⊃p) = ⊥`**: for any finite model `m`
(with reflexive `Rᵢ`), injective naming avoiding `p`, and ANY
`IsIPCAll`-value `A` of the translation `(◯p⊃p)^{c0Of m}`:

    A is falAxioms-equivalent to the translated value ⊥
      ⟺  every Rₘ-stable world of `m` is fallible.

(The ⊥ ⊢ A direction is trivial, so the iff is stated on the
substantive direction.) -/
theorem model_dichotomy_boxp_imp_p {nm : Nat → String}
    (hnm : Function.Injective nm) {m : FinModel}
    (hrefl : ∀ w ∈ worldsOf m, m.ri w w = true) {p : String}
    (hp : ∀ w ∈ worldsOf m, nm w ≠ p) {A : PLLFormula}
    (hA : IsIPCAll p isIPL
      (subC (c0Of nm m) ((PLLFormula.prop p).somehow.ifThen (.prop p))) A) :
    Nonempty (LaxND (A :: falAxioms nm m) .falsePLL) ↔
      ∀ u ∈ worldsOf m, stableB m u = true → m.fal u = true := by
  constructor
  · intro hder u₀ hu₀ hstab
    by_contra hfal'
    have hfal : m.fal u₀ = false := by
      cases hff : m.fal u₀ with
      | true => exact absurd hff hfal'
      | false => rfl
    refine fails_half_boxp_imp_p (c0Of_residuePair hnm hrefl hu₀ hstab)
      (fun hpe => hp u₀ hu₀ hpe.symm) ?_ hA (falAxioms_avoid hnm hfal) hder
    intro hmem
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp hmem
    exact hp v (List.mem_filter.mp hv).1 hveq
  · intro hall
    exact (holds_half_boxp_imp_p (c0Of_thetaNamed hall)
      (falAxioms_pfree hp) hA).1

/-- **The dichotomy, row `∀p.◯(◯p⊃p) = ◯⊥`** (Löb/sideways row):
`A` derives the translated value `(◯⊥)^{c0Of m}` relative to the
fallibility axioms ⟺ every stable world is fallible.  (The converse
derivation `value ⊢_Θ A` is the sandwich lower bound and holds
unconditionally.) -/
theorem model_dichotomy_box_lob {nm : Nat → String}
    (hnm : Function.Injective nm) {m : FinModel}
    (hrefl : ∀ w ∈ worldsOf m, m.ri w w = true) {p : String}
    (hp : ∀ w ∈ worldsOf m, nm w ≠ p) {A : PLLFormula}
    (hA : IsIPCAll p isIPL
      (subC (c0Of nm m)
        ((PLLFormula.prop p).somehow.ifThen (.prop p)).somehow) A) :
    Nonempty (LaxND (A :: falAxioms nm m)
        (subC (c0Of nm m) PLLFormula.falsePLL.somehow)) ↔
      ∀ u ∈ worldsOf m, stableB m u = true → m.fal u = true := by
  constructor
  · intro hder u₀ hu₀ hstab
    by_contra hfal'
    have hfal : m.fal u₀ = false := by
      cases hff : m.fal u₀ with
      | true => exact absurd hff hfal'
      | false => rfl
    refine fails_half_box_lob (c0Of_residuePair hnm hrefl hu₀ hstab)
      (fun hpe => hp u₀ hu₀ hpe.symm) ?_ hA (falAxioms_avoid hnm hfal) hder
    intro hmem
    obtain ⟨v, hv, hveq⟩ := List.mem_map.mp hmem
    exact hp v (List.mem_filter.mp hv).1 hveq
  · intro hall
    exact (holds_half_box_lob (c0Of_thetaNamed hall)
      (falAxioms_pfree hp) falAxioms_isIPL hA).1

/-! ### Coherence with the probes: chain2 and chain3 pin -/

/-- chain2 as tables. -/
def mChain2L : FinModel where
  n := 2
  ri := fun a b => a.ble b
  rm := fun a b => a.ble b
  fal := fun a => a == 1

/-- chain3 as tables (Rₘ rigid except 1 → 2, top fallible). -/
def mChain3L : FinModel where
  n := 3
  ri := fun a b => a.ble b
  rm := fun a b => a == b || (a == 1 && b == 2)
  fal := fun a => a == 2

/-- `c0Of` with the probes' naming reproduces the probes' constraints. -/
example : c0Of (fun i => "a" ++ toString i) mChain2L = chain2C := by decide
example : c0Of (fun i => "a" ++ toString i) mChain3L = chain3C := by decide

end SemUI
end PLLND
