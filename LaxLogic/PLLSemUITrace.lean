import LaxLogic.PLLSemUIDesc
import LaxLogic.PLLFinComp

/-!
# The descriptions functor and the realisability gfp

The residue discharges of `PLLSemUIDesc` ask, per `(C, x)`, for a
description-realisation pack into a target model together with a
distinguished triple over `x`.  This file supplies the two halves of
that question.

**The descriptions functor.**  Every world `c` of every constraint
model has a *closure description*

  `trace C cl c := ⟨ {χ ∈ cl | c ⊩ χ}, {χ ∈ cl | c ⊮ χ},
                     {χ ∈ cl | the whole m-row of c refutes χ} ⟩`,

a closure-maximal triple (consistency is soundness evaluated at `c`
itself — `cons_of_countermodel`).  Of the six pack clauses, the functor
satisfies exactly the four *forth-and-safety* ones:

* `atoms` (`trace_atoms`), `fall` (`trace_fall` — `⊥ ∈ cl` is packaged
  in `SubClosed`), `iforth` (`trace_iforth`, by persistence), and —
  the design validation of the `mfal` component — `mforth`
  (`trace_mforth`): promises propagate along `Rₘ` by transitivity, so
  descriptions are functorial for BOTH relations.

The two *back* clauses FAIL (`trace_kback_fails`,
`trace_mback_fails`, machine-checked on two-world instances): the
canonical model is more saturated than an arbitrary base, so canonical
moves need not be realised above a given world.  The functor is a lax
morphism, not a bisimulation — the pack relation for the discharges
must be finer than the trace graph.

**The realisability gfp.**  All six pack clauses use the relation only
POSITIVELY, so pack relations are closed under unions and there is a
LARGEST one: `Realises C K p dom := ⋃ {R | R is a pack relation}`
(`packRel_realises`).  Pack existence is thereby absorbed —
`DescPack.ofPackRel packRel_realises` is a pack once and for all — and
both residue discharges reduce to a single relational condition per
`(C, x)`: exhibit a closure triple with `◯φ ∈ fal` (∀-side,
`boxRowAmalgAll_of_realises`) resp. `◯φ ∈ val` (∃-side,
`boxRowAmalgEx_of_realises`) that is `Realises`-related to `x`.  On
finite instances `Realises` is computable by fixpoint iteration.

**Necessary conditions.**  A realised description agrees with its base
world on every p-free tracked formula (`realises_force_iff`,
via the graft's forcing lemma and bisimulation invariance); over
`canonFin cl` this pins the whole p-free part of any realisable triple
to the p-free part of the trace (`realises_val_iff`).  All
realisation freedom is in the p-relevant part — exactly the freedom
the redecoration spends.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp

/- Descriptions are classical objects: which closure formulas a world
of an ARBITRARY model forces is not decidable.  File-local classical
decidability keeps the `Finset` filters honest. -/
attribute [local instance] Classical.propDecidable

/-! ## Forcing finite disjunctions -/

/-- A forced `bigOr` forces some disjunct, or the world is fallible. -/
theorem force_bigOr_cases {C : ConstraintModel} {L : List PLLFormula} {w : C.W}
    (h : C.force w (bigOr L)) : (∃ τ ∈ L, C.force w τ) ∨ w ∈ C.F := by
  induction L with
  | nil => exact .inr h
  | cons τ L ih =>
      rcases h with hτ | hL
      · exact .inl ⟨τ, List.mem_cons_self .., hτ⟩
      · rcases ih hL with ⟨τ', hm, hf⟩ | hF
        · exact .inl ⟨τ', List.mem_cons_of_mem _ hm, hf⟩
        · exact .inr hF

/-! ## Consistency from a countermodel -/

/-- **Consistency from a countermodel**: a triple whose three
components are witnessed at a single world — `val` forced, `fal`
refuted, `mfal` refuted along the whole m-row — is consistent, by
soundness of the calculus evaluated at that world. -/
theorem cons_of_countermodel {T : FTheory} (C : ConstraintModel) (w : C.W)
    (hval : ∀ φ ∈ T.val, C.force w φ)
    (hfal : ∀ φ ∈ T.fal, ¬ C.force w φ)
    (hmfal : ∀ φ ∈ T.mfal, ∀ u, C.Rm w u → ¬ C.force u φ) : T.Cons := by
  intro Ds Ts hDs hTs hne hder
  obtain ⟨L, hL, ⟨d⟩⟩ := hder
  have hforce : C.force w (disjOf Ds Ts) :=
    soundness d C w (fun ψ hψ => hval ψ (Finset.mem_coe.mp (hL ψ hψ)))
  -- a forced `bigOr` over `fal`-members is absurd
  have noDs : ∀ (l : List PLLFormula), (∀ φ ∈ l, φ ∈ T.fal) → l ≠ [] →
      ¬ C.force w (bigOr l) := by
    intro l hl hlne hf
    rcases force_bigOr_cases hf with ⟨τ, hm, hτ⟩ | hF
    · exact hfal τ (hl τ hm) hτ
    · cases l with
      | nil => exact hlne rfl
      | cons τ l =>
          exact hfal τ (hl τ (List.mem_cons_self ..)) (C.force_of_fallible hF)
  -- a forced `◯bigOr` over `mfal`-members is absurd (evaluate at `w` itself)
  have noTs : ∀ (l : List PLLFormula), (∀ φ ∈ l, φ ∈ T.mfal) → l ≠ [] →
      ¬ C.force w ((bigOr l).somehow) := by
    intro l hl hlne hf
    obtain ⟨u, hmu, hu⟩ := hf w (C.refl_i w)
    rcases force_bigOr_cases hu with ⟨τ, hm, hτ⟩ | hF
    · exact hmfal τ (hl τ hm) u hmu hτ
    · cases l with
      | nil => exact hlne rfl
      | cons τ l =>
          exact hmfal τ (hl τ (List.mem_cons_self ..)) u hmu
            (C.force_of_fallible hF)
  cases Ds with
  | nil =>
      cases Ts with
      | nil => exact hne rfl
      | cons K Ts' =>
          rw [disjOf_nil_left] at hforce
          exact noTs _ (fun φ h => Finset.mem_coe.mp (hTs φ h)) (by simp) hforce
  | cons D Ds' =>
      cases Ts with
      | nil =>
          rw [disjOf_nil_right] at hforce
          exact noDs _ (fun φ h => Finset.mem_coe.mp (hDs φ h)) (by simp) hforce
      | cons K Ts' =>
          rw [disjOf_cons_cons] at hforce
          rcases hforce with h | h
          · exact noDs _ (fun φ hm => Finset.mem_coe.mp (hDs φ hm)) (by simp) h
          · exact noTs _ (fun φ hm => Finset.mem_coe.mp (hTs φ hm)) (by simp) h

/-- A triple with empty `fal` and `mfal` is consistent outright. -/
theorem cons_of_empty_falm {T : FTheory} (hf : T.fal = ∅) (hm : T.mfal = ∅) :
    T.Cons := by
  intro Ds Ts hDs hTs hne _
  cases Ds with
  | cons D Ds' =>
      have h := hDs D (List.mem_cons_self ..)
      rw [FTheory.toTheory_fal, hf] at h
      exact absurd (Finset.mem_coe.mp h) (Finset.notMem_empty D)
  | nil =>
      cases Ts with
      | nil => exact hne rfl
      | cons K Ts' =>
          have h := hTs K (List.mem_cons_self ..)
          rw [FTheory.toTheory_mfal, hm] at h
          exact absurd (Finset.mem_coe.mp h) (Finset.notMem_empty K)

/-! ## The descriptions functor -/

/-- The closure description (trace) of a world: which closure formulas
it forces / refutes / refutes along its whole m-row.  Classical
filters — every world of every model has a description. -/
noncomputable def traceT (C : ConstraintModel) (cl : Finset PLLFormula)
    (c : C.W) : FTheory :=
  ⟨cl.filter (fun φ => C.force c φ),
   cl.filter (fun φ => ¬ C.force c φ),
   cl.filter (fun φ => ∀ u, C.Rm c u → ¬ C.force u φ)⟩

theorem mem_traceT_val {C : ConstraintModel} {cl : Finset PLLFormula}
    {c : C.W} {φ : PLLFormula} :
    φ ∈ (traceT C cl c).val ↔ φ ∈ cl ∧ C.force c φ :=
  Finset.mem_filter

theorem mem_traceT_fal {C : ConstraintModel} {cl : Finset PLLFormula}
    {c : C.W} {φ : PLLFormula} :
    φ ∈ (traceT C cl c).fal ↔ φ ∈ cl ∧ ¬ C.force c φ :=
  Finset.mem_filter

theorem mem_traceT_mfal {C : ConstraintModel} {cl : Finset PLLFormula}
    {c : C.W} {φ : PLLFormula} :
    φ ∈ (traceT C cl c).mfal ↔ φ ∈ cl ∧ ∀ u, C.Rm c u → ¬ C.force u φ :=
  Finset.mem_filter

/-- The description of any world is closure-maximal: consistent by
`cons_of_countermodel` at the world itself, total by excluded middle. -/
theorem traceT_maxIn (C : ConstraintModel) (cl : Finset PLLFormula)
    (c : C.W) : MaxIn cl (traceT C cl c) := by
  refine ⟨cons_of_countermodel C c
      (fun φ h => (mem_traceT_val.mp h).2)
      (fun φ h => (mem_traceT_fal.mp h).2)
      (fun φ h => (mem_traceT_mfal.mp h).2),
    ⟨Finset.filter_subset _ _, Finset.filter_subset _ _,
      Finset.filter_subset _ _⟩, ?_⟩
  intro φ hφ
  by_cases h : C.force c φ
  · exact .inl (mem_traceT_val.mpr ⟨hφ, h⟩)
  · exact .inr (mem_traceT_fal.mpr ⟨hφ, h⟩)

/-- **The descriptions functor** into the finite canonical model. -/
noncomputable def trace (C : ConstraintModel) (cl : Finset PLLFormula)
    (c : C.W) : (canonFin cl).W :=
  ⟨traceT C cl c, traceT_maxIn C cl c⟩

/-! ## The pack clauses of the functor: four hold … -/

/-- The `atoms` clause holds for the functor (no `p`-exception even
needed): tracked atoms agree with the description. -/
theorem trace_atoms {C : ConstraintModel} {cl : Finset PLLFormula}
    {c : C.W} {q : String} (hq : PLLFormula.prop q ∈ cl) :
    (c ∈ C.V q ↔ trace C cl c ∈ (canonFin cl).V q) := by
  constructor
  · intro h
    exact .inr (mem_traceT_val.mpr ⟨hq, h⟩)
  · rintro (h | h)
    · exact absurd hq h
    · exact (mem_traceT_val.mp h).2

/-- The `fall` clause holds for the functor (the closure carries `⊥`). -/
theorem trace_fall {C : ConstraintModel} {cl : Finset PLLFormula}
    (hbot : PLLFormula.falsePLL ∈ cl) {c : C.W} :
    (c ∈ C.F ↔ trace C cl c ∈ (canonFin cl).F) := by
  constructor
  · intro h; exact mem_traceT_val.mpr ⟨hbot, h⟩
  · intro h; exact (mem_traceT_val.mp h).2

/-- The `iforth` clause holds for the functor, with the exact witness
(no fallible escape needed): persistence makes descriptions monotone
along `Rᵢ`. -/
theorem trace_iforth {C : ConstraintModel} {cl : Finset PLLFormula}
    {c v : C.W} (h : C.Ri c v) :
    (canonFin cl).Ri (trace C cl c) (trace C cl v) := by
  intro φ hφ
  obtain ⟨hcl, hf⟩ := mem_traceT_val.mp hφ
  exact mem_traceT_val.mpr ⟨hcl, C.force_hered h hf⟩

/-- **The m-forth clause holds for the functor** — the design
validation of the promise component: `val` moves by persistence
(`Rₘ ⊆ Rᵢ`), and `mfal` moves because promises made at `c` bind the
whole row of any m-successor, by transitivity of `Rₘ`. -/
theorem trace_mforth {C : ConstraintModel} {cl : Finset PLLFormula}
    {c u : C.W} (h : C.Rm c u) :
    (canonFin cl).Rm (trace C cl c) (trace C cl u) := by
  constructor
  · intro φ hφ
    obtain ⟨hcl, hf⟩ := mem_traceT_val.mp hφ
    exact mem_traceT_val.mpr ⟨hcl, C.force_hered (C.sub_mi h) hf⟩
  · intro φ hφ
    obtain ⟨hcl, hf⟩ := mem_traceT_mfal.mp hφ
    exact mem_traceT_mfal.mpr ⟨hcl, fun w hw => hf w (C.trans_m h hw)⟩

/-! ## … and two fail (machine-checked)

The canonical model is more saturated than an arbitrary base: a
canonical extension of a description need not be realised above the
described world.  The functor is a lax morphism, not a bisimulation. -/

/-- **The i-back clause FAILS for the functor**: over `oneW` (one
world, nothing forced) the description has a canonical extension
validating the atom `q`, which no world realises. -/
theorem trace_kback_fails :
    ∃ (C : ConstraintModel) (cl : Finset PLLFormula) (c : C.W)
      (T' : (canonFin cl).W),
      (canonFin cl).Ri (trace C cl c) T' ∧
      ∀ v, C.Ri c v → trace C cl v ≠ T' := by
  refine ⟨oneW, {.prop "q"}, (),
    ⟨⟨{.prop "q"}, ∅, ∅⟩,
      cons_of_empty_falm rfl rfl,
      ⟨subset_rfl, Finset.empty_subset _, Finset.empty_subset _⟩,
      fun φ hφ => .inl hφ⟩,
    Finset.filter_subset _ _, ?_⟩
  intro v _ hEq
  have hq : PLLFormula.prop "q" ∈ (trace oneW {.prop "q"} v).1.val := by
    rw [hEq]
    exact Finset.mem_singleton_self _
  exact (mem_traceT_val.mp hq).2

/-- Two-point chain: a bottom world that sees a `q`-validating top
along both relations. -/
private def chainQ : ConstraintModel where
  W := Bool
  Ri := fun a b => a = b ∨ a = false
  Rm := fun a b => a = b ∨ a = false
  F := ∅
  V := fun a => {b | a = "q" ∧ b = true}
  refl_i := fun _ => .inl rfl
  trans_i := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | rfl
    · exact h₂
    · exact .inr rfl
  refl_m := fun _ => .inl rfl
  trans_m := by
    intro a b c h₁ h₂
    rcases h₁ with rfl | rfl
    · exact h₂
    · exact .inr rfl
  sub_mi := fun h => h
  hered_F := fun _ hw => hw.elim
  hered_V := by
    intro a w v h hw
    rcases h with rfl | rfl
    · exact hw
    · exact absurd hw.2 (by simp)
  full_F := fun hw => hw.elim

/-- **The m-back clause FAILS for the functor** (fallible escape
included): the description of the bottom of `chainQ` has a canonical
m-extension promising `q`, but neither world of the chain honours that
promise (the top forces `q`; the bottom's row reaches the top). -/
theorem trace_mback_fails :
    ∃ (C : ConstraintModel) (cl : Finset PLLFormula) (c : C.W)
      (S : (canonFin cl).W),
      (canonFin cl).Rm (trace C cl c) S ∧
      ∀ u, C.Rm c u → ¬ (trace C cl u = S ∨ u ∈ C.F) := by
  refine ⟨chainQ, {.prop "q"}, false,
    ⟨⟨∅, {.prop "q"}, {.prop "q"}⟩,
      cons_of_countermodel oneW ()
        (fun φ h => absurd h (Finset.notMem_empty φ))
        (fun φ h hf => by
          rw [Finset.mem_singleton] at h
          subst h
          exact hf)
        (fun φ h u _ hf => by
          rw [Finset.mem_singleton] at h
          subst h
          exact hf),
      ⟨Finset.empty_subset _, subset_rfl, subset_rfl⟩,
      fun φ hφ => .inr hφ⟩,
    ⟨?_, Finset.filter_subset _ _⟩, ?_⟩
  · -- the bottom forces nothing in the closure, so its `val`-trace is empty
    intro φ hφ
    obtain ⟨hm, hf⟩ := mem_traceT_val.mp hφ
    rw [Finset.mem_singleton] at hm
    subst hm
    exact absurd hf.2 (by simp)
  · rintro u hu (hEq | hF)
    · cases u with
      | true =>
          -- the top forces `q`, but the target's `val` is empty
          have hq : PLLFormula.prop "q" ∈ (trace chainQ {.prop "q"} true).1.val :=
            mem_traceT_val.mpr ⟨Finset.mem_singleton_self _, rfl, rfl⟩
          rw [hEq] at hq
          exact absurd hq (Finset.notMem_empty _)
      | false =>
          -- the bottom cannot promise `q`: its row reaches the `q`-top
          have hq : PLLFormula.prop "q" ∈ (trace chainQ {.prop "q"} false).1.mfal := by
            rw [hEq]
            exact Finset.mem_singleton_self _
          obtain ⟨-, hall⟩ := mem_traceT_mfal.mp hq
          exact hall true (.inr rfl) ⟨rfl, rfl⟩
    · exact hF

/-! ## The realisability gfp

All six pack clauses use the relation only positively, so pack
relations are closed under unions: there is a LARGEST pack relation,
the greatest fixpoint of the clause operator.  Pack existence is
thereby absorbed into a single relational condition per pair. -/

/-- The six pack clauses, as a predicate on relations (the property of
being the `R` of some `DescPack`). -/
def PackRel (C K : ConstraintModel) (p : String) (dom : String → Prop)
    (R : C.W → K.W → Prop) : Prop :=
  (∀ {c k}, R c k → ∀ q, q ≠ p → dom q → (c ∈ C.V q ↔ k ∈ K.V q)) ∧
  (∀ {c k}, R c k → (c ∈ C.F ↔ k ∈ K.F)) ∧
  (∀ {c k}, R c k → ∀ {v}, C.Ri c v →
    (∃ k', K.Ri k k' ∧ R v k') ∨ v ∈ C.F) ∧
  (∀ {c k}, R c k → ∀ {k'}, K.Ri k k' → ∃ v, C.Ri c v ∧ R v k') ∧
  (∀ {c k}, R c k → ∀ {u}, C.Rm c u →
    ∃ s, K.Rm k s ∧ (R u s ∨ (u ∈ C.F ∧ s ∈ K.F))) ∧
  (∀ {c k}, R c k → ∀ {s}, K.Rm k s → ∃ u, C.Rm c u ∧ (R u s ∨ u ∈ C.F))

variable {C K : ConstraintModel} {p : String} {dom : String → Prop}

/-- Package a pack relation as a `DescPack`. -/
def DescPack.ofPackRel {R : C.W → K.W → Prop}
    (h : PackRel C K p dom R) : DescPack C K p dom where
  R := R
  atoms := h.1
  fall := h.2.1
  iforth := h.2.2.1
  kback := h.2.2.2.1
  mforth := h.2.2.2.2.1
  mback := h.2.2.2.2.2

/-- The relation of any `DescPack` is a pack relation. -/
theorem DescPack.packRel (P : DescPack C K p dom) :
    PackRel C K p dom P.R :=
  ⟨P.atoms, P.fall, P.iforth, P.kback, P.mforth, P.mback⟩

/-- **Description-realisability**: the union of all pack relations —
the greatest fixpoint of the clause operator.  `Realises c k` says
some pack pairs `c` with `k`. -/
def Realises (C K : ConstraintModel) (p : String) (dom : String → Prop)
    (c : C.W) (k : K.W) : Prop :=
  ∃ R : C.W → K.W → Prop, PackRel C K p dom R ∧ R c k

/-- Every pack relation is contained in `Realises` (largest-fixpoint
half). -/
theorem realises_of_packRel {R : C.W → K.W → Prop}
    (hR : PackRel C K p dom R) {c : C.W} {k : K.W} (h : R c k) :
    Realises C K p dom c k :=
  ⟨R, hR, h⟩

/-- **The union of packs is a pack**: `Realises` is itself a pack
relation (the clauses only use the relation positively, so witnesses
re-wrap). -/
theorem packRel_realises : PackRel C K p dom (Realises C K p dom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro c k ⟨R, hR, hck⟩ q hq hdq
    exact hR.1 hck q hq hdq
  · rintro c k ⟨R, hR, hck⟩
    exact hR.2.1 hck
  · rintro c k ⟨R, hR, hck⟩ v hv
    rcases hR.2.2.1 hck hv with ⟨k', hkk', hR'⟩ | hF
    · exact .inl ⟨k', hkk', R, hR, hR'⟩
    · exact .inr hF
  · rintro c k ⟨R, hR, hck⟩ k' hkk'
    obtain ⟨v, hcv, hR'⟩ := hR.2.2.2.1 hck hkk'
    exact ⟨v, hcv, R, hR, hR'⟩
  · rintro c k ⟨R, hR, hck⟩ u hu
    rcases hR.2.2.2.2.1 hck hu with ⟨s, hks, hR' | hFF⟩
    · exact ⟨s, hks, .inl ⟨R, hR, hR'⟩⟩
    · exact ⟨s, hks, .inr hFF⟩
  · rintro c k ⟨R, hR, hck⟩ s hks
    obtain ⟨u, hcu, hR' | hF⟩ := hR.2.2.2.2.2 hck hks
    · exact ⟨u, hcu, .inl ⟨R, hR, hR'⟩⟩
    · exact ⟨u, hcu, .inr hF⟩

/-- The realisability pack: the one `DescPack` that subsumes all
others. -/
def realisesPack (C K : ConstraintModel) (p : String)
    (dom : String → Prop) : DescPack C K p dom :=
  DescPack.ofPackRel packRel_realises

/-! ## The residue discharges, canonically targeted

With pack existence absorbed, each residue reduces to one membership
question per `(C, x)`: a closure triple with the right `◯φ`-component,
realised over `x`. -/

/-- **The ∀-residue reduces to realisability**: per `(C, x)` with a
`ψ`-refuting row, a closure triple with `◯φ ∈ fal` realised over `x`
discharges `BoxRowAmalgAll` (truth lemma + the realisability pack). -/
theorem boxRowAmalgAll_of_realises {p : String} {φ ψ : PLLFormula}
    {cl : Finset PLLFormula} (hcl : SubClosed cl)
    (hat : ∀ q ∈ φ.atoms, q ≠ p → PLLFormula.prop q ∈ cl)
    (hbox : φ.somehow ∈ cl)
    (h : ∀ (C : ConstraintModel) (x : C.W),
      (∀ y, C.Rm x y → ¬ C.force y ψ) →
      ∃ k : (canonFin cl).W,
        Realises C (canonFin cl) p (fun q => PLLFormula.prop q ∈ cl) x k ∧
        φ.somehow ∈ k.1.fal) :
    BoxRowAmalgAll p φ ψ := by
  refine boxRowAmalgAll_of_desc (dom := fun q => PLLFormula.prop q ∈ cl)
    hat ?_
  intro C x hrow
  obtain ⟨k, hRk, hfal⟩ := h C x hrow
  exact ⟨canonFin cl, realisesPack C (canonFin cl) p _, k, hRk,
    (FinComp.truth_lemma hcl _ hbox k).2 hfal⟩

/-- **The ∃-residue reduces to realisability** dually: a closure
triple with `◯φ ∈ val` realised over `w`. -/
theorem boxRowAmalgEx_of_realises {p : String} {φ ψ : PLLFormula}
    {cl : Finset PLLFormula} (hcl : SubClosed cl)
    (hat : ∀ q ∈ φ.atoms, q ≠ p → PLLFormula.prop q ∈ cl)
    (hbox : φ.somehow ∈ cl)
    (h : ∀ (C : ConstraintModel) (w : C.W),
      (∀ x, C.Ri w x → ∃ y, C.Rm x y ∧ C.force y ψ) →
      ∃ k : (canonFin cl).W,
        Realises C (canonFin cl) p (fun q => PLLFormula.prop q ∈ cl) w k ∧
        φ.somehow ∈ k.1.val) :
    BoxRowAmalgEx p φ ψ := by
  refine boxRowAmalgEx_of_desc (dom := fun q => PLLFormula.prop q ∈ cl)
    hat ?_
  intro C w hw
  obtain ⟨k, hRk, hval⟩ := h C w hw
  exact ⟨canonFin cl, realisesPack C (canonFin cl) p _, k, hRk,
    (FinComp.truth_lemma hcl _ hbox k).1 hval⟩

/-! ## Necessary conditions on realisable descriptions -/

/-- On the finite canonical model, forcing of closure formulas is
membership in `val` (both truth-lemma halves plus totality). -/
theorem canonFin_force_iff {cl : Finset PLLFormula} (hcl : SubClosed cl)
    {χ : PLLFormula} (hχ : χ ∈ cl) (T : (canonFin cl).W) :
    (canonFin cl).force T χ ↔ χ ∈ T.1.val := by
  constructor
  · intro hf
    rcases T.2.2.2 χ hχ with hv | hfal
    · exact hv
    · exact absurd hf ((FinComp.truth_lemma hcl χ hχ T).2 hfal)
  · exact (FinComp.truth_lemma hcl χ hχ T).1

/-- **Realised descriptions agree with their base world on p-free
tracked formulas**: through the graft, `c` and `k` force exactly the
same `θ` whenever `p ∉ θ.atoms` and `θ`'s atoms are tracked
(bisimulation invariance on the base side, the forcing lemma on the
fibre side). -/
theorem realises_force_iff {c : C.W} {k : K.W}
    (hR : Realises C K p dom c k) {θ : PLLFormula}
    (hpf : p ∉ θ.atoms) (hdom : ∀ q ∈ θ.atoms, dom q) :
    (C.force c θ ↔ K.force k θ) := by
  obtain ⟨R, hPR, hck⟩ := hR
  have h1 : C.force c θ ↔
      (descGraft (DescPack.ofPackRel hPR)).force (.inr ⟨(c, k), hck⟩) θ :=
    force_iff_of_bisim (descGraft_pbisim (DescPack.ofPackRel hPR))
      (fun a ha he => hpf (he ▸ ha)) rfl
  exact h1.trans (descGraft_force_iff (DescPack.ofPackRel hPR)
    (fun q hq _ => hdom q hq) c k hck)

/-- Over the finite canonical model this pins the whole p-free part of
any realisable triple: `χ ∈ val` iff the base world forces `χ` — the
p-free part of a realisable description IS the p-free trace.  All
realisation freedom is p-relevant. -/
theorem realises_val_iff {cl : Finset PLLFormula} (hcl : SubClosed cl)
    {c : C.W} {k : (canonFin cl).W}
    (hR : Realises C (canonFin cl) p (fun q => PLLFormula.prop q ∈ cl) c k)
    {χ : PLLFormula} (hχcl : χ ∈ cl) (hpf : p ∉ χ.atoms)
    (hatoms : ∀ q ∈ χ.atoms, PLLFormula.prop q ∈ cl) :
    (χ ∈ k.1.val ↔ C.force c χ) := by
  rw [← canonFin_force_iff hcl hχcl k]
  exact (realises_force_iff hR hpf hatoms).symm

/-! ## The pre-triple: the syntactic crux isolated

For the ∀-residue at `(C, x)` the canonical refuting triple must carry
the p-free description of `x` with `◯φ` falsified.  Its seed — the
**pre-triple** — is

  `⟨ {χ ∈ cl | χ p-free, x ⊩ χ},
     {◯φ} ∪ {χ ∈ cl | χ p-free, x ⊮ χ},
     {χ ∈ cl | χ p-free, the whole row of x refutes χ} ⟩`.

Consistency of this triple is a purely syntactic, per-instance
condition — no choice of `Ds ⊆ fal`, `Ts ⊆ mfal` has `⋁Ds ∨ ◯⋁Ts`
derivable from the p-free forced part.  Two theorems place it exactly:

* **necessity** (`preTripleAll_cons_of_residue`): if the residue holds
  at `(C, x)`, the p-variant world killing `◯φ` is itself a
  countermodel for the triple — p-free formulas transfer through the
  bisimulation, the row transfers through `mback`;
* **existence** (`preTripleAll_extend`): from consistency,
  `lindenbaum` produces a closure-maximal extension with the p-free
  part pinned, the promises untouched, and `◯φ ∈ fal`.

Realisability of that extension over `x` (`Realises`) is then the
exact remaining distance to the discharge
(`boxRowAmalgAll_of_realises`).  Dually for the ∃-side with `◯φ`
seeded into `val`. -/

/-- The ∀-side pre-triple over `x`: the p-free description of `x`,
seeded with `◯φ` falsified. -/
noncomputable def preTripleAll (C : ConstraintModel) (cl : Finset PLLFormula)
    (p : String) (x : C.W) (φ : PLLFormula) : FTheory :=
  ⟨cl.filter (fun χ => p ∉ χ.atoms ∧ C.force x χ),
   insert φ.somehow (cl.filter (fun χ => p ∉ χ.atoms ∧ ¬ C.force x χ)),
   cl.filter (fun χ => p ∉ χ.atoms ∧ ∀ u, C.Rm x u → ¬ C.force u χ)⟩

/-- The ∃-side pre-triple over `w`: the p-free description of `w`,
seeded with `◯φ` validated. -/
noncomputable def preTripleEx (C : ConstraintModel) (cl : Finset PLLFormula)
    (p : String) (w : C.W) (φ : PLLFormula) : FTheory :=
  ⟨insert φ.somehow (cl.filter (fun χ => p ∉ χ.atoms ∧ C.force w χ)),
   cl.filter (fun χ => p ∉ χ.atoms ∧ ¬ C.force w χ),
   cl.filter (fun χ => p ∉ χ.atoms ∧ ∀ u, C.Rm w u → ¬ C.force u χ)⟩

/-- **The syntactic crux is NECESSARY for the ∀-residue**: a p-variant
killing `◯φ` over `x` is a countermodel witnessing consistency of the
pre-triple — evaluate at the variant world; p-free content transfers
through the bisimulation, the row through `mback`. -/
theorem preTripleAll_cons_of_residue {p : String} {φ ψ : PLLFormula}
    (hAm : BoxRowAmalgAll p φ ψ) (cl : Finset PLLFormula)
    (C : ConstraintModel) (x : C.W)
    (hrow : ∀ y, C.Rm x y → ¬ C.force y ψ) :
    (preTripleAll C cl p x φ).Cons := by
  obtain ⟨N, B, x', hZ, hnb⟩ := hAm C x hrow
  refine cons_of_countermodel N x' ?_ ?_ ?_
  · intro χ hχ
    obtain ⟨-, hpf, hf⟩ := Finset.mem_filter.mp hχ
    exact (force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZ).mp hf
  · intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hnb
    · obtain ⟨-, hpf, hf⟩ := Finset.mem_filter.mp hχ
      exact fun hf' =>
        hf ((force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZ).mpr hf')
  · intro χ hχ u' hu' hf'
    obtain ⟨-, hpf, hall⟩ := Finset.mem_filter.mp hχ
    obtain ⟨u, hxu, hZu⟩ := B.mback hZ hu'
    exact hall u hxu
      ((force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZu).mpr hf')

/-- **The syntactic crux is NECESSARY for the ∃-residue** dually: a
p-variant forcing `◯φ` over `w` witnesses consistency of the ∃-side
pre-triple. -/
theorem preTripleEx_cons_of_residue {p : String} {φ ψ : PLLFormula}
    (hAm : BoxRowAmalgEx p φ ψ) (cl : Finset PLLFormula)
    (C : ConstraintModel) (w : C.W)
    (hw : ∀ x, C.Ri w x → ∃ y, C.Rm x y ∧ C.force y ψ) :
    (preTripleEx C cl p w φ).Cons := by
  obtain ⟨N, B, w', hZ, hb⟩ := hAm C w hw
  refine cons_of_countermodel N w' ?_ ?_ ?_
  · intro χ hχ
    rcases Finset.mem_insert.mp hχ with rfl | hχ
    · exact hb
    · obtain ⟨-, hpf, hf⟩ := Finset.mem_filter.mp hχ
      exact (force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZ).mp hf
  · intro χ hχ
    obtain ⟨-, hpf, hf⟩ := Finset.mem_filter.mp hχ
    exact fun hf' =>
      hf ((force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZ).mpr hf')
  · intro χ hχ u' hu' hf'
    obtain ⟨-, hpf, hall⟩ := Finset.mem_filter.mp hχ
    obtain ⟨u, hxu, hZu⟩ := B.mback hZ hu'
    exact hall u hxu
      ((force_iff_of_bisim B (fun a ha he => hpf (he ▸ ha)) hZu).mpr hf')

/-- **From consistency to the canonical triple**: `lindenbaum` extends
the consistent ∀-side pre-triple to a closure-maximal triple with
`◯φ ∈ fal`, the pre-triple below it, and the promises exactly
preserved. -/
theorem preTripleAll_extend {C : ConstraintModel} {cl : Finset PLLFormula}
    {p : String} {x : C.W} {φ : PLLFormula} (hbox : φ.somehow ∈ cl)
    (hcons : (preTripleAll C cl p x φ).Cons) :
    ∃ T : (canonFin cl).W,
      φ.somehow ∈ T.1.fal ∧
      (preTripleAll C cl p x φ).le T.1 ∧
      T.1.mfal = (preTripleAll C cl p x φ).mfal := by
  obtain ⟨T', hle, hM, hmf⟩ := lindenbaum hcons
    ⟨Finset.filter_subset _ _,
     insertSubset hbox (Finset.filter_subset _ _),
     Finset.filter_subset _ _⟩
  exact ⟨⟨T', hM⟩, hle.2.1 (Finset.mem_insert_self ..), hle, hmf⟩

/-- Dually: the consistent ∃-side pre-triple extends to a
closure-maximal triple with `◯φ ∈ val`. -/
theorem preTripleEx_extend {C : ConstraintModel} {cl : Finset PLLFormula}
    {p : String} {w : C.W} {φ : PLLFormula} (hbox : φ.somehow ∈ cl)
    (hcons : (preTripleEx C cl p w φ).Cons) :
    ∃ T : (canonFin cl).W,
      φ.somehow ∈ T.1.val ∧
      (preTripleEx C cl p w φ).le T.1 ∧
      T.1.mfal = (preTripleEx C cl p w φ).mfal := by
  obtain ⟨T', hle, hM, hmf⟩ := lindenbaum hcons
    ⟨insertSubset hbox (Finset.filter_subset _ _),
     Finset.filter_subset _ _,
     Finset.filter_subset _ _⟩
  exact ⟨⟨T', hM⟩, hle.1 (Finset.mem_insert_self ..), hle, hmf⟩

/-! ## Axiom audit (pinned) -/

/--
info: 'PLLND.SemUI.traceT_maxIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms traceT_maxIn

/--
info: 'PLLND.SemUI.trace_mforth' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_mforth

/--
info: 'PLLND.SemUI.trace_kback_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_kback_fails

/--
info: 'PLLND.SemUI.trace_mback_fails' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_mback_fails

/--
info: 'PLLND.SemUI.packRel_realises' does not depend on any axioms
-/
#guard_msgs in
#print axioms packRel_realises

/--
info: 'PLLND.SemUI.boxRowAmalgAll_of_realises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms boxRowAmalgAll_of_realises

/--
info: 'PLLND.SemUI.boxRowAmalgEx_of_realises' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms boxRowAmalgEx_of_realises

/--
info: 'PLLND.SemUI.realises_val_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms realises_val_iff

/--
info: 'PLLND.SemUI.preTripleAll_cons_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms preTripleAll_cons_of_residue

/--
info: 'PLLND.SemUI.preTripleEx_cons_of_residue' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms preTripleEx_cons_of_residue

/--
info: 'PLLND.SemUI.preTripleAll_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms preTripleAll_extend

/--
info: 'PLLND.SemUI.preTripleEx_extend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms preTripleEx_extend

end SemUI
end PLLND
