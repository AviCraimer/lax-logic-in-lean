import LaxLogic.PLLFinComp
import LaxLogic.PLLConfluentComplete

/-!
# `canonFinC` — the confluent finite canonical model (PCLL)  [WIP]

Branch `ui-confluence`.  The finite analogue of `PLLConfluentComplete`'s
`canonU`/`obInv`: worlds `{T : FTheory // MaxIn cl T}` as in `canonFin`,
but `Rₘ` is the `obInv` relation with the `◯◯ → ◯` collapse kept LOCAL
(Matthew's steer): we propagate the COLLAPSED box `boxOf χ` (= `χ` if `χ`
is already `◯ψ`, else `◯χ`).  Because `boxOf` always returns a `◯` and is
idempotent on `◯`s, transitivity closes with no `◯◯` ever entering `cl` —
so `cl` stays a finite subformula-closed set.
-/

open PLLFormula

namespace PLLND
namespace FinComp

open SetDeriv
open ConfluentU

variable {cl : Finset PLLFormula}

/-- The collapsed box: `◯χ` normalised by `◯◯ = ◯`.  Always a `◯`, and
idempotent (`boxOf (boxOf χ) = boxOf χ`). -/
def boxOf : PLLFormula → PLLFormula
  | .somehow ψ => .somehow ψ
  | φ => φ.somehow

@[simp] theorem boxOf_somehow (ψ : PLLFormula) :
    boxOf (.somehow ψ) = .somehow ψ := rfl

theorem boxOf_idem (χ : PLLFormula) : boxOf (boxOf χ) = boxOf χ := by
  cases χ <;> rfl

/-- The confluent backing: `v`'s closure-decisions come from an infinite
closed prime `DerivU` theory (a `canonU` world).  Exactly what a
cl-restriction of a `canonU` world carries; it is what makes `obInv`
prime, hence what makes the finite model confluent. -/
def Backed (cl : Finset PLLFormula) (v : FTheory) : Prop :=
  ∃ T : Set PLLFormula, SClosed T ∧ SPrime T ∧ ∀ φ ∈ cl, (φ ∈ v.val ↔ φ ∈ T)

/-- **Confluent finite worlds**: closure-maximal triples that carry a
backing.  (The backing is essential — over bare `MaxIn` worlds `obInv` is
inconsistent and the model is not confluent.) -/
abbrev WC (cl : Finset PLLFormula) := {v : FTheory // MaxIn cl v ∧ Backed cl v}

/-- The ◯-unit at the canonical level: `χ ∈ val` and `◯χ ∈ cl` give
`◯χ ∈ val`, by `laxIntro` and deductive closure. -/
theorem boxUnit {T : {T : FTheory // MaxIn cl T}} {χ : PLLFormula}
    (hbox : χ.somehow ∈ cl) (hχ : χ ∈ T.1.val) : χ.somehow ∈ T.1.val :=
  T.2.ded_closed hbox
    (setDeriv_coe_iff.mpr ⟨.laxIntro (.iden (Finset.mem_toList.mpr hχ))⟩)

/-- Confluent `Rₘ` (finite `obInv`, `◯◯`-collapsed): `val ⊆ val`, and
every collapsed box `boxOf χ ∈ cl` whose `χ` is validated at `U` is
validated at `T`. -/
def RmC (cl : Finset PLLFormula) (T U : {T : FTheory // MaxIn cl T}) : Prop :=
  T.1.val ⊆ U.1.val ∧
    ∀ χ : PLLFormula, boxOf χ ∈ cl → χ ∈ U.1.val → boxOf χ ∈ T.1.val

theorem RmC_refl (T : {T : FTheory // MaxIn cl T}) : RmC cl T T := by
  refine ⟨subset_rfl, fun χ hbox hχ => ?_⟩
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit hbox hχ
  | falsePLL => exact boxUnit hbox hχ
  | and a b => exact boxUnit hbox hχ
  | or a b => exact boxUnit hbox hχ
  | ifThen a b => exact boxUnit hbox hχ

theorem RmC_trans {T U V : {T : FTheory // MaxIn cl T}}
    (h : RmC cl T U) (h' : RmC cl U V) : RmC cl T V := by
  refine ⟨h.1.trans h'.1, fun χ hbox hχ => ?_⟩
  have hU : boxOf χ ∈ U.1.val := h'.2 χ hbox hχ
  have hbb : boxOf (boxOf χ) = boxOf χ := boxOf_idem χ
  have hT : boxOf (boxOf χ) ∈ T.1.val :=
    h.2 (boxOf χ) (by rw [hbb]; exact hbox) hU
  rwa [hbb] at hT

/-- **The confluent finite canonical model.**  As `canonFin`, but with
`Rₘ` the collapsed `obInv` relation `RmC`. -/
def canonFinC (cl : Finset PLLFormula) : ConstraintModel where
  W := WC cl
  Ri T T' := T.1.val ⊆ T'.1.val
  Rm a b := RmC cl ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
  F := {T | PLLFormula.falsePLL ∈ T.1.val}
  V a := {T | PLLFormula.prop a ∉ cl ∨ PLLFormula.prop a ∈ T.1.val}
  refl_i _ := subset_rfl
  trans_i h h' := h.trans h'
  refl_m a := RmC_refl ⟨a.1, a.2.1⟩
  trans_m h h' := RmC_trans h h'
  sub_mi h := h.1
  hered_F h hw := h hw
  hered_V h hw := hw.imp_right (fun h' => h h')
  full_F {a} {T} hw := by
    by_cases hcl : PLLFormula.prop a ∈ cl
    · exact .inr (T.2.1.ded_closed hcl (falso _ (of_mem (Finset.mem_coe.mpr hw))))
    · exact .inl hcl

-- audit: the confluent Rm + model are sorry-free
#print axioms RmC_trans
#print axioms canonFinC

/-! ## `obInvW` — the confluent canonical successor  [WIP]

Needs `cl` to be ◯-ADEQUATE: `boxOf φ ∈ cl` for every `φ ∈ cl`.  Finite
(`Sub ∪ {◯φ : φ ∈ Sub}`), because `boxOf` collapses `◯◯`. -/

/-- ◯-adequacy of the closure. -/
def OBoxAdeq (cl : Finset PLLFormula) : Prop := ∀ φ ∈ cl, boxOf φ ∈ cl

/-- The `obInv` world's underlying triple: `val = {ψ ∈ cl | boxOf ψ ∈
val(v)}`, its complement as `fal`, no promises. -/
def obInvFT (cl : Finset PLLFormula) (v : {T : FTheory // MaxIn cl T}) :
    FTheory :=
  ⟨cl.filter (fun ψ => boxOf ψ ∈ v.1.val),
   cl.filter (fun ψ => boxOf ψ ∉ v.1.val), ∅⟩

theorem obInvFT_val_iff {cl : Finset PLLFormula}
    {v : {T : FTheory // MaxIn cl T}} {ψ : PLLFormula} :
    ψ ∈ (obInvFT cl v).val ↔ ψ ∈ cl ∧ boxOf ψ ∈ v.1.val :=
  Finset.mem_filter

/-! ## The confluent backing — transferring `obInv_prime` to the finite level

The finite obInv is consistent only over worlds that arise as
cl-restrictions of `PLLConfluentComplete`'s infinite closed-prime
`DerivU` theories (`canonU` worlds).  We carry that backing explicitly and
transfer the two facts we need — `obInv_closed`/`obInv_prime` — verbatim.
No new Lindenbaum, no new completeness: `DerivU ⊇ LaxND`, so these worlds
still satisfy the ambient `MaxIn`. -/

/-- `LaxND`-derivability from a set implies `DerivU`-derivability (`SDeriv`). -/
theorem sderiv_of_setderiv {Γ : Set PLLFormula} {φ : PLLFormula}
    (h : Γ ⊩ φ) : SDeriv Γ φ := by
  obtain ⟨L, hL, ⟨p⟩⟩ := h
  exact ⟨L, hL, DerivU.of_nd p⟩

/-- In a deductively closed (`SClosed`) set the collapsed and raw boxes
agree: `boxOf ψ ∈ T ↔ ◯ψ ∈ T` (the box case is `◯R`/`◯M`). -/
theorem boxOf_mem_iff {T : Set PLLFormula} (hc : SClosed T) (ψ : PLLFormula) :
    boxOf ψ ∈ T ↔ PLLFormula.somehow ψ ∈ T := by
  cases ψ with
  | somehow ψ' =>
      simp only [boxOf_somehow]
      constructor
      · intro h; exact hc _ (SDeriv.unit (SDeriv.of_mem h))
      · intro h
        -- `◯◯ψ' ⊃ ◯ψ'` inline (the `canonU.trans_m` term)
        have hM : LaxND ([] : List PLLFormula)
            ((somehow (somehow ψ')).ifThen (somehow ψ')) :=
          .impIntro (.laxElim (φ := somehow ψ') (.iden (by simp)) (.iden (by simp)))
        exact hc _ (SDeriv.mp ⟨[], by simp, DerivU.of_nd hM⟩ (SDeriv.of_mem h))
  | prop a => exact Iff.rfl
  | falsePLL => exact Iff.rfl
  | and a b => exact Iff.rfl
  | or a b => exact Iff.rfl
  | ifThen a b => exact Iff.rfl

/-- Primeness over a finite disjunction: a closed prime set containing
`⋁Ds` (nonempty) contains one of the `Ds` (the `⊥`-tail is absorbed by
closure). -/
theorem sprime_bigOr {U : Set PLLFormula} (hc : SClosed U) (hp : SPrime U) :
    ∀ (Ds : List PLLFormula), bigOr Ds ∈ U → Ds ≠ [] → ∃ D ∈ Ds, D ∈ U := by
  intro Ds
  induction Ds with
  | nil => intro _ hne; exact absurd rfl hne
  | cons D Ds' ih =>
      intro h _
      rcases hp D (bigOr Ds') h with hD | hrest
      · exact ⟨D, List.mem_cons_self .., hD⟩
      · by_cases hDs' : Ds' = []
        · subst hDs'
          have hDU : D ∈ U := hc D ⟨[PLLFormula.falsePLL], by simpa [bigOr] using hrest,
            DerivU.of_nd (.falsoElim D (.iden (by simp)))⟩
          exact ⟨D, List.mem_cons_self .., hDU⟩
        · obtain ⟨D', hD'mem, hD'U⟩ := ih hrest hDs'
          exact ⟨D', List.mem_cons_of_mem _ hD'mem, hD'U⟩

/-- **The heart, now TRUE.**  Over a ◯-adequate closure and a backed
world, the finite obInv successor is consistent — because its `val` is a
subset of the (prime, by `obInv_prime`) infinite `obInv T`, so any derived
disjunction of `fal`-formulas would put a `fal`-formula's box back in
`val v`.  Pure transfer of `obInv_closed`/`obInv_prime`. -/
theorem obInvFT_cons_of_backed {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    {v : {T : FTheory // MaxIn cl T}} (hback : Backed cl v.1) :
    (obInvFT cl v).Cons := by
  obtain ⟨T, hTc, hTp, hTmatch⟩ := hback
  -- `val (obInvFT cl v) ⊆ obInv T`
  have hsub : (↑(obInvFT cl v).val : Set PLLFormula) ⊆ obInv T := by
    intro ψ hψ
    obtain ⟨hψcl, hbv⟩ := obInvFT_val_iff.mp (Finset.mem_coe.mp hψ)
    show PLLFormula.somehow ψ ∈ T
    exact (boxOf_mem_iff hTc ψ).mp ((hTmatch _ (hadeq _ hψcl)).mp hbv)
  intro Ds Ts hDs hTs hne hder
  have hTsnil : Ts = [] := by
    cases Ts with
    | nil => rfl
    | cons K Ts => exact absurd (hTs K (List.mem_cons_self ..)) (by simp [obInvFT])
  subst hTsnil
  rw [disjOf_nil_right, FTheory.toTheory_val] at hder
  have hne' : Ds ≠ [] := by simpa using hne
  have hbig : bigOr Ds ∈ obInv T :=
    obInv_closed hTc (bigOr Ds) (SDeriv.mono hsub (sderiv_of_setderiv hder))
  obtain ⟨D, hDmem, hDobinv⟩ :=
    sprime_bigOr (obInv_closed hTc) (obInv_prime hTc hTp) Ds hbig hne'
  have hDfal := hDs D hDmem
  simp only [FTheory.toTheory_fal, Finset.mem_coe, obInvFT, Finset.mem_filter] at hDfal
  obtain ⟨hDcl, hDbv⟩ := hDfal
  have hbT : boxOf D ∈ T := (boxOf_mem_iff hTc D).mpr hDobinv
  exact hDbv ((hTmatch _ (hadeq _ hDcl)).mpr hbT)

-- audit: the backed heart is kernel-clean (pure transfer of obInv_prime)
#print axioms obInvFT_cons_of_backed

/-- Closure-maximality of the obInv successor, over a **backed** world:
`Cons` is `obInvFT_cons_of_backed`; `InCl`/totality are structural. -/
theorem obInvFT_maxIn {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (v : {T : FTheory // MaxIn cl T}) (hb : Backed cl v.1) :
    MaxIn cl (obInvFT cl v) := by
  refine ⟨obInvFT_cons_of_backed hadeq hb,
    ⟨Finset.filter_subset _ _, Finset.filter_subset _ _,
      Finset.empty_subset _⟩, ?_⟩
  intro φ hφ
  by_cases h : boxOf φ ∈ v.1.val
  · exact .inl (Finset.mem_filter.mpr ⟨hφ, h⟩)
  · exact .inr (Finset.mem_filter.mpr ⟨hφ, h⟩)

/-- The obInv successor is itself backed: by `obInv T` (prime via
`obInv_prime`), which matches `obInvFT`'s `val` on `cl` (`boxOf_mem_iff`).
So `obInvW` maps confluent worlds to confluent worlds. -/
theorem obInvFT_backed {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl)
    (v : {T : FTheory // MaxIn cl T}) (hb : Backed cl v.1) :
    Backed cl (obInvFT cl v) := by
  obtain ⟨T, hTc, hTp, hTmatch⟩ := hb
  refine ⟨obInv T, obInv_closed hTc, obInv_prime hTc hTp, ?_⟩
  intro φ hφcl
  rw [obInvFT_val_iff]
  constructor
  · rintro ⟨-, hbv⟩
    show PLLFormula.somehow φ ∈ T
    exact (boxOf_mem_iff hTc φ).mp ((hTmatch _ (hadeq _ hφcl)).mp hbv)
  · intro hoi
    refine ⟨hφcl, (hTmatch _ (hadeq _ hφcl)).mpr ((boxOf_mem_iff hTc φ).mpr hoi)⟩

/-- **The confluent canonical successor** `obInvW : WC cl → WC cl`. -/
def obInvW {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl) (w : WC cl) : WC cl :=
  ⟨obInvFT cl ⟨w.1, w.2.1⟩,
   obInvFT_maxIn hadeq ⟨w.1, w.2.1⟩ w.2.2,
   obInvFT_backed hadeq ⟨w.1, w.2.1⟩ w.2.2⟩

/-- **The confluent row-witness**: `w Rₘ obInvW w` in `canonFinC`.  The
`val`-inclusion uses ◯-adequacy + `boxUnit` for non-boxes and
`boxOf`-fixity for boxes; the `obInv` clause is definitional. -/
theorem rm_obInvW {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl) (w : WC cl) :
    (canonFinC cl).Rm w (obInvW hadeq w) := by
  refine ⟨fun χ hχ => ?_, fun χ _ hχ => (Finset.mem_filter.mp hχ).2⟩
  have hχcl : χ ∈ cl := w.2.1.2.1.1 hχ
  refine Finset.mem_filter.mpr ⟨hχcl, ?_⟩
  cases χ with
  | somehow ψ => exact hχ
  | prop a => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | falsePLL => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | and a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | or a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ
  | ifThen a b => exact boxUnit (T := ⟨w.1, w.2.1⟩) (hadeq _ hχcl) hχ

-- audit: the confluent successor is kernel-clean
#print axioms obInvW
#print axioms rm_obInvW

/-! ## Confluence, and the `restr` constructor for backed successors -/

/-- **`canonFinC` is mutually confluent** — the confluence square is
witnessed by `obInvW v` (port of `canonU_confluent`). -/
theorem canonFinC_confluent {cl : Finset PLLFormula} (hadeq : OBoxAdeq cl) :
    MutuallyConfluent (canonFinC cl) := by
  intro x w v hm hi
  refine ⟨obInvW hadeq v, fun ψ hψ => ?_, rm_obInvW hadeq v⟩
  have hψcl : ψ ∈ cl := w.2.1.2.1.1 hψ
  exact Finset.mem_filter.mpr ⟨hψcl, hi (hm.2 ψ (hadeq _ hψcl) hψ)⟩

/-- Consistency of any cl-restriction of a closed prime `DerivU` theory:
`val ⊆ T`, `mfal = ∅`, `fal ∩ T = ∅`.  (The general form of the heart.) -/
theorem cons_of_sub_prime {T : Set PLLFormula}
    (hTc : SClosed T) (hTp : SPrime T) {v : FTheory}
    (hsub : (↑v.val : Set PLLFormula) ⊆ T) (hmf : v.mfal = ∅)
    (hfal : ∀ φ ∈ v.fal, φ ∉ T) : v.Cons := by
  intro Ds Ts hDs hTs hne hder
  have hTsnil : Ts = [] := by
    cases Ts with
    | nil => rfl
    | cons K Ts =>
        have hK := hTs K (List.mem_cons_self ..)
        rw [FTheory.toTheory_mfal, hmf] at hK
        exact absurd hK (by simp)
  subst hTsnil
  rw [disjOf_nil_right, FTheory.toTheory_val] at hder
  have hne' : Ds ≠ [] := by simpa using hne
  have hbig : bigOr Ds ∈ T := hTc _ (SDeriv.mono hsub (sderiv_of_setderiv hder))
  obtain ⟨D, hDmem, hDT⟩ := sprime_bigOr hTc hTp Ds hbig hne'
  have hDfal : D ∈ v.fal := by
    have hD := hDs D hDmem
    rwa [FTheory.toTheory_fal, Finset.mem_coe] at hD
  exact hfal D hDfal hDT

open Classical in
/-- The cl-restriction of an infinite theory, as a triple (`mfal = ∅`). -/
noncomputable def restrFT (cl : Finset PLLFormula) (T : Set PLLFormula) : FTheory :=
  ⟨cl.filter (· ∈ T), cl.filter (· ∉ T), ∅⟩

open Classical in
theorem restrFT_val_iff {cl : Finset PLLFormula} {T : Set PLLFormula}
    {φ : PLLFormula} : φ ∈ (restrFT cl T).val ↔ φ ∈ cl ∧ φ ∈ T := by
  simp only [restrFT, Finset.mem_filter]

open Classical in
theorem restr_backed {cl : Finset PLLFormula} {T : Set PLLFormula}
    (hTc : SClosed T) (hTp : SPrime T) : Backed cl (restrFT cl T) := by
  refine ⟨T, hTc, hTp, fun φ hφ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact ((restrFT_val_iff (cl := cl) (T := T)).mp h).2
  · exact (restrFT_val_iff (cl := cl) (T := T)).mpr ⟨hφ, h⟩

open Classical in
theorem restr_maxIn {cl : Finset PLLFormula} {T : Set PLLFormula}
    (hTc : SClosed T) (hTp : SPrime T) : MaxIn cl (restrFT cl T) := by
  refine ⟨cons_of_sub_prime hTc hTp (fun ψ hψ => ?_) rfl (fun ψ hψ => ?_),
    ⟨Finset.filter_subset _ _, Finset.filter_subset _ _, Finset.empty_subset _⟩,
    fun φ hφ => ?_⟩
  · exact (restrFT_val_iff.mp (Finset.mem_coe.mp hψ)).2
  · exact (Finset.mem_filter.mp hψ).2
  · by_cases h : φ ∈ T
    · exact .inl (restrFT_val_iff.mpr ⟨hφ, h⟩)
    · exact .inr (Finset.mem_filter.mpr ⟨hφ, h⟩)

/-- **Backed world from a closed prime theory** — the cl-restriction as a
`WC cl`.  This is where `prime_extension` re-enters at the finite level. -/
noncomputable def restr (cl : Finset PLLFormula) {T : Set PLLFormula}
    (hTc : SClosed T) (hTp : SPrime T) : WC cl :=
  ⟨restrFT cl T, restr_maxIn hTc hTp, restr_backed hTc hTp⟩

#print axioms canonFinC_confluent
#print axioms restr

/-! ## Box/val collapse helpers and the backed ⊃-successor -/

/-- `◯φ ∈ val ⇒ boxOf φ ∈ val` (deductive closure + `◯◯ → ◯`). -/
theorem boxOf_mem_of_somehow_mem {cl : Finset PLLFormula}
    {w : {T : FTheory // MaxIn cl T}} {φ : PLLFormula} (hbcl : boxOf φ ∈ cl)
    (h : PLLFormula.somehow φ ∈ w.1.val) : boxOf φ ∈ w.1.val := by
  cases φ with
  | somehow φ' =>
      simp only [boxOf_somehow]
      refine w.2.ded_closed (by simpa using hbcl) ?_
      exact setDeriv_coe_iff.mpr
        ⟨LaxND.laxElim (.iden (Finset.mem_toList.mpr h)) (.iden (.head _))⟩
  | prop a => exact h
  | falsePLL => exact h
  | and a b => exact h
  | or a b => exact h
  | ifThen a b => exact h

/-- `boxOf φ ∈ val ⇒ ◯φ ∈ val` (given `◯φ ∈ cl`; the box case is `boxUnit`
on the collapsed box). -/
theorem somehow_mem_of_boxOf_mem {cl : Finset PLLFormula}
    {w : {T : FTheory // MaxIn cl T}} {φ : PLLFormula}
    (hφcl : PLLFormula.somehow φ ∈ cl) (h : boxOf φ ∈ w.1.val) :
    PLLFormula.somehow φ ∈ w.1.val := by
  cases φ with
  | somehow φ' => simp only [boxOf_somehow] at h; exact boxUnit hφcl h
  | prop a => exact h
  | falsePLL => exact h
  | and a b => exact h
  | or a b => exact h
  | ifThen a b => exact h

/-- **The backed ⊃-successor**: a falsified implication `φ ⊃ ψ ∈ fal w`
yields a backed `Rᵢ`-successor forcing `φ` and refuting `ψ`.  Built by
`prime_extension` on `insert φ T` (backing) — *not* the `LaxND`
`lindenbaum`, which would break backing. -/
theorem imp_fal_successor {cl : Finset PLLFormula} (w : WC cl)
    {φ ψ : PLLFormula} (hφ₁ : φ ∈ cl) (hψ₁ : ψ ∈ cl)
    (hf : φ.ifThen ψ ∈ w.1.fal) :
    ∃ w' : WC cl, w.1.val ⊆ w'.1.val ∧ φ ∈ w'.1.val ∧ ψ ∈ w'.1.fal := by
  obtain ⟨T, hTc, hTp, hTmatch⟩ := w.2.2
  have hφψcl : φ.ifThen ψ ∈ cl := w.2.1.2.1.2.1 hf
  have hnotval : φ.ifThen ψ ∉ w.1.val := fun hv => w.2.1.not_mem_fal_of_mem_val hv hf
  have hnotT : φ.ifThen ψ ∉ T := fun hT => hnotval ((hTmatch _ hφψcl).mpr hT)
  have hnd : ¬ SDeriv (insert φ T) ψ := fun hd => hnotT (hTc _ (SDeriv.deduction hd))
  obtain ⟨T', hsub', hψ'⟩ := prime_extension hnd
  refine ⟨restr cl T'.2.1 T'.2.2, fun χ hχ => ?_, ?_, ?_⟩
  · have hχcl : χ ∈ cl := w.2.1.2.1.1 hχ
    exact (restrFT_val_iff (cl := cl) (T := T'.1)).mpr
      ⟨hχcl, hsub' (Set.mem_insert_of_mem _ ((hTmatch _ hχcl).mp hχ))⟩
  · exact (restrFT_val_iff (cl := cl) (T := T'.1)).mpr ⟨hφ₁, hsub' (Set.mem_insert _ _)⟩
  · show ψ ∈ (restrFT cl T'.1).fal
    simp only [restrFT, Finset.mem_filter]
    exact ⟨hψ₁, hψ'⟩

#print axioms imp_fal_successor

/-! ## The truth lemma for `canonFinC` -/

/-- **Truth lemma** for the confluent finite canonical model: on a
◯-adequate subformula-closed closure, `val` forces and `fal` refutes.
The ⊃-backward step uses the backed `imp_fal_successor`; the ◯-case is the
`obInvW` bare-possibility (confluence). -/
theorem truth_lemmaC {cl : Finset PLLFormula} (hcl : SubClosed cl)
    (hadeq : OBoxAdeq cl) :
    ∀ (φ : PLLFormula), φ ∈ cl → ∀ w : WC cl,
      (φ ∈ w.1.val → (canonFinC cl).force w φ) ∧
        (φ ∈ w.1.fal → ¬ (canonFinC cl).force w φ) := by
  intro φ
  induction φ with
  | prop a =>
      intro hφ w
      refine ⟨fun h => .inr h, fun h hf => ?_⟩
      rcases hf with hout | hv
      · exact hout (w.2.1.2.1.2.1 h)
      · exact w.2.1.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hv))
  | falsePLL =>
      intro hφ w
      refine ⟨fun h => h, fun h hf => ?_⟩
      exact w.2.1.not_fal_deriv h (of_mem (Finset.mem_coe.mpr hf))
  | and φ ψ ihφ ihψ =>
      intro hφ w
      have hφ₁ := hcl.and_left hφ
      have hψ₁ := hcl.and_right hφ
      constructor
      · intro h
        have h₁ : φ ∈ w.1.val := w.2.1.ded_closed hφ₁
          (map (fun p => .andElim1 p) (of_mem (Finset.mem_coe.mpr h)))
        have h₂ : ψ ∈ w.1.val := w.2.1.ded_closed hψ₁
          (map (fun p => .andElim2 p) (of_mem (Finset.mem_coe.mpr h)))
        exact ⟨(ihφ hφ₁ w).1 h₁, (ihψ hψ₁ w).1 h₂⟩
      · intro h hf
        rcases w.2.1.fal_and hcl h with h' | h'
        · exact (ihφ hφ₁ w).2 h' hf.1
        · exact (ihψ hψ₁ w).2 h' hf.2
  | or φ ψ ihφ ihψ =>
      intro hφ w
      have hφ₁ := hcl.or_left hφ
      have hψ₁ := hcl.or_right hφ
      constructor
      · intro h
        rcases w.2.1.or_mem hcl h with h' | h'
        · exact .inl ((ihφ hφ₁ w).1 h')
        · exact .inr ((ihψ hψ₁ w).1 h')
      · intro h hf
        obtain ⟨h₁, h₂⟩ := w.2.1.fal_or hcl h
        rcases hf with hf | hf
        · exact (ihφ hφ₁ w).2 h₁ hf
        · exact (ihψ hψ₁ w).2 h₂ hf
  | ifThen φ ψ ihφ ihψ =>
      intro hφ w
      have hφ₁ := hcl.imp_left hφ
      have hψ₁ := hcl.imp_right hφ
      constructor
      · intro h w' hle hfφ
        rcases w'.2.1.imp_mem hcl (hle h) with h'' | h''
        · exact absurd hfφ ((ihφ hφ₁ w').2 h'')
        · exact (ihψ hψ₁ w').1 h''
      · intro h hf
        obtain ⟨w', hle, hfφ', hffψ'⟩ := imp_fal_successor w hφ₁ hψ₁ h
        exact (ihψ hψ₁ w').2 hffψ' (hf w' hle ((ihφ hφ₁ w').1 hfφ'))
  | somehow φ ih =>
      intro hφ w
      have hφ₁ : φ ∈ cl := hcl.lax hφ
      constructor
      · intro h
        rw [force_somehow_iff_of_confluent (canonFinC_confluent hadeq)]
        refine ⟨obInvW hadeq w, rm_obInvW hadeq w, (ih hφ₁ (obInvW hadeq w)).1 ?_⟩
        exact Finset.mem_filter.mpr
          ⟨hφ₁, boxOf_mem_of_somehow_mem (w := ⟨w.1, w.2.1⟩) (hadeq _ hφ₁) h⟩
      · intro h hff
        rw [force_somehow_iff_of_confluent (canonFinC_confluent hadeq)] at hff
        obtain ⟨u, hwu, hfu⟩ := hff
        have hφu : φ ∈ u.1.val := by
          rcases u.2.1.2.2 φ hφ₁ with hv | hfl
          · exact hv
          · exact absurd hfu ((ih hφ₁ u).2 hfl)
        have hbw : boxOf φ ∈ w.1.val := hwu.2 φ (hadeq _ hφ₁) hφu
        exact w.2.1.not_fal_deriv h
          (of_mem (Finset.mem_coe.mpr
            (somehow_mem_of_boxOf_mem (w := ⟨w.1, w.2.1⟩) hφ hbw)))

#print axioms truth_lemmaC

end FinComp
end PLLND
