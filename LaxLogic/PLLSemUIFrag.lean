import LaxLogic.PLLSemUILayered

/-!
# Fragment finiteness up to interderivability

Proof of `frag_reps_exist'`: for every finite atom set `V` and rank
bound `r`, there is a FINITE LIST of formulas of crank ≤ r over `V`
such that every formula of crank ≤ r over `V` is interderivable (in
`LaxND`) with a member of the list.  This is the Litak–Visser Thm 4.5
analogue for PLL, with `crank` the ◯-costs-2 complexity of
`PLLSemUILayered.lean`.

The construction is syntactic: rank-stratified component lists
(`comps`) — atoms and ⊥ at rank 0, implications between canonical
DNFs one rank up, boxes of canonical DNFs two ranks up — and a
normal-form lemma (`toDNF`) putting every formula into a disjunction
of conjunctions of components, canonicalised (`canonicalise`) into a
member of the fixed list `dnfL (comps V r)` by filtering through the
canonical enumeration.
-/

open PLLFormula

namespace PLLND
namespace SemUI

/-! ## Derivability, `Prop`-level -/

/-- `Deriv Γ φ`: the natural-deduction sequent `Γ ⊢ φ` is derivable. -/
def Deriv (Γ : List PLLFormula) (φ : PLLFormula) : Prop := Nonempty (LaxND Γ φ)

namespace Deriv

theorem iden {Γ : List PLLFormula} {φ : PLLFormula} (h : φ ∈ Γ) : Deriv Γ φ :=
  ⟨.iden h⟩

theorem rename {Γ Γ' : List PLLFormula} {φ : PLLFormula}
    (H : ∀ χ ∈ Γ, χ ∈ Γ') : Deriv Γ φ → Deriv Γ' φ
  | ⟨p⟩ => ⟨p.rename H⟩

theorem falsoElim {Γ : List PLLFormula} (φ : PLLFormula) :
    Deriv Γ .falsePLL → Deriv Γ φ
  | ⟨p⟩ => ⟨.falsoElim φ p⟩

theorem impIntro {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv (φ :: Γ) ψ → Deriv Γ (φ.ifThen ψ)
  | ⟨p⟩ => ⟨.impIntro p⟩

theorem impElim {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.ifThen ψ) → Deriv Γ φ → Deriv Γ ψ
  | ⟨p⟩, ⟨q⟩ => ⟨.impElim p q⟩

theorem andIntro {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ.and ψ)
  | ⟨p⟩, ⟨q⟩ => ⟨.andIntro p q⟩

theorem andElim1 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.and ψ) → Deriv Γ φ
  | ⟨p⟩ => ⟨.andElim1 p⟩

theorem andElim2 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ (φ.and ψ) → Deriv Γ ψ
  | ⟨p⟩ => ⟨.andElim2 p⟩

theorem orIntro1 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ φ → Deriv Γ (φ.or ψ)
  | ⟨p⟩ => ⟨.orIntro1 p⟩

theorem orIntro2 {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv Γ ψ → Deriv Γ (φ.or ψ)
  | ⟨p⟩ => ⟨.orIntro2 p⟩

theorem orElim {Γ : List PLLFormula} {φ ψ χ : PLLFormula} :
    Deriv Γ (φ.or ψ) → Deriv (φ :: Γ) χ → Deriv (ψ :: Γ) χ → Deriv Γ χ
  | ⟨p⟩, ⟨q₁⟩, ⟨q₂⟩ => ⟨.orElim p q₁ q₂⟩

theorem somehowMono {Γ : List PLLFormula} {φ ψ : PLLFormula} :
    Deriv (φ :: Γ) ψ → Deriv (.somehow φ :: Γ) (.somehow ψ)
  | ⟨p⟩ => ⟨LaxND.somehowMono p⟩

/-- Weaken a one-hypothesis derivation to any context carrying that
hypothesis at the head. -/
theorem toHead {φ ψ : PLLFormula} {Γ : List PLLFormula} (h : Deriv [φ] ψ) :
    Deriv (φ :: Γ) ψ :=
  h.rename fun χ hχ => by
    simp only [List.mem_singleton] at hχ; subst hχ; exact List.mem_cons_self ..

/-- Cut against a single hypothesis. -/
theorem cutHead {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (p : Deriv Γ φ) (q : Deriv [φ] ψ) : Deriv Γ ψ :=
  impElim (impIntro q.toHead) p

end Deriv

/-! ## Interderivability -/

/-- Interderivability: each formula proves the other from a single
hypothesis. -/
def Interd (φ ψ : PLLFormula) : Prop :=
  Nonempty (LaxND [φ] ψ) ∧ Nonempty (LaxND [ψ] φ)

namespace Interd

theorem refl (φ : PLLFormula) : Interd φ φ :=
  ⟨⟨.iden (.head _)⟩, ⟨.iden (.head _)⟩⟩

theorem symm {φ ψ : PLLFormula} (h : Interd φ ψ) : Interd ψ φ := ⟨h.2, h.1⟩

theorem trans {φ ψ χ : PLLFormula} (h₁ : Interd φ ψ) (h₂ : Interd ψ χ) :
    Interd φ χ :=
  ⟨Deriv.cutHead h₁.1 h₂.1, Deriv.cutHead h₂.2 h₁.2⟩

theorem and_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.and ψ) (φ'.and ψ') :=
  ⟨Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h₁.1)
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h₂.1),
   Deriv.andIntro (Deriv.cutHead (Deriv.andElim1 (Deriv.iden (.head _))) h₁.2)
      (Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _))) h₂.2)⟩

theorem or_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.or ψ) (φ'.or ψ') :=
  ⟨Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.toHead h₁.1)) (Deriv.orIntro2 (Deriv.toHead h₂.1)),
   Deriv.orElim (Deriv.iden (.head _))
      (Deriv.orIntro1 (Deriv.toHead h₁.2)) (Deriv.orIntro2 (Deriv.toHead h₂.2))⟩

theorem imp_congr {φ φ' ψ ψ' : PLLFormula} (h₁ : Interd φ φ') (h₂ : Interd ψ ψ') :
    Interd (φ.ifThen ψ) (φ'.ifThen ψ') := by
  refine ⟨?_, ?_⟩
  · refine Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) ?_) h₂.1)
    exact Deriv.cutHead (Deriv.iden (.head _)) h₁.2
  · refine Deriv.impIntro (Deriv.cutHead
      (Deriv.impElim (Deriv.iden (.tail _ (.head _))) ?_) h₂.2)
    exact Deriv.cutHead (Deriv.iden (.head _)) h₁.1

theorem box_congr {φ φ' : PLLFormula} (h : Interd φ φ') :
    Interd (PLLFormula.somehow φ) (PLLFormula.somehow φ') :=
  ⟨Deriv.somehowMono h.1, Deriv.somehowMono h.2⟩

end Interd

/-! ## Finite conjunctions -/

/-- Finite conjunction; the singleton case avoids a trailing `⊤`
(`truePLL = ⊥ ⊃ ⊥` has crank 1), so a NONEMPTY conjunction's crank is
the maximum of its members'. -/
def bigAnd : List PLLFormula → PLLFormula
  | [] => truePLL
  | [φ] => φ
  | φ :: ψ :: l => φ.and (bigAnd (ψ :: l))

@[simp] theorem bigAnd_nil : bigAnd [] = truePLL := rfl
@[simp] theorem bigAnd_singleton (φ : PLLFormula) : bigAnd [φ] = φ := rfl
@[simp] theorem bigAnd_cons₂ (φ ψ : PLLFormula) (l : List PLLFormula) :
    bigAnd (φ :: ψ :: l) = φ.and (bigAnd (ψ :: l)) := rfl

/-! ### Crank and atoms bounds for `bigAnd`/`bigOr` -/

theorem crank_bigAnd_le {r : Nat} :
    ∀ {T : List PLLFormula}, T ≠ [] → (∀ D ∈ T, crank D ≤ r) →
      crank (bigAnd T) ≤ r
  | [], h, _ => absurd rfl h
  | [E], _, h => h E (.head _)
  | E :: F :: l, _, h => by
      have h₁ := h E (.head _)
      have h₂ : crank (bigAnd (F :: l)) ≤ r :=
        crank_bigAnd_le (by simp) fun D hD => h D (.tail _ hD)
      simp only [bigAnd_cons₂, crank]
      omega

theorem atoms_bigAnd {Q : String → Prop} :
    ∀ {T : List PLLFormula}, (∀ D ∈ T, ∀ a ∈ D.atoms, Q a) →
      ∀ a ∈ (bigAnd T).atoms, Q a
  | [], _, a, ha => by simp [truePLL] at ha
  | [E], h, a, ha => h E (.head _) a ha
  | E :: F :: l, h, a, ha => by
      rcases mem_atoms_and.mp ha with h' | h'
      · exact h E (.head _) a h'
      · exact atoms_bigAnd (fun D hD => h D (.tail _ hD)) a h'

theorem crank_bigOr_le {r : Nat} :
    ∀ {S : List PLLFormula}, (∀ D ∈ S, crank D ≤ r) → crank (bigOr S) ≤ r
  | [], _ => by simp [crank]
  | E :: l, h => by
      have h₁ := h E (.head _)
      have h₂ : crank (bigOr l) ≤ r := crank_bigOr_le fun D hD => h D (.tail _ hD)
      simp only [bigOr, crank]
      omega

theorem atoms_bigOr {Q : String → Prop} :
    ∀ {S : List PLLFormula}, (∀ D ∈ S, ∀ a ∈ D.atoms, Q a) →
      ∀ a ∈ (bigOr S).atoms, Q a
  | [], _, a, ha => by simp at ha
  | E :: l, h, a, ha => by
      rcases mem_atoms_or.mp ha with h' | h'
      · exact h E (.head _) a h'
      · exact atoms_bigOr (fun D hD => h D (.tail _ hD)) a h'

/-! ### Calculus of finite conjunctions and disjunctions -/

/-- A finite conjunction proves each of its members. -/
theorem Deriv.bigAndElim :
    ∀ {T : List PLLFormula} {D : PLLFormula}, D ∈ T → Deriv [bigAnd T] D
  | [], _, h => nomatch h
  | [E], D, h => by
      obtain rfl : D = E := List.mem_singleton.mp h
      exact Deriv.iden (.head _)
  | E :: F :: l, D, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Deriv.andElim1 (Deriv.iden (.head _))
      · exact Deriv.cutHead (Deriv.andElim2 (Deriv.iden (.head _)))
          (Deriv.bigAndElim h')

/-- A context proving each member proves the conjunction. -/
theorem Deriv.bigAndIntro {Γ : List PLLFormula} :
    ∀ {T : List PLLFormula}, (∀ D ∈ T, Deriv Γ D) → Deriv Γ (bigAnd T)
  | [], _ => Deriv.impIntro (Deriv.iden (.head _))
  | [E], h => h E (.head _)
  | E :: _ :: _, h =>
      Deriv.andIntro (h E (.head _))
        (Deriv.bigAndIntro fun D hD => h D (.tail _ hD))

/-- Each member proves the finite disjunction. -/
theorem Deriv.bigOrIntroT :
    ∀ {S : List PLLFormula} {D : PLLFormula}, D ∈ S → Deriv [D] (bigOr S)
  | [], _, h => nomatch h
  | E :: l, D, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact Deriv.orIntro1 (Deriv.iden (.head _))
      · exact Deriv.orIntro2 (Deriv.bigOrIntroT h')

/-- Eliminate a finite disjunction (`Prop`-level; the `Type`-level
branch functions are recovered with choice). -/
theorem Deriv.bigOrElim {Γ : List PLLFormula} {χ : PLLFormula}
    {Ds : List PLLFormula} (p : Deriv Γ (bigOr Ds))
    (br : ∀ φ ∈ Ds, Deriv (φ :: Γ) χ) : Deriv Γ χ :=
  ⟨LaxND.bigOrElim (Nonempty.some p) fun φ h => Nonempty.some (br φ h)⟩

/-- Monotonicity of finite disjunction along a derivable refinement of
the disjunct list. -/
theorem deriv_bigOr_mono {A B : List PLLFormula}
    (h : ∀ x ∈ A, ∃ y ∈ B, Deriv [x] y) : Deriv [bigOr A] (bigOr B) := by
  refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
  intro x hx
  obtain ⟨y, hy, d⟩ := h x hx
  exact Deriv.toHead (d.cutHead (Deriv.bigOrIntroT hy))

/-- Conjunctions over lists with the same members are interderivable. -/
theorem interd_bigAnd_of_mem_iff {T T' : List PLLFormula}
    (h : ∀ x, x ∈ T ↔ x ∈ T') : Interd (bigAnd T) (bigAnd T') :=
  ⟨Deriv.bigAndIntro fun D hD => Deriv.bigAndElim ((h D).mpr hD),
   Deriv.bigAndIntro fun D hD => Deriv.bigAndElim ((h D).mp hD)⟩

/-- Disjunctions over lists with the same members are interderivable. -/
theorem interd_bigOr_of_mem_iff {S S' : List PLLFormula}
    (h : ∀ x, x ∈ S ↔ x ∈ S') : Interd (bigOr S) (bigOr S') :=
  ⟨deriv_bigOr_mono fun x hx => ⟨x, (h x).mp hx, Deriv.iden (.head _)⟩,
   deriv_bigOr_mono fun x hx => ⟨x, (h x).mpr hx, Deriv.iden (.head _)⟩⟩

/-- A formula is interderivable with its singleton disjunction `φ ∨ ⊥`. -/
theorem interd_bigOr_single (φ : PLLFormula) : Interd φ (bigOr [φ]) :=
  ⟨Deriv.orIntro1 (Deriv.iden (.head _)),
   Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _))
     (Deriv.falsoElim _ (Deriv.iden (.head _)))⟩

/-! ### Distribution laws for DNF data

A DNF datum is a list `ds` of conjunct lists; its formula is
`bigOr (ds.map bigAnd)`. -/

/-- Conjunction of two DNFs: the cross product of the conjunct lists. -/
theorem interd_and_dnf (ds₁ ds₂ : List (List PLLFormula)) :
    Interd ((bigOr (ds₁.map bigAnd)).and (bigOr (ds₂.map bigAnd)))
      (bigOr ((ds₁.flatMap fun S => ds₂.map fun T => S ++ T).map bigAnd)) := by
  refine ⟨?_, ?_⟩
  · -- distribute the conjunction over both disjunctions
    refine Deriv.bigOrElim (Deriv.andElim1 (Deriv.iden (.head _))) ?_
    intro x hx
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hx
    refine Deriv.bigOrElim (Deriv.andElim2 (Deriv.iden (.tail _ (.head _)))) ?_
    intro y hy
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hy
    have hcross : bigAnd (S ++ T)
        ∈ (ds₁.flatMap fun S => ds₂.map fun T => S ++ T).map bigAnd :=
      List.mem_map.mpr ⟨S ++ T,
        List.mem_flatMap.mpr ⟨S, hS, List.mem_map.mpr ⟨T, hT, rfl⟩⟩, rfl⟩
    refine Deriv.cutHead ?_ (Deriv.bigOrIntroT hcross)
    refine Deriv.bigAndIntro ?_
    intro D hD
    rcases List.mem_append.mp hD with h' | h'
    · exact Deriv.cutHead (Deriv.iden (.tail _ (.head _))) (Deriv.bigAndElim h')
    · exact Deriv.cutHead (Deriv.iden (.head _)) (Deriv.bigAndElim h')
  · -- each cross conjunct recovers both original disjunctions
    refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro z hz
    obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hz
    obtain ⟨S, hS, hU'⟩ := List.mem_flatMap.mp hU
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hU'
    refine Deriv.andIntro ?_ ?_
    · refine Deriv.cutHead ?_
        (Deriv.bigOrIntroT (List.mem_map.mpr ⟨S, hS, rfl⟩))
      exact Deriv.cutHead (Deriv.iden (.head _))
        (Deriv.bigAndIntro fun D hD =>
          Deriv.bigAndElim (List.mem_append.mpr (Or.inl hD)))
    · refine Deriv.cutHead ?_
        (Deriv.bigOrIntroT (List.mem_map.mpr ⟨T, hT, rfl⟩))
      exact Deriv.cutHead (Deriv.iden (.head _))
        (Deriv.bigAndIntro fun D hD =>
          Deriv.bigAndElim (List.mem_append.mpr (Or.inr hD)))

/-- Disjunction of two DNFs: append the conjunct lists. -/
theorem interd_or_append (ds₁ ds₂ : List (List PLLFormula)) :
    Interd ((bigOr (ds₁.map bigAnd)).or (bigOr (ds₂.map bigAnd)))
      (bigOr ((ds₁ ++ ds₂).map bigAnd)) := by
  rw [List.map_append]
  refine ⟨?_, ?_⟩
  · refine Deriv.orElim (Deriv.iden (.head _)) ?_ ?_
    · exact Deriv.toHead (deriv_bigOr_mono fun x hx =>
        ⟨x, List.mem_append.mpr (Or.inl hx), Deriv.iden (.head _)⟩)
    · exact Deriv.toHead (deriv_bigOr_mono fun x hx =>
        ⟨x, List.mem_append.mpr (Or.inr hx), Deriv.iden (.head _)⟩)
  · refine Deriv.bigOrElim (Deriv.iden (.head _)) ?_
    intro x hx
    rcases List.mem_append.mp hx with h' | h'
    · exact Deriv.toHead (Deriv.orIntro1 (Deriv.bigOrIntroT h'))
    · exact Deriv.toHead (Deriv.orIntro2 (Deriv.bigOrIntroT h'))

/-! ## The representative lists -/

/-- All implications between members of `l`. -/
def implList (l : List PLLFormula) : List PLLFormula :=
  l.flatMap fun D => l.map fun E => D.ifThen E

/-- All boxes of members of `l`. -/
def boxList (l : List PLLFormula) : List PLLFormula := l.map .somehow

/-- All disjunctions of nonempty conjunctions of members of `c`, in
the canonical (sublist) enumeration order. -/
def dnfL (c : List PLLFormula) : List PLLFormula :=
  (((c.sublists.filter (· ≠ [])).map bigAnd).sublists).map bigOr

theorem mem_implList {l : List PLLFormula} {P : PLLFormula} :
    P ∈ implList l ↔ ∃ D ∈ l, ∃ E ∈ l, D.ifThen E = P := by
  simp [implList]

theorem mem_boxList {l : List PLLFormula} {P : PLLFormula} :
    P ∈ boxList l ↔ ∃ D ∈ l, PLLFormula.somehow D = P := by
  simp [boxList]

/-- The rank-stratified components: atoms and `⊥` at rank 0; from rank
1 on, implications between canonical DNFs one rank down (crank ≤ r);
from rank 2 on, boxes of canonical DNFs two ranks down (crank ≤ r). -/
def comps (V : List String) : Nat → List PLLFormula
  | 0 => .falsePLL :: V.map .prop
  | 1 => comps V 0 ++ implList (dnfL (comps V 0))
  | (r+2) => comps V (r+1) ++ implList (dnfL (comps V (r+1)))
      ++ boxList (dnfL (comps V r))

theorem comps_zero (V : List String) :
    comps V 0 = .falsePLL :: V.map .prop := by rw [comps]

theorem comps_one (V : List String) :
    comps V 1 = comps V 0 ++ implList (dnfL (comps V 0)) := by
  conv_lhs => rw [comps]

theorem comps_add_two (V : List String) (r : Nat) :
    comps V (r+2) = comps V (r+1) ++ implList (dnfL (comps V (r+1)))
      ++ boxList (dnfL (comps V r)) := by rw [comps]

theorem comps_succ_append (V : List String) :
    ∀ r : Nat, ∃ rest, comps V (r+1) = comps V r ++ rest
  | 0 => ⟨_, comps_one V⟩
  | r+1 =>
      ⟨implList (dnfL (comps V (r+1))) ++ boxList (dnfL (comps V r)), by
        rw [comps_add_two, List.append_assoc]⟩

theorem comps_mono {V : List String} {r : Nat} :
    ∀ P ∈ comps V r, P ∈ comps V (r+1) := by
  intro P hP
  obtain ⟨rest, h⟩ := comps_succ_append V r
  rw [h]
  exact List.mem_append_left _ hP

theorem comps_le_mono {V : List String} {r r' : Nat} (h : r ≤ r') :
    ∀ P ∈ comps V r, P ∈ comps V r' := by
  induction h with
  | refl => exact fun _ hP => hP
  | step _ ih => exact fun P hP => comps_mono P (ih P hP)

/-! ### Crank and atoms bounds for `dnfL` and `comps` -/

theorem dnfL_crank {c : List PLLFormula} {r : Nat}
    (hc : ∀ P ∈ c, crank P ≤ r) : ∀ D ∈ dnfL c, crank D ≤ r := by
  intro D hD
  simp only [dnfL, List.mem_map] at hD
  obtain ⟨E, hE, rfl⟩ := hD
  refine crank_bigOr_le fun x hx => ?_
  have hx' := (List.mem_sublists.mp hE).subset hx
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, ne_eq] at hx'
  obtain ⟨T, ⟨hT, hTne⟩, rfl⟩ := hx'
  exact crank_bigAnd_le hTne fun P hP => hc P ((List.mem_sublists.mp hT).subset hP)

theorem dnfL_atoms {c : List PLLFormula} {Q : String → Prop}
    (hc : ∀ P ∈ c, ∀ a ∈ P.atoms, Q a) :
    ∀ D ∈ dnfL c, ∀ a ∈ D.atoms, Q a := by
  intro D hD
  simp only [dnfL, List.mem_map] at hD
  obtain ⟨E, hE, rfl⟩ := hD
  refine atoms_bigOr fun x hx => ?_
  have hx' := (List.mem_sublists.mp hE).subset hx
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, ne_eq] at hx'
  obtain ⟨T, ⟨hT, _⟩, rfl⟩ := hx'
  exact atoms_bigAnd fun P hP => hc P ((List.mem_sublists.mp hT).subset hP)

theorem comps_crank (V : List String) : ∀ r : Nat, ∀ P ∈ comps V r, crank P ≤ r
  | 0 => by
      intro P hP
      rw [comps_zero] at hP
      rcases List.mem_cons.mp hP with rfl | hP
      · simp [crank]
      · obtain ⟨b, _, rfl⟩ := List.mem_map.mp hP
        simp [crank]
  | 1 => by
      intro P hP
      rw [comps_one] at hP
      rcases List.mem_append.mp hP with h | h
      · exact (comps_crank V 0 P h).trans (by omega)
      · obtain ⟨D, hD, E, hE, rfl⟩ := mem_implList.mp h
        have hd := dnfL_crank (comps_crank V 0) D hD
        have he := dnfL_crank (comps_crank V 0) E hE
        simp only [crank]
        omega
  | (r+2) => by
      intro P hP
      rw [comps_add_two] at hP
      rcases List.mem_append.mp hP with h | hbox
      · rcases List.mem_append.mp h with h' | h'
        · exact (comps_crank V (r+1) P h').trans (by omega)
        · obtain ⟨D, hD, E, hE, rfl⟩ := mem_implList.mp h'
          have hd := dnfL_crank (comps_crank V (r+1)) D hD
          have he := dnfL_crank (comps_crank V (r+1)) E hE
          simp only [crank]
          omega
      · obtain ⟨D, hD, rfl⟩ := mem_boxList.mp hbox
        have hd := dnfL_crank (comps_crank V r) D hD
        simp only [crank]
        omega

theorem comps_atoms (V : List String) :
    ∀ r : Nat, ∀ P ∈ comps V r, ∀ a ∈ P.atoms, a ∈ V
  | 0 => by
      intro P hP a ha
      rw [comps_zero] at hP
      rcases List.mem_cons.mp hP with rfl | hP
      · simp at ha
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hP
        simp only [atoms_prop, Finset.mem_singleton] at ha
        subst ha
        exact hb
  | 1 => by
      intro P hP a ha
      rw [comps_one] at hP
      rcases List.mem_append.mp hP with h | h
      · exact comps_atoms V 0 P h a ha
      · obtain ⟨D, hD, E, hE, rfl⟩ := mem_implList.mp h
        rcases mem_atoms_ifThen.mp ha with h' | h'
        · exact dnfL_atoms (comps_atoms V 0) D hD a h'
        · exact dnfL_atoms (comps_atoms V 0) E hE a h'
  | (r+2) => by
      intro P hP a ha
      rw [comps_add_two] at hP
      rcases List.mem_append.mp hP with h | hbox
      · rcases List.mem_append.mp h with h' | h'
        · exact comps_atoms V (r+1) P h' a ha
        · obtain ⟨D, hD, E, hE, rfl⟩ := mem_implList.mp h'
          rcases mem_atoms_ifThen.mp ha with h'' | h''
          · exact dnfL_atoms (comps_atoms V (r+1)) D hD a h''
          · exact dnfL_atoms (comps_atoms V (r+1)) E hE a h''
      · obtain ⟨D, hD, rfl⟩ := mem_boxList.mp hbox
        rw [atoms_somehow] at ha
        exact dnfL_atoms (comps_atoms V r) D hD a ha

theorem implList_dnfL_subset (V : List String) :
    ∀ s : Nat, ∀ P ∈ implList (dnfL (comps V s)), P ∈ comps V (s+1)
  | 0 => by
      intro P hP
      rw [comps_one]
      exact List.mem_append_right _ hP
  | t+1 => by
      intro P hP
      rw [comps_add_two]
      exact List.mem_append_left _ (List.mem_append_right _ hP)

theorem boxList_dnfL_subset (V : List String) (s : Nat) :
    ∀ P ∈ boxList (dnfL (comps V s)), P ∈ comps V (s+2) := by
  intro P hP
  rw [comps_add_two]
  exact List.mem_append_right _ hP

/-! ## Canonicalisation -/

/-- The canonical conjunct associated to `S`: filter the enumeration
`c` down to the members of `S`. -/
def canonAnd (c S : List PLLFormula) : PLLFormula := bigAnd (c.filter (· ∈ S))

/-- The canonical disjunct list associated to a DNF datum `ds`: filter
the canonical conjunct enumeration down to the canonical conjuncts of
members of `ds`. -/
def canonList (c : List PLLFormula) (ds : List (List PLLFormula)) :
    List PLLFormula :=
  ((c.sublists.filter (· ≠ [])).map bigAnd).filter (· ∈ ds.map (canonAnd c))

theorem mem_filter_mem_iff {c S : List PLLFormula} (hSc : ∀ P ∈ S, P ∈ c)
    (x : PLLFormula) : x ∈ c.filter (· ∈ S) ↔ x ∈ S := by
  simp only [List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hSc x h, h⟩⟩

theorem interd_canonAnd {c S : List PLLFormula} (hSc : ∀ P ∈ S, P ∈ c) :
    Interd (bigAnd S) (canonAnd c S) :=
  interd_bigAnd_of_mem_iff fun x => (mem_filter_mem_iff hSc x).symm

theorem canonAnd_mem {c S : List PLLFormula} (hSne : S ≠ [])
    (hSc : ∀ P ∈ S, P ∈ c) :
    canonAnd c S ∈ (c.sublists.filter (· ≠ [])).map bigAnd := by
  refine List.mem_map.mpr ⟨c.filter (· ∈ S), ?_, rfl⟩
  rw [List.mem_filter]
  refine ⟨List.mem_sublists.mpr List.filter_sublist, ?_⟩
  simp only [decide_eq_true_eq, ne_eq]
  obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil S hSne
  exact List.ne_nil_of_mem ((mem_filter_mem_iff hSc x₀).mpr hx₀)

/-- **Canonicalisation**: any DNF datum over `comps V s` is
interderivable with a MEMBER of the fixed finite list
`dnfL (comps V s)`. -/
theorem canonicalise (V : List String) (s : Nat) (ds : List (List PLLFormula))
    (h : ∀ S ∈ ds, S ≠ [] ∧ ∀ P ∈ S, P ∈ comps V s) :
    ∃ D ∈ dnfL (comps V s), Interd (bigOr (ds.map bigAnd)) D := by
  refine ⟨bigOr (canonList (comps V s) ds), ?_, ?_, ?_⟩
  · -- membership: the canonical disjunct list is a sublist of the enumeration
    simp only [dnfL]
    refine List.mem_map.mpr ⟨canonList (comps V s) ds, ?_, rfl⟩
    exact List.mem_sublists.mpr List.filter_sublist
  · -- forward: each conjunct maps to its canonical form
    refine deriv_bigOr_mono ?_
    intro x hx
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hSne, hSc⟩ := h S hS
    refine ⟨canonAnd (comps V s) S, ?_, (interd_canonAnd hSc).1⟩
    simp only [canonList, List.mem_filter, decide_eq_true_eq]
    exact ⟨canonAnd_mem hSne hSc, List.mem_map.mpr ⟨S, hS, rfl⟩⟩
  · -- backward: each canonical conjunct comes from some original one
    refine deriv_bigOr_mono ?_
    intro x hx
    simp only [canonList, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨-, hx⟩ := hx
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hSne, hSc⟩ := h S hS
    exact ⟨bigAnd S, List.mem_map.mpr ⟨S, hS, rfl⟩, (interd_canonAnd hSc).2⟩

/-! ## The normal-form lemma -/

/-- **Normal form**: every formula of crank ≤ r over atoms in `V` is
interderivable with a disjunction of nonempty conjunctions of members
of `comps V r`. -/
theorem toDNF (V : List String) :
    ∀ (φ : PLLFormula) (r : Nat), crank φ ≤ r → (∀ a ∈ φ.atoms, a ∈ V) →
    ∃ ds : List (List PLLFormula),
      (∀ S ∈ ds, S ≠ [] ∧ ∀ P ∈ S, P ∈ comps V r) ∧
      Interd φ (bigOr (ds.map bigAnd)) := by
  intro φ
  induction φ with
  | prop b =>
      intro r _ ha
      refine ⟨[[.prop b]], ?_, ?_⟩
      · intro S hS
        obtain rfl : S = [.prop b] := List.mem_singleton.mp hS
        refine ⟨by simp, ?_⟩
        intro P hP
        obtain rfl : P = .prop b := List.mem_singleton.mp hP
        refine comps_le_mono (Nat.zero_le r) _ ?_
        rw [comps_zero]
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨b, ha b (by simp), rfl⟩)
      · simpa using interd_bigOr_single (PLLFormula.prop b)
  | falsePLL =>
      intro r _ _
      exact ⟨[], by simp, by simpa using Interd.refl PLLFormula.falsePLL⟩
  | and φ ψ ihφ ihψ =>
      intro r hc ha
      have hcφ : crank φ ≤ r := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ r := by simp only [crank] at hc; omega
      obtain ⟨ds₁, h₁, i₁⟩ := ihφ r hcφ fun a h' => ha a (mem_atoms_and.mpr (Or.inl h'))
      obtain ⟨ds₂, h₂, i₂⟩ := ihψ r hcψ fun a h' => ha a (mem_atoms_and.mpr (Or.inr h'))
      refine ⟨ds₁.flatMap fun S => ds₂.map fun T => S ++ T, ?_, ?_⟩
      · intro S hS
        simp only [List.mem_flatMap, List.mem_map] at hS
        obtain ⟨S₁, hS₁, S₂, hS₂, rfl⟩ := hS
        obtain ⟨hne₁, hm₁⟩ := h₁ S₁ hS₁
        obtain ⟨hne₂, hm₂⟩ := h₂ S₂ hS₂
        constructor
        · obtain ⟨x₀, hx₀⟩ := List.exists_mem_of_ne_nil S₁ hne₁
          exact List.ne_nil_of_mem (List.mem_append.mpr (Or.inl hx₀))
        · intro P hP
          rcases List.mem_append.mp hP with h' | h'
          exacts [hm₁ P h', hm₂ P h']
      · exact (Interd.and_congr i₁ i₂).trans (interd_and_dnf ds₁ ds₂)
  | or φ ψ ihφ ihψ =>
      intro r hc ha
      have hcφ : crank φ ≤ r := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ r := by simp only [crank] at hc; omega
      obtain ⟨ds₁, h₁, i₁⟩ := ihφ r hcφ fun a h' => ha a (mem_atoms_or.mpr (Or.inl h'))
      obtain ⟨ds₂, h₂, i₂⟩ := ihψ r hcψ fun a h' => ha a (mem_atoms_or.mpr (Or.inr h'))
      refine ⟨ds₁ ++ ds₂, ?_, ?_⟩
      · intro S hS
        rcases List.mem_append.mp hS with h' | h'
        exacts [h₁ S h', h₂ S h']
      · exact (Interd.or_congr i₁ i₂).trans (interd_or_append ds₁ ds₂)
  | ifThen φ ψ ihφ ihψ =>
      intro r hc ha
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 :=
        ⟨r - 1, by simp only [crank] at hc; omega⟩
      have hcφ : crank φ ≤ s := by simp only [crank] at hc; omega
      have hcψ : crank ψ ≤ s := by simp only [crank] at hc; omega
      obtain ⟨ds₁, h₁, i₁⟩ := ihφ s hcφ fun a h' => ha a (mem_atoms_ifThen.mpr (Or.inl h'))
      obtain ⟨ds₂, h₂, i₂⟩ := ihψ s hcψ fun a h' => ha a (mem_atoms_ifThen.mpr (Or.inr h'))
      obtain ⟨D₁, hD₁, j₁⟩ := canonicalise V s ds₁ h₁
      obtain ⟨D₂, hD₂, j₂⟩ := canonicalise V s ds₂ h₂
      refine ⟨[[D₁.ifThen D₂]], ?_, ?_⟩
      · intro S hS
        obtain rfl : S = [D₁.ifThen D₂] := List.mem_singleton.mp hS
        refine ⟨by simp, ?_⟩
        intro P hP
        obtain rfl : P = D₁.ifThen D₂ := List.mem_singleton.mp hP
        exact implList_dnfL_subset V s _ (mem_implList.mpr ⟨D₁, hD₁, D₂, hD₂, rfl⟩)
      · refine (Interd.imp_congr (i₁.trans j₁) (i₂.trans j₂)).trans ?_
        simpa using interd_bigOr_single (D₁.ifThen D₂)
  | somehow φ ihφ =>
      intro r hc ha
      obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 :=
        ⟨r - 2, by simp only [crank] at hc; omega⟩
      have hcφ : crank φ ≤ s := by simp only [crank] at hc; omega
      obtain ⟨ds₁, h₁, i₁⟩ := ihφ s hcφ ha
      obtain ⟨D, hD, j⟩ := canonicalise V s ds₁ h₁
      refine ⟨[[.somehow D]], ?_, ?_⟩
      · intro S hS
        obtain rfl : S = [.somehow D] := List.mem_singleton.mp hS
        refine ⟨by simp, ?_⟩
        intro P hP
        obtain rfl : P = .somehow D := List.mem_singleton.mp hP
        exact boxList_dnfL_subset V s _ (mem_boxList.mpr ⟨D, hD, rfl⟩)
      · refine (Interd.box_congr (i₁.trans j)).trans ?_
        simpa using interd_bigOr_single (PLLFormula.somehow D)

/-! ## The fragment-finiteness theorem -/

/-- **Fragment finiteness up to interderivability** (Litak–Visser
Thm 4.5 analogue for PLL): the finite list `dnfL (comps V.toList r)`
contains, up to interderivability, every formula of crank ≤ r over
atoms in `V`, and all its members satisfy the same bounds. -/
theorem frag_reps_exist' (V : Finset String) (r : Nat) :
    ∃ L : List PLLFormula,
      (∀ D ∈ L, crank D ≤ r ∧ ∀ a ∈ D.atoms, a ∈ V) ∧
      ∀ φ : PLLFormula, crank φ ≤ r → (∀ a ∈ φ.atoms, a ∈ V) →
        ∃ D ∈ L, Nonempty (LaxND [φ] D) ∧ Nonempty (LaxND [D] φ) := by
  refine ⟨dnfL (comps V.toList r), ?_, ?_⟩
  · intro D hD
    refine ⟨dnfL_crank (comps_crank V.toList r) D hD, ?_⟩
    intro a ha
    exact Finset.mem_toList.mp (dnfL_atoms (comps_atoms V.toList r) D hD a ha)
  · intro φ hcφ haφ
    obtain ⟨ds, hds, i⟩ :=
      toDNF V.toList φ r hcφ fun a h' => Finset.mem_toList.mpr (haφ a h')
    obtain ⟨D, hD, j⟩ := canonicalise V.toList r ds hds
    exact ⟨D, hD, (i.trans j).1, (i.trans j).2⟩

/-- info: 'PLLND.SemUI.frag_reps_exist'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms frag_reps_exist'

end SemUI
end PLLND
