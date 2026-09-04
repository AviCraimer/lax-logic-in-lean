import LaxLogic.PLLG4Gap
import LaxLogic.PLLG4UI

/-!
# Iemhoff's UI proof in its own habitat: quantifiers for G4iLL proper

Task #13.  The repo refuted the bridge (her Corollary 1 / book Cor 8.1:
`G3iLL ≡ G4iLL`) on which Iemhoff's Theorem 6 (book Thm 8.6, "PLL has
uniform interpolation") rests: `PLLG4Gap.lean` separates the calculi and
moreover proves **cut is not admissible in G4iLL**
(`PLLG4Gap.cut_not_admissible`) and **contraction is not admissible**
(`contraction_not_admissible`).  This file asks the residual question:
is her construction locally correct *for her own calculus* — does
uniform interpolation hold for **G4iLL-derivability** (a proper
sublogic of PLL), with her own quantifier tables, and with the
adequacy statement read *derivability-relatively* (no cut anywhere)?

## The calculus

We build on `PLLND.G4` of `LaxLogic/PLLG4.lean`, which *is* Iemhoff's
G4iLL transcribed verbatim (checked once more against Figures 2.2/2.3
of arXiv:2209.08976v1): `impLLax` = her `R◯→`, `impLLaxLax` = her
`L◯→`; every left rule consumes its principal.  One flagged delta: the
repo's `G4` has `impLBot` (`⊥→ψ` is deleted), while her Figure 2.2 has
no rule for `⊥→ψ` (for her, `⊥` is not an atom, so no `L1→` instance
matches).  We keep the repo rule and give it the evident clause; the
choice is conservative for the separation question and is flagged at
the clause site.

## Her quantifiers, transcribed

Sources: her §6.3–6.6 (arXiv v1; = book §8.6.3–8.6.6) plus the
*standard interpolant assignment* of "Uniform interpolation and the
existence of sequent calculi" (APAL 2019) §4.3 and §5, from which her
PLL assignment explicitly extends.  Dictionary: her `∃pS` and `∀pS`
are **sequent-indexed** (she proves `∃pS ≡ ∃p⋀Sᵃ` and `∀pS ≡ ∀pI(S)`
only *in the logic*, through the equivalence we refuted, so we must
not collapse the succedent-sensitivity); we write `iemE p Γ C` and
`iemA p Γ C`, with `C = ⊥` playing her empty succedent (`⊥` is never
principal on the right in G4iLL, and her own plumbing conjuncts
`∃p(Sᵃ⇒)` only fire at `Sˢ ≠ ∅`, which we render as `C ≠ ⊥`).

Her recursion terminates on the plain Dershowitz–Manna order over
`weight` (her Fact 1/2: G4iLL is *reductive*) — no retention, so every
clause's sequent strictly descends; no fuel and no budget are needed
*mathematically*.  Mechanically we define the pair by **fuel
recursion with her measure as the promised bound** (documented
choice: the WF mutual recursion over nested `flatMap`/`filterMap`
binders costs a day of `decreasing_by` plumbing that buys nothing for
the adequacy question).  The single `Nat` measure
`seqMeasure Γ C = Σ_{φ∈Γ} 4^{weight φ} + (if C = ⊥ then 0 else 4^{weight C})`
linearises her DM order clause-by-clause (each rule replaces one
principal of measure `4^w` by at most two pieces of measures
`4^{w'} , w' < w`, and `4^a + 4^b < 4^c` for `a, b < c`); the lemma
`seqMeasure`-descent per clause is recorded below, so
`fuel = seqMeasure Γ C` always suffices and the packaged interpolant
at that fuel is fuel-free, i.e. *uniform* — computed from the sequent
alone, never from a derivation.
-/

open PLLFormula

namespace PLLND
namespace G4UI

/-! ### The measure (her ≪, linearised) -/

/-- `4^weight`: the Dershowitz–Manna order on weight-multisets embeds
into `Nat` by summing these, because every G4iLL premise replaces one
formula by at most two strictly lighter ones. -/
def fwt (φ : PLLFormula) : Nat := 4 ^ φ.weight

/-- Antecedent measure. -/
def ctxMeasure (Γ : List PLLFormula) : Nat := (Γ.map fwt).sum

/-- Sequent measure; `⊥` models her empty succedent and counts `0`. -/
def seqMeasure (Γ : List PLLFormula) (C : PLLFormula) : Nat :=
  ctxMeasure Γ + (if C = falsePLL then 0 else fwt C)

/-! ### The quantifier pair

Clause tables verbatim from her papers (see the module docstring for
the source of each family).  Layout of `iemE p (fuel+1) Γ C`, a big
conjunction:

* `∃ᵃᵗ` part 1 — atoms `q ≠ p` of `Γ`, and `⊥` if `⊥ ∈ Γ`;
* axiom instances — if `S` is an `At`- or `L⊥`-instance, the
  conjunction of the p-free members of `Γ`;
* per context formula `F ∈ Γ` with `Γ' = Γ.erase F` (rule instances
  with `F` principal, plus the `∃ᵃᵗ` implication family):
  - `F = A∧B` (L∧): `E(A,B,Γ' ⇒ C)`
  - `F = A∨B` (L∨): `E(A,Γ' ⇒ C) ∨ E(B,Γ' ⇒ C)`
  - `F = q→B`: if `q ∈ Γ'` the `L1→` instance conjunct
    (`q = p`: `E(B,Γ' ⇒ C)`; else `q ∧ E(B,Γ' ⇒ C)`), and always
    (for `q ≠ p`) the `∃ᵃᵗ` conjunct `q → E(B,Γ' ⇒ C)`
  - `F = ⊥→B` (repo `impLBot`, flagged extension): `E(Γ' ⇒ C)`
  - `F = (A∧B)→D` (L2→): `E(A→(B→D),Γ' ⇒ C)`
  - `F = (A∨B)→D` (L3→): `E(A→D,B→D,Γ' ⇒ C)`
  - `F = (A→B)→D` (L4→): `E(B→D,Γ' ⇒ A→B) ∧ (A(B→D,Γ' ⇒ A→B) → E(D,Γ' ⇒ C))`
  - `F = ◯A→B` (R◯→): `E(Γ' ⇒ A) ∧ (A(Γ' ⇒ A) → E(B,Γ' ⇒ C))`;
    (L◯→, one per witness box `◯x ∈ Γ'`, `Γ'' = Γ'.erase ◯x`):
    `◯E(x,Γ'' ⇒ ◯A) ∧ (◯A(x,Γ'' ⇒ ◯A) → E(B,Γ' ⇒ C))`
  - `F = ◯χ` (L◯ instance, only for `C = ◯ψ`): `◯E(χ,Γ' ⇒ C)`
* right-rule instances, by the shape of `C`:
  - `C = A∧B` (R∧): `E(Γ ⇒ A) ∨ E(Γ ⇒ B)`
  - `C = A∨B` (R∨, two instances): `E(Γ ⇒ A)` and `E(Γ ⇒ B)`
  - `C = A→B` (R→): `A → E(A,Γ ⇒ B)` if `p ∉ A`, else nothing (her `⊤`)
  - `C = ◯D` (R◯): `◯E(Γ ⇒ D)`
* `L◯→`-nonprincipal (her `S^γ`, every sequent):
  - box openers, one per `◯α ∈ Γ`: `◯E(α, Γ.erase ◯α ⇒ ∅)`
  - γ-forms, one per `γ = ◯α→β ∈ Γ`:
    `E(Γ.erase γ ⇒ ◯α) ∧ (◯A(Γ.erase γ ⇒ ◯α) → E(β, Γ.erase γ ⇒ C))`
* succedent plumbing (only for `C ≠ ⊥`; her `R◯→`/`L4→`-nonprincipal
  `⋀{∃p(Π⇒) | Π ⊆ Sᵃ}`): `E(Π ⇒ ∅)` for every sublist `Π` of `Γ`.

`iemA p (fuel+1) Γ C`, a big disjunction:

* `∀ᵃᵗ` — `C = q ≠ p`: disjunct `q`; and per `q→B ∈ Γ` (`q ≠ p`):
  `q ∧ A(B, Γ.erase (q→B) ⇒ C)`;
* axiom instances — `⊤` if (`C = q` and `q ∈ Γ`) or `⊥ ∈ Γ`;
* right-rule instances (goal clauses):
  - `C = A∧B` (R∧): `(E(Γ⇒A) → A(Γ⇒A)) ∧ (E(Γ⇒B) → A(Γ⇒B))`
  - `C = A∨B` (R∨, two): `E(Γ⇒A) → A(Γ⇒A)` and `E(Γ⇒B) → A(Γ⇒B)`
  - `C = A→B` (R→): `A → A(A,Γ ⇒ B)` if `p ∉ A`, else
    `E(A,Γ ⇒ B) → A(A,Γ ⇒ B)`
  - `C = ◯D` (R◯): `◯A(Γ ⇒ D)`
* per context formula `F ∈ Γ`, `Γ' = Γ.erase F`:
  - `F = A∧B` (L∧): `E(A,B,Γ'⇒C) → A(A,B,Γ'⇒C)`
  - `F = A∨B` (L∨): `(E(A,Γ'⇒C) → A(A,Γ'⇒C)) ∧ (E(B,Γ'⇒C) → A(B,Γ'⇒C))`
  - `F = q→B`, `q ∈ Γ'` (L1→): `q = p`: `A(B,Γ'⇒C)`, else `q → A(B,Γ'⇒C)`
  - `F = ⊥→B` (flagged): `E(Γ'⇒C) → A(Γ'⇒C)`
  - `F = (A∧B)→D` (L2→): `E(σ⇒C) → A(σ⇒C)`, `σ = A→(B→D),Γ'`
  - `F = (A∨B)→D` (L3→): likewise at `A→D,B→D,Γ'`
  - `F = (A→B)→D` (L4→): `(E(B→D,Γ'⇒A→B) → A(B→D,Γ'⇒A→B)) ∧ (E(D,Γ'⇒C) → A(D,Γ'⇒C))`
  - `F = ◯A→B` (R◯→, note: *unguarded*, her ι∀ᴿ = ∀pS₁ ∧ ∀pS₂):
    `A(Γ'⇒A) ∧ A(B,Γ'⇒C)`; (L◯→ per witness `◯x ∈ Γ'`):
    `◯A(x,Γ''⇒◯A) ∧ A(B,Γ'⇒C)`
  - `F = ◯χ` (L◯, only for `C = ◯ψ`): `◯A(χ,Γ'⇒C)`
* `L◯→`-nonprincipal γ-disjuncts, one per `γ = ◯α→β ∈ Γ`:
  `◯A(Γ.erase γ ⇒ ◯α) ∧ A(β, Γ.erase γ ⇒ C)`.
-/

/-- Is `S = (Γ ⇒ C)` an instance of one of her axioms (`At`, `L⊥`)? -/
def isAxInst (Γ : List PLLFormula) (C : PLLFormula) : Bool :=
  Γ.contains falsePLL ||
    (match C with | .prop _ => Γ.contains C | _ => false)

/-! #### Clause families

Each family is a plain (non-recursive) definition taking the
one-level-down quantifier values `E A` as parameters (the UIML
`e_rule`/`a_rule` architecture); the fueled pair below ties the knot.
All clause-membership reasoning happens on these, where the equation
lemmas reduce cleanly on constructor shapes. -/

section Clauses

variable (p : String) (E A : List PLLFormula → PLLFormula → PLLFormula)

/-- `∃ᵃᵗ` part 1: atoms `≠ p` of `Γ`, and `⊥` if present. -/
def eAtomList (Γ : List PLLFormula) : List PLLFormula :=
  Γ.filterMap (fun F => match F with
    | .prop q => if q = p then none else some (prop q)
    | .falsePLL => some falsePLL
    | _ => none)

/-- Left-rule instance clauses (plus the `∃ᵃᵗ` implication family) for
one context formula `F ∈ Γ`, E-side. -/
def eCtxClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  let Γ' := Γ.erase F
  match F with
  | .and A₁ B₁ => [E (A₁ :: B₁ :: Γ') C]
  | .or A₁ B₁ => [(E (A₁ :: Γ') C).or (E (B₁ :: Γ') C)]
  | .ifThen (.prop q) B₁ =>
      (if prop q ∈ Γ' then
        [if q = p then E (B₁ :: Γ') C
         else (prop q).and (E (B₁ :: Γ') C)] else [])
      ++ (if q = p then [] else [(prop q).ifThen (E (B₁ :: Γ') C)])
  | .ifThen .falsePLL _ => [E Γ' C]
  | .ifThen (.and A₁ B₁) D => [E (A₁.ifThen (B₁.ifThen D) :: Γ') C]
  | .ifThen (.or A₁ B₁) D => [E (A₁.ifThen D :: B₁.ifThen D :: Γ') C]
  | .ifThen (.ifThen A₁ B₁) D =>
      [(E (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).and
        ((A (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).ifThen (E (D :: Γ') C))]
  | .ifThen (.somehow A₁) B₁ =>
      ((E Γ' A₁).and ((A Γ' A₁).ifThen (E (B₁ :: Γ') C)))
      :: Γ'.filterMap (fun X => match X with
          | .somehow x =>
              let Γ'' := Γ'.erase (somehow x)
              some (((E (x :: Γ'') A₁.somehow).somehow).and
                (((A (x :: Γ'') A₁.somehow).somehow).ifThen (E (B₁ :: Γ') C)))
          | _ => none)
  | .somehow χ =>
      (match C with
        | .somehow _ => [(E (χ :: Γ') C).somehow]
        | _ => [])
  | _ => []

/-- Right-rule instance clauses, E-side, by the shape of `C`. -/
def eGoalClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .and A₁ B₁ => [(E Γ A₁).or (E Γ B₁)]
  | .or A₁ B₁ => [E Γ A₁, E Γ B₁]
  | .ifThen A₁ B₁ =>
      if p ∈ A₁.atoms then [] else [A₁.ifThen (E (A₁ :: Γ) B₁)]
  | .somehow D => [(E Γ D).somehow]
  | _ => []

/-- `L◯→`-nonprincipal box openers, one per `◯α ∈ Γ`. -/
def eOpenClauses (Γ : List PLLFormula) (F : PLLFormula) : List PLLFormula :=
  match F with
  | .somehow α => [(E (α :: Γ.erase (somehow α)) falsePLL).somehow]
  | _ => []

/-- `L◯→`-nonprincipal γ-forms, one per `γ = ◯α→β ∈ Γ`. -/
def eGammaClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  match F with
  | .ifThen (.somehow α) β =>
      let Γ' := Γ.erase F
      [(E Γ' α.somehow).and
        (((A Γ' α.somehow).somehow).ifThen (E (β :: Γ') C))]
  | _ => []

/-- Succedent plumbing `⋀{∃p(Θ⇒) | Θ ⊆ Γ}` (`C ≠ ⊥` only). -/
def ePlumbClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  if C = falsePLL then [] else Γ.sublists.map (fun Θ => E Θ falsePLL)

/-- Goal-directed disjuncts, A-side. -/
def aGoalClauses (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .prop q => if q = p then [] else [prop q]
  | .and A₁ B₁ =>
      [((E Γ A₁).ifThen (A Γ A₁)).and ((E Γ B₁).ifThen (A Γ B₁))]
  | .or A₁ B₁ =>
      [(E Γ A₁).ifThen (A Γ A₁), (E Γ B₁).ifThen (A Γ B₁)]
  | .ifThen A₁ B₁ =>
      if p ∈ A₁.atoms then [(E (A₁ :: Γ) B₁).ifThen (A (A₁ :: Γ) B₁)]
      else [A₁.ifThen (A (A₁ :: Γ) B₁)]
  | .somehow D => [(A Γ D).somehow]
  | _ => []

/-- Context-directed disjuncts for one `F ∈ Γ`, A-side. -/
def aCtxClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  let Γ' := Γ.erase F
  match F with
  | .and A₁ B₁ =>
      [(E (A₁ :: B₁ :: Γ') C).ifThen (A (A₁ :: B₁ :: Γ') C)]
  | .or A₁ B₁ =>
      [((E (A₁ :: Γ') C).ifThen (A (A₁ :: Γ') C)).and
        ((E (B₁ :: Γ') C).ifThen (A (B₁ :: Γ') C))]
  | .ifThen (.prop q) B₁ =>
      (if prop q ∈ Γ' then
        [if q = p then A (B₁ :: Γ') C
         else (prop q).ifThen (A (B₁ :: Γ') C)] else [])
      ++ (if q = p then [] else [(prop q).and (A (B₁ :: Γ') C)])
  | .ifThen .falsePLL _ => [(E Γ' C).ifThen (A Γ' C)]
  | .ifThen (.and A₁ B₁) D =>
      [(E (A₁.ifThen (B₁.ifThen D) :: Γ') C).ifThen
        (A (A₁.ifThen (B₁.ifThen D) :: Γ') C)]
  | .ifThen (.or A₁ B₁) D =>
      [(E (A₁.ifThen D :: B₁.ifThen D :: Γ') C).ifThen
        (A (A₁.ifThen D :: B₁.ifThen D :: Γ') C)]
  | .ifThen (.ifThen A₁ B₁) D =>
      [((E (B₁.ifThen D :: Γ') (A₁.ifThen B₁)).ifThen
          (A (B₁.ifThen D :: Γ') (A₁.ifThen B₁))).and
        ((E (D :: Γ') C).ifThen (A (D :: Γ') C))]
  | .ifThen (.somehow A₁) B₁ =>
      ((A Γ' A₁).and (A (B₁ :: Γ') C))
      :: Γ'.filterMap (fun X => match X with
          | .somehow x =>
              let Γ'' := Γ'.erase (somehow x)
              some (((A (x :: Γ'') A₁.somehow).somehow).and
                (A (B₁ :: Γ') C))
          | _ => none)
  | .somehow χ =>
      (match C with
        | .somehow _ => [(A (χ :: Γ') C).somehow]
        | _ => [])
  | _ => []

/-- `L◯→`-nonprincipal γ-disjuncts, A-side. -/
def aGammaClauses (Γ : List PLLFormula) (C F : PLLFormula) : List PLLFormula :=
  match F with
  | .ifThen (.somehow α) β =>
      let Γ' := Γ.erase F
      [((A Γ' α.somehow).somehow).and (A (β :: Γ') C)]
  | _ => []

end Clauses

mutual

/-- Iemhoff's `∃pS`, sequent-indexed, fueled. -/
def iemE (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => truePLL
  | fuel + 1, Γ, C =>
      andAll (
        eAtomList p Γ
        ++ (if isAxInst Γ C then
              [andAll (Γ.filter (fun φ => p ∉ φ.atoms))] else [])
        ++ Γ.flatMap (eCtxClauses p (iemE p fuel) (iemA p fuel) Γ C)
        ++ eGoalClauses p (iemE p fuel) Γ C
        ++ Γ.flatMap (eOpenClauses (iemE p fuel) Γ)
        ++ Γ.flatMap (eGammaClauses (iemE p fuel) (iemA p fuel) Γ C)
        ++ ePlumbClauses (iemE p fuel) Γ C)

/-- Iemhoff's `∀pS`, sequent-indexed, fueled. -/
def iemA (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => falsePLL
  | fuel + 1, Γ, C =>
      orAll (
        (if isAxInst Γ C then [truePLL] else [])
        ++ aGoalClauses p (iemE p fuel) (iemA p fuel) Γ C
        ++ Γ.flatMap (aCtxClauses p (iemE p fuel) (iemA p fuel) Γ C)
        ++ Γ.flatMap (aGammaClauses (iemA p fuel) Γ C))

end

/-! ### p-freeness -/

private theorem mem_atoms_andAll' {x : String} :
    ∀ {l : List PLLFormula}, x ∈ (andAll l).atoms → ∃ φ ∈ l, x ∈ φ.atoms := by
  intro l
  induction l with
  | nil => intro h; simp [andAll, truePLL] at h
  | cons φ l ih =>
      intro h
      simp only [andAll, atoms_and, Finset.mem_union] at h
      rcases h with h | h
      · exact ⟨φ, .head _, h⟩
      · obtain ⟨ψ, hmem, hx⟩ := ih h
        exact ⟨ψ, .tail _ hmem, hx⟩

private theorem mem_atoms_orAll' {x : String} :
    ∀ {l : List PLLFormula}, x ∈ (orAll l).atoms → ∃ φ ∈ l, x ∈ φ.atoms := by
  intro l
  induction l with
  | nil => intro h; simp [orAll] at h
  | cons φ l ih =>
      intro h
      simp only [orAll, atoms_or, Finset.mem_union] at h
      rcases h with h | h
      · exact ⟨φ, .head _, h⟩
      · obtain ⟨ψ, hmem, hx⟩ := ih h
        exact ⟨ψ, .tail _ hmem, hx⟩

/-- p-freeness transfers from the parameter functions to every clause
family; stated once, consumed by the fuel induction below. -/
private theorem pfree_families (p : String)
    (E A : List PLLFormula → PLLFormula → PLLFormula)
    (hE : ∀ Γ C, p ∉ (E Γ C).atoms) (hA : ∀ Γ C, p ∉ (A Γ C).atoms) :
    (∀ Γ φ, φ ∈ eAtomList p Γ → p ∉ φ.atoms) ∧
    (∀ Γ C F φ, φ ∈ eCtxClauses p E A Γ C F → p ∉ φ.atoms) ∧
    (∀ Γ C φ, φ ∈ eGoalClauses p E Γ C → p ∉ φ.atoms) ∧
    (∀ Γ F φ, φ ∈ eOpenClauses E Γ F → p ∉ φ.atoms) ∧
    (∀ Γ C F φ, φ ∈ eGammaClauses E A Γ C F → p ∉ φ.atoms) ∧
    (∀ Γ C φ, φ ∈ ePlumbClauses E Γ C → p ∉ φ.atoms) ∧
    (∀ Γ C φ, φ ∈ aGoalClauses p E A Γ C → p ∉ φ.atoms) ∧
    (∀ Γ C F φ, φ ∈ aCtxClauses p E A Γ C F → p ∉ φ.atoms) ∧
    (∀ Γ C F φ, φ ∈ aGammaClauses A Γ C F → p ∉ φ.atoms) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- eAtomList
    intro Γ φ hφ hx
    obtain ⟨F, hFΓ, hF⟩ := List.mem_filterMap.mp hφ
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | A₁ <;>
      simp only [eAtomList] at hF
    · split at hF
      · simp at hF
      · rename_i hq
        simp only [Option.some.injEq] at hF
        subst hF
        rw [atoms_prop, Finset.mem_singleton] at hx
        exact hq hx.symm
    · simp only [Option.some.injEq] at hF
      subst hF
      simp at hx
    · simp at hF
    · simp at hF
    · simp at hF
    · simp at hF
  · -- eCtxClauses
    intro Γ C F φ hf hx
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [eCtxClauses] at hf
    · simp at hf
    · simp at hf
    · rw [List.mem_singleton] at hf
      subst hf
      exact hE _ _ hx
    · rw [List.mem_singleton] at hf
      subst hf
      rw [atoms_or, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hE _ _ hx
      · exact hE _ _ hx
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hf
      · rcases List.mem_append.mp hf with hf | hf
        · split at hf
          · rw [List.mem_singleton] at hf
            subst hf
            split at hx
            · exact hE _ _ hx
            · rename_i hq
              rw [atoms_and, Finset.mem_union] at hx
              rcases hx with hx | hx
              · rw [atoms_prop, Finset.mem_singleton] at hx
                exact hq hx.symm
              · exact hE _ _ hx
          · simp at hf
        · split at hf
          · simp at hf
          · rename_i hq
            rw [List.mem_singleton] at hf
            subst hf
            rw [atoms_ifThen, Finset.mem_union] at hx
            rcases hx with hx | hx
            · rw [atoms_prop, Finset.mem_singleton] at hx
              exact hq hx.symm
            · exact hE _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        exact hE _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        exact hE _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        exact hE _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        simp only [atoms_and, atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
        · exact hE _ _ hx
      · rcases List.mem_cons.mp hf with rfl | hf
        · simp only [atoms_and, atoms_ifThen, Finset.mem_union] at hx
          rcases hx with hx | hx | hx
          · exact hE _ _ hx
          · exact hA _ _ hx
          · exact hE _ _ hx
        · obtain ⟨X, hXΓ, hXf⟩ := List.mem_filterMap.mp hf
          rcases X with _ | _ | _ | _ | _ | x <;> simp only at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp only [Option.some.injEq] at hXf
            subst hXf
            simp only [atoms_and, atoms_ifThen, atoms_somehow,
              Finset.mem_union] at hx
            rcases hx with hx | hx | hx
            · exact hE _ _ hx
            · exact hA _ _ hx
            · exact hE _ _ hx
    · rcases C with _ | _ | _ | _ | _ | ψ <;> simp only at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · rw [List.mem_singleton] at hf
        subst hf
        rw [atoms_somehow] at hx
        exact hE _ _ hx
  · -- eGoalClauses
    intro Γ C φ hφ hx
    rcases C with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | D <;>
      simp only [eGoalClauses] at hφ
    · simp at hφ
    · simp at hφ
    · rw [List.mem_singleton] at hφ
      subst hφ
      rw [atoms_or, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hE _ _ hx
      · exact hE _ _ hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact hE _ _ hx
      · exact hE _ _ hx
    · split at hφ
      · simp at hφ
      · rename_i hpA
        rw [List.mem_singleton] at hφ
        subst hφ
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hpA hx
        · exact hE _ _ hx
    · rw [List.mem_singleton] at hφ
      subst hφ
      rw [atoms_somehow] at hx
      exact hE _ _ hx
  · -- eOpenClauses
    intro Γ F φ hφ hx
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | α <;>
      simp only [eOpenClauses] at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · rw [List.mem_singleton] at hφ
      subst hφ
      rw [atoms_somehow] at hx
      exact hE _ _ hx
  · -- eGammaClauses
    intro Γ C F φ hφ hx
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [eGammaClauses] at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        simp only [atoms_and, atoms_ifThen, atoms_somehow,
          Finset.mem_union] at hx
        rcases hx with hx | hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
        · exact hE _ _ hx
    · simp at hφ
  · -- ePlumbClauses
    intro Γ C φ hφ hx
    simp only [ePlumbClauses] at hφ
    split at hφ
    · simp at hφ
    · obtain ⟨Θ, _, rfl⟩ := List.mem_map.mp hφ
      exact hE _ _ hx
  · -- aGoalClauses
    intro Γ C φ hφ hx
    rcases C with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | D <;>
      simp only [aGoalClauses] at hφ
    · split at hφ
      · simp at hφ
      · rename_i hq
        rw [List.mem_singleton] at hφ
        subst hφ
        rw [atoms_prop, Finset.mem_singleton] at hx
        exact hq hx.symm
    · simp at hφ
    · rw [List.mem_singleton] at hφ
      subst hφ
      simp only [atoms_and, atoms_ifThen, Finset.mem_union] at hx
      rcases hx with (hx | hx) | (hx | hx)
      · exact hE _ _ hx
      · exact hA _ _ hx
      · exact hE _ _ hx
      · exact hA _ _ hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
    · split at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rename_i hpA
        rw [List.mem_singleton] at hφ
        subst hφ
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hpA hx
        · exact hA _ _ hx
    · rw [List.mem_singleton] at hφ
      subst hφ
      rw [atoms_somehow] at hx
      exact hA _ _ hx
  · -- aCtxClauses
    intro Γ C F φ hf hx
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [aCtxClauses] at hf
    · simp at hf
    · simp at hf
    · rw [List.mem_singleton] at hf
      subst hf
      rw [atoms_ifThen, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact hE _ _ hx
      · exact hA _ _ hx
    · rw [List.mem_singleton] at hf
      subst hf
      simp only [atoms_and, atoms_ifThen, Finset.mem_union] at hx
      rcases hx with (hx | hx) | (hx | hx)
      · exact hE _ _ hx
      · exact hA _ _ hx
      · exact hE _ _ hx
      · exact hA _ _ hx
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hf
      · rcases List.mem_append.mp hf with hf | hf
        · split at hf
          · rw [List.mem_singleton] at hf
            subst hf
            split at hx
            · exact hA _ _ hx
            · rename_i hq
              rw [atoms_ifThen, Finset.mem_union] at hx
              rcases hx with hx | hx
              · rw [atoms_prop, Finset.mem_singleton] at hx
                exact hq hx.symm
              · exact hA _ _ hx
          · simp at hf
        · split at hf
          · simp at hf
          · rename_i hq
            rw [List.mem_singleton] at hf
            subst hf
            rw [atoms_and, Finset.mem_union] at hx
            rcases hx with hx | hx
            · rw [atoms_prop, Finset.mem_singleton] at hx
              exact hq hx.symm
            · exact hA _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        rw [atoms_ifThen, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rw [List.mem_singleton] at hf
        subst hf
        simp only [atoms_and, atoms_ifThen, Finset.mem_union] at hx
        rcases hx with (hx | hx) | (hx | hx)
        · exact hE _ _ hx
        · exact hA _ _ hx
        · exact hE _ _ hx
        · exact hA _ _ hx
      · rcases List.mem_cons.mp hf with rfl | hf
        · rw [atoms_and, Finset.mem_union] at hx
          rcases hx with hx | hx
          · exact hA _ _ hx
          · exact hA _ _ hx
        · obtain ⟨X, hXΓ, hXf⟩ := List.mem_filterMap.mp hf
          rcases X with _ | _ | _ | _ | _ | x <;> simp only at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp only [Option.some.injEq] at hXf
            subst hXf
            simp only [atoms_and, atoms_somehow, Finset.mem_union] at hx
            rcases hx with hx | hx
            · exact hA _ _ hx
            · exact hA _ _ hx
    · rcases C with _ | _ | _ | _ | _ | ψ <;> simp only at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · rw [List.mem_singleton] at hf
        subst hf
        rw [atoms_somehow] at hx
        exact hA _ _ hx
  · -- aGammaClauses
    intro Γ C F φ hφ hx
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [aGammaClauses] at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        simp only [atoms_and, atoms_somehow, Finset.mem_union] at hx
        rcases hx with hx | hx
        · exact hA _ _ hx
        · exact hA _ _ hx
    · simp at hφ

/-- **The quantifiers are p-free.** -/
theorem iem_pfree (p : String) : ∀ (fuel : Nat),
    (∀ Γ C, p ∉ (iemE p fuel Γ C).atoms) ∧
    (∀ Γ C, p ∉ (iemA p fuel Γ C).atoms) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ C h; simp [iemE, truePLL] at h
      · intro Γ C h; simp [iemA] at h
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
        pfree_families p (iemE p fuel) (iemA p fuel) ihE ihA
      constructor
      · intro Γ C hmem
        simp only [iemE] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_andAll' hmem
        rcases List.mem_append.mp hφ with hφ | hplumb
        rotate_left
        · exact h6 _ _ _ hplumb hx
        rcases List.mem_append.mp hφ with hφ | hγ
        rotate_left
        · obtain ⟨F, _, hf⟩ := List.mem_flatMap.mp hγ
          exact h5 _ _ _ _ hf hx
        rcases List.mem_append.mp hφ with hφ | hbox
        rotate_left
        · obtain ⟨F, _, hf⟩ := List.mem_flatMap.mp hbox
          exact h4 _ _ _ hf hx
        rcases List.mem_append.mp hφ with hφ | hgoal
        rotate_left
        · exact h3 _ _ _ hgoal hx
        rcases List.mem_append.mp hφ with hφ | hctx
        rotate_left
        · obtain ⟨F, _, hf⟩ := List.mem_flatMap.mp hctx
          exact h2 _ _ _ _ hf hx
        rcases List.mem_append.mp hφ with hφ | hax
        rotate_left
        · split at hax
          · rw [List.mem_singleton] at hax
            subst hax
            obtain ⟨ψ, hψ, hx⟩ := mem_atoms_andAll' hx
            have hp := (List.mem_filter.mp hψ).2
            simp only [decide_eq_true_eq] at hp
            exact hp hx
          · simp at hax
        · exact h1 _ _ hφ hx
      · intro Γ C hmem
        simp only [iemA] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_orAll' hmem
        rcases List.mem_append.mp hφ with hφ | hγ
        rotate_left
        · obtain ⟨F, _, hf⟩ := List.mem_flatMap.mp hγ
          exact h9 _ _ _ _ hf hx
        rcases List.mem_append.mp hφ with hφ | hctx
        rotate_left
        · obtain ⟨F, _, hf⟩ := List.mem_flatMap.mp hctx
          exact h8 _ _ _ _ hf hx
        rcases List.mem_append.mp hφ with hφ | hgoal
        rotate_left
        · exact h7 _ _ _ hgoal hx
        · split at hφ
          · rw [List.mem_singleton] at hφ
            subst hφ
            simp [truePLL] at hx
          · simp at hφ

/-! ### G4-side admissible glue

Her soundness lemmas (Lemmas 3–6, 7 of the PLL paper; 4.4.1–4.4.7 of
APAL 2019) construct derivations *in the logic*: the recurring step is
"from `Sᵃ ⊢ X` and `Sᵃ, ∀pS ⊢ Sˢ` conclude `Sᵃ, X→∀pS ⊢ Sˢ`" — an
`L→`-application in G3iLL, i.e. cut-strength glue when read inside
G4iLL.  The **retained** form of that rule (G3's `L→`, which keeps
`X→Y` in its own premise) is *not* admissible in G4iLL — it would give
`G3iLL ⊆ G4iLL`, refuted by `PLLG4Gap.sep_not_G4` — but the
**consumed** form is, and the consumed form is all her glue needs:

    guardMP :  Δ ⊢ X   and   Y, Δ ⊢ C   imply   X→Y, Δ ⊢ C.

Lexicographic induction: weight of `X` (for the right-rule cases,
which re-enter at the subformulas over a modified context), then the
derivation of `Δ ⊢ X` (left rules commute, transporting the second
premise through the goal-preserving inversions of `PLLG4Inv.lean`).
The `laxL`-last case is the load-bearing one: it closes *only because*
`impLLaxLax` (her `L◯→`) lets `◯W→Y` consume the very box that `laxL`
was opening — Iemhoff's duplication device is exactly what makes her
own glue admissible in consumed form.  This is the sharpest positive
evidence for the "locally correct" reading of her proof. -/

namespace G4

private theorem swap₁ (a b : PLLFormula) (l : List PLLFormula) :
    (a :: b :: l).Perm (b :: a :: l) := List.Perm.swap b a l

/-- **Consumed-form modus ponens against a context implication.** -/
theorem guardMP : ∀ (n : Nat) {Δ : List PLLFormula} {X : PLLFormula},
    G4 Δ X → X.weight ≤ n → ∀ {Y C : PLLFormula},
    G4 (Y :: Δ) C → G4 (X.ifThen Y :: Δ) C := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHw =>
  intro Δ X d
  induction d with
  | @init Δ a h =>
      intro _ Y C g
      exact .impLProp (List.Perm.refl _) h g
  | @botL Δ X h =>
      intro _ Y C g
      exact .botL (.tail _ h)
  | @andR Δ A B d₁ d₂ ih₁ ih₂ =>
      intro hw Y C g
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A
        simp [PLLFormula.weight] at hw; omega
      exact .impLAnd (List.Perm.refl _)
        (IHw _ hA d₁ le_rfl (IHw _ hB d₂ le_rfl g))
  | @orR1 Δ A B d₁ ih₁ =>
      intro hw Y C g
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      refine .impLOr (List.Perm.refl _) ?_
      exact IHw _ hA (d₁.weaken (B.ifThen Y)) le_rfl
        ((g.weaken (B.ifThen Y)).perm (swap₁ _ _ _))
  | @orR2 Δ A B d₁ ih₁ =>
      intro hw Y C g
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A
        simp [PLLFormula.weight] at hw; omega
      refine .impLOr (List.Perm.refl _) ?_
      refine (IHw _ hB (d₁.weaken (A.ifThen Y)) le_rfl
        ((g.weaken (A.ifThen Y)).perm (swap₁ _ _ _))).perm (swap₁ _ _ _)
  | @impR Δ A B d₁ ih₁ =>
      intro _ Y C g
      refine .impLImp (List.Perm.refl _) ?_ g
      exact .impR ((d₁.weaken (B.ifThen Y)).perm (swap₁ _ _ _))
  | @laxR Δ A d₁ ih₁ =>
      intro _ Y C g
      exact .impLLax (List.Perm.refl _) d₁ g
  | @laxL Δ Δ' A W h d₁ ih₁ =>
      intro _ Y C g
      exact .impLLaxLax (h.cons _) d₁ (g.perm (h.cons _))
  | @andL Δ Δ' A B X h d₁ ih₁ =>
      intro hw Y C g
      have g' : G4 (Y :: A :: B :: Δ') C :=
        (g.inv (.and A B) ((h.cons _).trans (swap₁ _ _ _))).perm
          (((swap₁ _ _ _).cons _).trans (swap₁ _ _ _))
      refine .andL ((h.cons _).trans (swap₁ _ _ _)) ?_
      exact (ih₁ hw g').perm ((swap₁ _ _ _).trans ((swap₁ _ _ _).cons _))
  | @orL Δ Δ' A B X h d₁ d₂ ih₁ ih₂ =>
      intro hw Y C g
      have g₁ : G4 (Y :: A :: Δ') C :=
        (g.inv (.or₁ A B) ((h.cons _).trans (swap₁ _ _ _))).perm (swap₁ _ _ _)
      have g₂ : G4 (Y :: B :: Δ') C :=
        (g.inv (.or₂ A B) ((h.cons _).trans (swap₁ _ _ _))).perm (swap₁ _ _ _)
      refine .orL ((h.cons _).trans (swap₁ _ _ _)) ?_ ?_
      · exact (ih₁ hw g₁).perm (swap₁ _ _ _)
      · exact (ih₂ hw g₂).perm (swap₁ _ _ _)
  | @impLProp Δ Δ' a B X h ha d₁ ih₁ =>
      intro hw Y C g
      have g' : G4 (Y :: B :: Δ') C :=
        (g.inv (.impProp a B) ((h.cons _).trans (swap₁ _ _ _))).perm
          (swap₁ _ _ _)
      refine .impLProp ((h.cons _).trans (swap₁ _ _ _)) (.tail _ ha) ?_
      exact (ih₁ hw g').perm (swap₁ _ _ _)
  | @impLBot Δ Δ' B X h d₁ ih₁ =>
      intro hw Y C g
      have g' : G4 (Y :: Δ') C :=
        g.inv (.impBot B) ((h.cons _).trans (swap₁ _ _ _))
      exact .impLBot ((h.cons _).trans (swap₁ _ _ _)) (ih₁ hw g')
  | @impLAnd Δ Δ' A B D X h d₁ ih₁ =>
      intro hw Y C g
      have g' : G4 (Y :: A.ifThen (B.ifThen D) :: Δ') C :=
        (g.inv (.impAnd A B D) ((h.cons _).trans (swap₁ _ _ _))).perm
          (swap₁ _ _ _)
      refine .impLAnd ((h.cons _).trans (swap₁ _ _ _)) ?_
      exact (ih₁ hw g').perm (swap₁ _ _ _)
  | @impLOr Δ Δ' A B D X h d₁ ih₁ =>
      intro hw Y C g
      have g' : G4 (Y :: A.ifThen D :: B.ifThen D :: Δ') C :=
        (g.inv (.impOr A B D) ((h.cons _).trans (swap₁ _ _ _))).perm
          (((swap₁ _ _ _).cons _).trans (swap₁ _ _ _))
      refine .impLOr ((h.cons _).trans (swap₁ _ _ _)) ?_
      exact (ih₁ hw g').perm ((swap₁ _ _ _).trans ((swap₁ _ _ _).cons _))
  | @impLImp Δ Δ' A B D X h d₁ d₂ ih₁ ih₂ =>
      intro hw Y C g
      have g' : G4 (Y :: D :: Δ') C :=
        (g.inv (.impImp A B D) ((h.cons _).trans (swap₁ _ _ _))).perm
          (swap₁ _ _ _)
      refine .impLImp ((h.cons _).trans (swap₁ _ _ _)) ?_ ?_
      · exact (d₁.weaken (X.ifThen Y)).perm (swap₁ _ _ _)
      · exact (ih₂ hw g').perm (swap₁ _ _ _)
  | @impLLax Δ Δ' A B X h d₁ d₂ ih₁ ih₂ =>
      intro hw Y C g
      have g' : G4 (Y :: B :: Δ') C :=
        (g.inv (.impLax A B) ((h.cons _).trans (swap₁ _ _ _))).perm
          (swap₁ _ _ _)
      refine .impLLax ((h.cons _).trans (swap₁ _ _ _)) ?_ ?_
      · exact d₁.weaken (X.ifThen Y)
      · exact (ih₂ hw g').perm (swap₁ _ _ _)
  | @impLLaxLax Δ Δ' A B W X h d₁ d₂ ih₁ ih₂ =>
      intro hw Y C g
      have g' : G4 (Y :: B :: W.somehow :: Δ') C :=
        (g.inv (.impLax A B) ((h.cons _).trans (swap₁ _ _ _))).perm
          (swap₁ _ _ _)
      refine .impLLaxLax
        ((h.cons _).trans ((swap₁ _ _ _).trans ((swap₁ _ _ _).cons _))) ?_ ?_
      · exact (d₁.weaken (X.ifThen Y)).perm (swap₁ _ _ _)
      · exact (ih₂ hw g').perm ((swap₁ _ _ _).trans ((swap₁ _ _ _).cons _))

/-- `guardMP`, packaged: fire a context implication whose antecedent
the rest of the context derives. -/
theorem mp {Γ Δ : List PLLFormula} {X Y C : PLLFormula}
    (hp : Γ.Perm (X.ifThen Y :: Δ))
    (dX : G4 Δ X) (dY : G4 (Y :: Δ) C) : G4 Γ C :=
  (guardMP X.weight dX le_rfl dY).perm hp.symm

/-- **General identity** `Γ, φ ⊢ φ`, strong induction on weight; the
`∧→`/`∨→` antecedent cases consume `guardMP`, the `◯→` case fires
`impLLaxLax` with the freshly introduced `◯A` as its own witness. -/
theorem iden : ∀ (n : Nat) (φ : PLLFormula), φ.weight ≤ n →
    ∀ (Γ : List PLLFormula), G4 (φ :: Γ) φ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro φ hw Γ
  match φ with
  | .prop a => exact .init (.head _)
  | .falsePLL => exact .botL (.head _)
  | .and A B =>
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A
        simp [PLLFormula.weight] at hw; omega
      refine .andL (List.Perm.refl _) (.andR ?_ ?_)
      · exact IH _ hA A le_rfl (B :: Γ)
      · exact (IH _ hB B le_rfl (A :: Γ)).perm (swap₁ _ _ _)
  | .or A B =>
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A
        simp [PLLFormula.weight] at hw; omega
      exact .orL (List.Perm.refl _)
        (.orR1 (IH _ hA A le_rfl Γ)) (.orR2 (IH _ hB B le_rfl Γ))
  | .somehow A =>
      have hA : A.weight < n := by
        simp [PLLFormula.weight] at hw; omega
      exact .laxL (List.Perm.refl _) (.laxR (IH _ hA A le_rfl Γ))
  | .ifThen (.prop a) B =>
      have hB : B.weight < n := by
        simp [PLLFormula.weight] at hw; omega
      exact .impR (.impLProp (swap₁ _ _ _) (.head _)
        (IH _ hB B le_rfl (prop a :: Γ)))
  | .ifThen .falsePLL B =>
      exact .impR (.botL (.head _))
  | .ifThen (.and A B) D =>
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B; have := PLLFormula.weight_pos D
        simp [PLLFormula.weight] at hw; omega
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A; have := PLLFormula.weight_pos D
        simp [PLLFormula.weight] at hw; omega
      have hD : D.weight < n := by
        have := PLLFormula.weight_pos A; have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      refine .impR (.impLAnd (swap₁ _ _ _) (.andL (swap₁ _ _ _) ?_))
      -- A :: B :: A→(B→D) :: Γ ⊢ D : two consumed-form MPs
      refine G4.mp (Δ := A :: B :: Γ)
        (((swap₁ _ _ _).cons _).trans (swap₁ _ _ _)) ?_ ?_
      · exact IH _ hA A le_rfl (B :: Γ)
      · exact G4.mp (List.Perm.refl _)
          ((IH _ hB B le_rfl (A :: Γ)).perm (swap₁ _ _ _))
          (IH _ hD D le_rfl (A :: B :: Γ))
  | .ifThen (.or A B) D =>
      have hA : A.weight < n := by
        have := PLLFormula.weight_pos B; have := PLLFormula.weight_pos D
        simp [PLLFormula.weight] at hw; omega
      have hB : B.weight < n := by
        have := PLLFormula.weight_pos A; have := PLLFormula.weight_pos D
        simp [PLLFormula.weight] at hw; omega
      have hD : D.weight < n := by
        have := PLLFormula.weight_pos A; have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw; omega
      refine .impR (.impLOr (swap₁ _ _ _) ?_)
      -- A→D :: B→D :: A∨B :: Γ ⊢ D
      refine .orL (Δ := A.ifThen D :: B.ifThen D :: Γ)
        (((swap₁ _ _ _).cons _).trans (swap₁ _ _ _)) ?_ ?_
      · -- A :: A→D :: B→D :: Γ ⊢ D
        refine G4.mp (Δ := A :: (B.ifThen D) :: Γ) (swap₁ _ _ _) ?_ ?_
        · exact IH _ hA A le_rfl (B.ifThen D :: Γ)
        · exact IH _ hD D le_rfl (A :: B.ifThen D :: Γ)
      · -- B :: A→D :: B→D :: Γ ⊢ D
        refine G4.mp (Δ := B :: (A.ifThen D) :: Γ)
          (((swap₁ _ _ _).cons _).trans (swap₁ _ _ _)) ?_ ?_
        · exact IH _ hB B le_rfl (A.ifThen D :: Γ)
        · exact IH _ hD D le_rfl (B :: A.ifThen D :: Γ)
  | .ifThen (.ifThen A B) D =>
      have h₁ : (A.ifThen B).weight < n := by
        have := PLLFormula.weight_pos D
        simp [PLLFormula.weight] at hw ⊢; omega
      have h₂ : D.weight < n := by
        have := PLLFormula.weight_pos A; have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw ⊢; omega
      refine .impR (.impLImp (swap₁ _ _ _) ?_ ?_)
      · exact (IH _ h₁ (A.ifThen B) le_rfl (B.ifThen D :: Γ)).perm
          (swap₁ _ _ _)
      · exact IH _ h₂ D le_rfl (A.ifThen B :: Γ)
  | .ifThen (.somehow A) B =>
      have h₁ : A.weight < n := by
        have := PLLFormula.weight_pos B
        simp [PLLFormula.weight] at hw ⊢; omega
      have h₂ : B.weight < n := by
        have := PLLFormula.weight_pos A
        simp [PLLFormula.weight] at hw ⊢; omega
      refine .impR (.impLLaxLax (Δ := Γ) (swap₁ _ _ _) ?_ ?_)
      · exact .laxR (IH _ h₁ A le_rfl Γ)
      · exact IH _ h₂ B le_rfl (A.somehow :: Γ)

/-- Identity from membership: `ψ ∈ Γ → Γ ⊢ ψ`. -/
theorem ofMem {Γ : List PLLFormula} {ψ : PLLFormula} (h : ψ ∈ Γ) : G4 Γ ψ :=
  (iden ψ.weight ψ le_rfl (Γ.erase ψ)).perm (List.perm_cons_erase h).symm

theorem truePLL_intro (Γ : List PLLFormula) : G4 Γ truePLL :=
  .impR (.botL (.head _))

theorem andAll_intro : ∀ {l : List PLLFormula} {Γ : List PLLFormula},
    (∀ φ ∈ l, G4 Γ φ) → G4 Γ (andAll l) := by
  intro l
  induction l with
  | nil => intro Γ _; exact truePLL_intro Γ
  | cons φ l ih =>
      intro Γ h
      exact .andR (h φ (.head _)) (ih fun ψ hψ => h ψ (.tail _ hψ))

theorem orAll_intro : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Γ : List PLLFormula}, G4 Γ φ → G4 Γ (orAll l) := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Γ h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact .orR1 h
      · exact .orR2 (ih hmem' h)

theorem andAll_elim : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Δ : List PLLFormula} {D : PLLFormula},
    G4 (φ :: Δ) D → G4 (andAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Δ D h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact .andL (List.Perm.refl _)
          ((h.weaken (andAll l)).perm
            ((swap₁ _ _ _).trans (List.Perm.refl _)))
      · refine .andL (List.Perm.refl _) ?_
        have := ih hmem' (Δ := x :: Δ) (D := D)
          ((h.weaken x).perm (swap₁ _ _ _))
        exact this.perm (swap₁ _ _ _)

theorem orAll_elim : ∀ {l : List PLLFormula} {Δ : List PLLFormula}
    {D : PLLFormula}, (∀ φ ∈ l, G4 (φ :: Δ) D) →
    G4 (orAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro Δ D _; exact .botL (.head _)
  | cons x l ih =>
      intro Δ D h
      exact .orL (List.Perm.refl _) (h x (.head _))
        (ih fun ψ hψ => h ψ (.tail _ hψ))

/-- Weaken along a sublist. -/
theorem weaken_sublist {Θ Γ : List PLLFormula} {C : PLLFormula}
    (hsub : Θ.Sublist Γ) (d : G4 Θ C) : G4 Γ C := by
  obtain ⟨l, hl⟩ := hsub.exists_perm_append
  exact (d.weakens l).perm ((hl.trans List.perm_append_comm).symm)

/-- Weaken by one formula in second position. -/
theorem weaken₂ {Γ : List PLLFormula} {A C : PLLFormula} (ψ : PLLFormula)
    (d : G4 (A :: Γ) C) : G4 (A :: ψ :: Γ) C :=
  (d.weaken ψ).perm (swap₁ _ _ _)

/-- Move the third element to the front. -/
private theorem rot₃ (a b c : PLLFormula) (l : List PLLFormula) :
    (a :: b :: c :: l).Perm (c :: a :: b :: l) :=
  ((swap₁ b c l).cons a).trans (swap₁ a c (b :: l))

end G4

/-! ### E1/A1 — her independent interpolant properties, in-habitat

Her (∃r): `⊢ Sᵃ ⇒ ∃pS`, and (∀l): `⊢ Sᵃ, ∀pS ⇒ Sˢ`, with `⊢` read as
**G4iLL-derivability** (no cut).  Both are proved per clause family
against abstract one-level-down values, then tied by fuel induction.
Every case is closed by rules + weakening + `G4.mp` (consumed-form MP)
+ `iden` — with **one exception**, sorry-isolated and analyzed below:
her `L4→` assignment's first conjunct `∃pS₁`.  -/

section Sound

variable {p : String} {E A : List PLLFormula → PLLFormula → PLLFormula}

private theorem eSound
    (hE : ∀ Γ C, G4 Γ (E Γ C))
    (hA : ∀ Γ C, G4 (A Γ C :: Γ) C) :
    (∀ Γ C F, F ∈ Γ → ∀ φ ∈ eCtxClauses p E A Γ C F, G4 Γ φ) ∧
    (∀ Γ C φ, φ ∈ eGoalClauses p E Γ C → G4 Γ φ) ∧
    (∀ Γ F, F ∈ Γ → ∀ φ ∈ eOpenClauses E Γ F, G4 Γ φ) ∧
    (∀ Γ C F, F ∈ Γ → ∀ φ ∈ eGammaClauses E A Γ C F, G4 Γ φ) ∧
    (∀ Γ C φ, φ ∈ ePlumbClauses E Γ C → G4 Γ φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- eCtxClauses
    intro Γ C F hFΓ φ hf
    have pF := List.perm_cons_erase hFΓ
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [eCtxClauses] at hf
    · simp at hf
    · simp at hf
    · -- L∧
      rw [List.mem_singleton] at hf
      subst hf
      exact .andL pF (hE _ _)
    · -- L∨
      rw [List.mem_singleton] at hf
      subst hf
      exact .orL pF (.orR1 (hE _ _)) (.orR2 (hE _ _))
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hf
      · -- L1→ instance + ∃ᵃᵗ family
        rcases List.mem_append.mp hf with hf | hf
        · split at hf
          · rename_i hqm
            rw [List.mem_singleton] at hf
            subst hf
            split
            · exact .impLProp pF hqm (hE _ _)
            · exact .andR (.init (List.mem_of_mem_erase hqm))
                (.impLProp pF hqm (hE _ _))
          · simp at hf
        · split at hf
          · simp at hf
          · rw [List.mem_singleton] at hf
            subst hf
            refine .impR (.impLProp ((pF.cons _).trans (G4.swap₁ _ _ _))
              (.head _) ?_)
            exact G4.weaken₂ _ (hE _ _)
      · -- L⊥→ (flagged repo extension)
        rw [List.mem_singleton] at hf
        subst hf
        exact .impLBot pF (hE _ _)
      · -- L2→
        rw [List.mem_singleton] at hf
        subst hf
        exact .impLAnd pF (hE _ _)
      · -- L3→
        rw [List.mem_singleton] at hf
        subst hf
        exact .impLOr pF (hE _ _)
      · -- L4→ : her ι∃ᴿ = ∃pS₁ ∧ (∀pS₁ → ∃pS₂)
        rw [List.mem_singleton] at hf
        subst hf
        refine .andR ?_ ?_
        · -- **HOLDOUT (∃r)-L4→-(i)**: `Γ ⊢ ∃pS₁` with
          -- `S₁ = (B₂→D, Γ∖F ⇒ A₂→B₂)`, `F = (A₂→B₂)→D ∈ Γ`.
          -- Her proof (APAL 2019, p.26): "we use the obvious fact
          -- that ⊢ ⋀Sᵃ → ⋀S₁ᵃ" and composes — context replacement
          -- along a derivable implication, i.e. CUT, unavailable in
          -- G4iLL (PLLG4Gap.cut_not_admissible).  No G4iLL rule
          -- reaches the context `B₂→D, Γ∖F` without changing the
          -- goal (impLImp forces goal `A₂→B₂`), so the IH does not
          -- apply; this is the unique clause whose premise context
          -- is neither a subcontext of `Γ` nor rule-reachable.
          -- Pitts'/UIML's clause for the same rule is the *guarded*
          -- `(E(S₁) → A(S₁)) → E(D,Γ∖F)`, which IS in-habitat
          -- provable (fire impLImp; G4.mp the guard with dX := IH-E
          -- at S₁ — exact) — her deviation from Pitts' shape is the
          -- precise local obstruction.
          sorry
        · refine .impR (.impLImp ((pF.cons _).trans (G4.swap₁ _ _ _))
            ?_ ?_)
          · exact (hA _ _).perm (G4.swap₁ _ _ _)
          · exact G4.weaken₂ _ (hE _ _)
      · -- R◯→ head + L◯→ witnesses
        rcases List.mem_cons.mp hf with rfl | hf
        · refine .andR (((hE _ _).weaken _).perm pF.symm) ?_
          refine .impR (.impLLax ((pF.cons _).trans (G4.swap₁ _ _ _))
            ?_ ?_)
          · exact hA _ _
          · exact G4.weaken₂ _ (hE _ _)
        · obtain ⟨X, hXΓ', hXf⟩ := List.mem_filterMap.mp hf
          rcases X with _ | _ | _ | _ | _ | x <;> simp only at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp only [Option.some.injEq] at hXf
            subst hXf
            have hxΓ : x.somehow ∈ Γ := List.mem_of_mem_erase hXΓ'
            have pX := List.perm_cons_erase hXΓ'
            refine .andR ?_ ?_
            · -- Γ ⊢ ◯ E(x, Γ'' ⇒ ◯A₂)
              refine .laxL (List.perm_cons_erase hxΓ) (.laxR ?_)
              have hFx : (α.somehow.ifThen B₁) ∈ Γ.erase x.somehow := by
                rw [List.mem_erase_of_ne (by simp)]
                exact hFΓ
              have : ((α.somehow.ifThen B₁) ::
                  ((Γ.erase x.somehow).erase (α.somehow.ifThen B₁))).Perm
                  (Γ.erase x.somehow) :=
                (List.perm_cons_erase hFx).symm
              rw [List.erase_comm] at this
              exact (G4.weaken₂ _ (hE _ _)).perm (this.cons x)
            · refine .impR (.impLLaxLax
                ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_ ?_)
              · refine (G4.perm ?_ ((pX.cons _).trans (G4.swap₁ _ _ _)).symm)
                exact .laxL (List.Perm.refl _) ((hA _ _).perm (G4.swap₁ _ _ _))
              · exact G4.weaken₂ _ (hE _ _)
    · -- L◯ instance (C = ◯ψ)
      rcases C with _ | _ | _ | _ | _ | ψ <;> simp only at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · rw [List.mem_singleton] at hf
        subst hf
        exact .laxL pF (.laxR (hE _ _))
  · -- eGoalClauses
    intro Γ C φ hφ
    rcases C with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | D <;>
      simp only [eGoalClauses] at hφ
    · simp at hφ
    · simp at hφ
    · rw [List.mem_singleton] at hφ
      subst hφ
      exact .orR1 (hE _ _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact hE _ _
      · exact hE _ _
    · split at hφ
      · simp at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        exact .impR (hE _ _)
    · rw [List.mem_singleton] at hφ
      subst hφ
      exact .laxR (hE _ _)
  · -- eOpenClauses
    intro Γ F hFΓ φ hφ
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | α <;>
      simp only [eOpenClauses] at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · rw [List.mem_singleton] at hφ
      subst hφ
      exact .laxL (List.perm_cons_erase hFΓ) (.laxR (hE _ _))
  · -- eGammaClauses: the self-witnessing γ-form
    intro Γ C F hFΓ φ hφ
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [eGammaClauses] at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · simp at hφ
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · simp at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        have pF := List.perm_cons_erase hFΓ
        refine .andR (((hE _ _).weaken _).perm pF.symm) ?_
        refine .impR (.impLLaxLax ((pF.cons _).trans (G4.swap₁ _ _ _))
          ?_ ?_)
        · exact hA _ _
        · exact G4.weaken₂ _ (hE _ _)
    · simp at hφ
  · -- ePlumbClauses
    intro Γ C φ hφ
    simp only [ePlumbClauses] at hφ
    split at hφ
    · simp at hφ
    · obtain ⟨Θ, hΘ, rfl⟩ := List.mem_map.mp hφ
      exact G4.weaken_sublist (List.mem_sublists.mp hΘ) (hE _ _)

private theorem aSound
    (hE : ∀ Γ C, G4 Γ (E Γ C))
    (hA : ∀ Γ C, G4 (A Γ C :: Γ) C) :
    (∀ Γ C φ, φ ∈ aGoalClauses p E A Γ C → G4 (φ :: Γ) C) ∧
    (∀ Γ C F, F ∈ Γ → ∀ φ ∈ aCtxClauses p E A Γ C F, G4 (φ :: Γ) C) ∧
    (∀ Γ C F, F ∈ Γ → ∀ φ ∈ aGammaClauses A Γ C F, G4 (φ :: Γ) C) := by
  refine ⟨?_, ?_, ?_⟩
  · -- aGoalClauses
    intro Γ C φ hφ
    rcases C with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | D <;>
      simp only [aGoalClauses] at hφ
    · split at hφ
      · simp at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        exact .init (.head _)
    · simp at hφ
    · -- C = A₁ ∧ B₁
      rw [List.mem_singleton] at hφ
      subst hφ
      refine .andL (List.Perm.refl _) (.andR ?_ ?_)
      · exact G4.mp (List.Perm.refl _) ((hE Γ A₁).weaken _)
          (G4.weaken₂ _ (hA Γ A₁))
      · exact G4.mp (G4.swap₁ _ _ _) ((hE Γ B₁).weaken _)
          (G4.weaken₂ _ (hA Γ B₁))
    · -- C = A₁ ∨ B₁
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact G4.mp (List.Perm.refl _) (hE Γ A₁) (.orR1 (hA Γ A₁))
      · exact G4.mp (List.Perm.refl _) (hE Γ B₁) (.orR2 (hA Γ B₁))
    · -- C = A₁ → B₁
      split at hφ
      · rw [List.mem_singleton] at hφ
        subst hφ
        refine .impR (G4.perm ?_ (G4.swap₁ _ _ _))
        exact G4.mp (List.Perm.refl _) (hE _ _) (hA _ _)
      · rw [List.mem_singleton] at hφ
        subst hφ
        refine .impR (G4.perm ?_ (G4.swap₁ _ _ _))
        exact G4.mp (List.Perm.refl _) (G4.ofMem (.head _)) (hA _ _)
    · -- C = ◯D
      rw [List.mem_singleton] at hφ
      subst hφ
      exact .laxL (List.Perm.refl _) (.laxR (hA Γ D))
  · -- aCtxClauses
    intro Γ C F hFΓ φ hf
    have pF := List.perm_cons_erase hFΓ
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [aCtxClauses] at hf
    · simp at hf
    · simp at hf
    · -- L∧
      rw [List.mem_singleton] at hf
      subst hf
      refine .andL ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_
      refine G4.perm ?_ (G4.rot₃ _ _ _ _).symm
      exact G4.mp (List.Perm.refl _) (hE _ _) (hA _ _)
    · -- L∨
      rw [List.mem_singleton] at hf
      subst hf
      refine .orL ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_ ?_
      · refine G4.perm ?_ (G4.swap₁ _ _ _)
        refine .andL (List.Perm.refl _) ?_
        exact G4.mp (List.Perm.refl _) ((hE _ _).weaken _)
          (G4.weaken₂ _ (hA _ _))
      · refine G4.perm ?_ (G4.swap₁ _ _ _)
        refine .andL (List.Perm.refl _) ?_
        exact G4.mp (G4.swap₁ _ _ _) ((hE _ _).weaken _)
          (G4.weaken₂ _ (hA _ _))
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hf
      · -- L1→ instance + ∀ᵃᵗ family
        rcases List.mem_append.mp hf with hf | hf
        · split at hf
          · rename_i hqm
            rw [List.mem_singleton] at hf
            subst hf
            split
            · refine .impLProp ((pF.cons _).trans (G4.swap₁ _ _ _))
                (.tail _ hqm) ?_
              exact (hA _ _).perm (G4.swap₁ _ _ _)
            · refine .impLProp ((pF.cons _).trans (G4.swap₁ _ _ _))
                (.tail _ hqm) ?_
              refine G4.perm ?_ (G4.swap₁ _ _ _)
              exact G4.mp (List.Perm.refl _)
                (G4.ofMem (.tail _ hqm)) (hA _ _)
          · simp at hf
        · split at hf
          · simp at hf
          · rw [List.mem_singleton] at hf
            subst hf
            refine .andL (List.Perm.refl _) ?_
            refine .impLProp (((pF.cons _).cons _).trans (G4.rot₃ _ _ _ _))
              (.head _) ?_
            exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _)
      · -- L⊥→
        rw [List.mem_singleton] at hf
        subst hf
        refine .impLBot ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_
        exact G4.mp (List.Perm.refl _) (hE _ _) (hA _ _)
      · -- L2→
        rw [List.mem_singleton] at hf
        subst hf
        refine .impLAnd ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_
        refine G4.perm ?_ (G4.swap₁ _ _ _)
        exact G4.mp (List.Perm.refl _) (hE _ _) (hA _ _)
      · -- L3→
        rw [List.mem_singleton] at hf
        subst hf
        refine .impLOr ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_
        refine G4.perm ?_ (G4.rot₃ _ _ _ _).symm
        exact G4.mp (List.Perm.refl _) (hE _ _) (hA _ _)
      · -- L4→ : ⋀ᵢ (∃pSᵢ → ∀pSᵢ)
        rw [List.mem_singleton] at hf
        subst hf
        refine .andL (List.Perm.refl _) ?_
        refine .impLImp (((pF.cons _).cons _).trans (G4.rot₃ _ _ _ _))
          ?_ ?_
        · refine G4.mp (G4.swap₁ _ _ _) (G4.weaken₂ _ (hE _ _)) ?_
          exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _).symm
        · refine G4.mp (G4.rot₃ _ _ _ _) (G4.weaken₂ _ (hE _ _)) ?_
          exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _).symm
      · -- R◯→ head + L◯→ witnesses
        rcases List.mem_cons.mp hf with rfl | hf
        · refine .andL (List.Perm.refl _) ?_
          refine .impLLax (((pF.cons _).cons _).trans (G4.rot₃ _ _ _ _))
            ?_ ?_
          · exact G4.weaken₂ _ (hA _ _)
          · exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _)
        · obtain ⟨X, hXΓ', hXf⟩ := List.mem_filterMap.mp hf
          rcases X with _ | _ | _ | _ | _ | x <;> simp only at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp at hXf
          · simp only [Option.some.injEq] at hXf
            subst hXf
            have pX := List.perm_cons_erase hXΓ'
            refine .andL (List.Perm.refl _) ?_
            refine .impLLaxLax
              (((pF.cons _).cons _).trans (G4.rot₃ _ _ _ _)) ?_ ?_
            · refine .laxL (((pX.cons _).cons _).trans (G4.rot₃ _ _ _ _)) ?_
              exact ((hA _ _).weaken _).perm
                ((G4.rot₃ _ _ _ _).trans ((G4.swap₁ _ _ _).cons _))
            · exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _)
    · -- L◯ (C = ◯ψ)
      rcases C with _ | _ | _ | _ | _ | ψ <;> simp only at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · rw [List.mem_singleton] at hf
        subst hf
        refine .laxL (List.Perm.refl _) ?_
        refine .laxL ((pF.cons _).trans (G4.swap₁ _ _ _)) ?_
        exact (hA _ _).perm (G4.swap₁ _ _ _)
  · -- aGammaClauses
    intro Γ C F hFΓ φ hf
    rcases F with q | _ | ⟨A₁, B₁⟩ | ⟨A₁, B₁⟩ | ⟨Ant, B₁⟩ | χ <;>
      simp only [aGammaClauses] at hf
    · simp at hf
    · simp at hf
    · simp at hf
    · simp at hf
    · rcases Ant with q | _ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | ⟨A₂, B₂⟩ | α <;>
        simp only at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · simp at hf
      · rw [List.mem_singleton] at hf
        subst hf
        have pF := List.perm_cons_erase hFΓ
        refine .andL (List.Perm.refl _) ?_
        refine .impLLaxLax
          (((pF.cons _).cons _).trans (G4.rot₃ _ _ _ _)) ?_ ?_
        · exact G4.weaken₂ _ (hA _ _)
        · exact ((hA _ _).weaken _).perm (G4.rot₃ _ _ _ _)
    · simp at hf

end Sound

private theorem axInst_cases {Γ : List PLLFormula} {C : PLLFormula}
    (h : isAxInst Γ C = true) : falsePLL ∈ Γ ∨ C ∈ Γ := by
  cases C <;> simp_all [isAxInst]

/-- **E1/A1 in-habitat** (her independent interpolant properties (∃r)
and (∀l), with `⊢` = G4iLL-derivability, no cut): modulo the single
sorry-isolated `(∃r)-L4→-(i)` conjunct inside `eSound`. -/
theorem iem_sound (p : String) : ∀ (fuel : Nat),
    (∀ Γ C, G4 Γ (iemE p fuel Γ C)) ∧
    (∀ Γ C, G4 (iemA p fuel Γ C :: Γ) C) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ C
        exact G4.truePLL_intro Γ
      · intro Γ C
        exact .botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      obtain ⟨e2, e3, e4, e5, e6⟩ := eSound (p := p) ihE ihA
      obtain ⟨a2, a3, a4⟩ := aSound (p := p) ihE ihA
      constructor
      · intro Γ C
        simp only [iemE]
        refine G4.andAll_intro ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hplumb
        rotate_left
        · exact e6 _ _ _ hplumb
        rcases List.mem_append.mp hφ with hφ | hγ
        rotate_left
        · obtain ⟨F, hFΓ, hf⟩ := List.mem_flatMap.mp hγ
          exact e5 _ _ _ hFΓ _ hf
        rcases List.mem_append.mp hφ with hφ | hbox
        rotate_left
        · obtain ⟨F, hFΓ, hf⟩ := List.mem_flatMap.mp hbox
          exact e4 _ _ hFΓ _ hf
        rcases List.mem_append.mp hφ with hφ | hgoal
        rotate_left
        · exact e3 _ _ _ hgoal
        rcases List.mem_append.mp hφ with hφ | hctx
        rotate_left
        · obtain ⟨F, hFΓ, hf⟩ := List.mem_flatMap.mp hctx
          exact e2 _ _ _ hFΓ _ hf
        rcases List.mem_append.mp hφ with hφ | hax
        rotate_left
        · split at hax
          · rw [List.mem_singleton] at hax
            subst hax
            refine G4.andAll_intro ?_
            intro ψ hψ
            exact G4.ofMem (List.mem_filter.mp hψ).1
          · simp at hax
        · obtain ⟨F, hFΓ, hF⟩ := List.mem_filterMap.mp hφ
          rcases F with q | _ | _ | _ | _ | _ <;>
            simp only [eAtomList] at hF
          · split at hF
            · simp at hF
            · simp only [Option.some.injEq] at hF
              subst hF
              exact .init hFΓ
          · simp only [Option.some.injEq] at hF
            subst hF
            exact .botL hFΓ
          · simp at hF
          · simp at hF
          · simp at hF
          · simp at hF
      · intro Γ C
        simp only [iemA]
        refine G4.orAll_elim ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hγ
        rotate_left
        · obtain ⟨F, hFΓ, hf⟩ := List.mem_flatMap.mp hγ
          exact a4 _ _ _ hFΓ _ hf
        rcases List.mem_append.mp hφ with hφ | hctx
        rotate_left
        · obtain ⟨F, hFΓ, hf⟩ := List.mem_flatMap.mp hctx
          exact a3 _ _ _ hFΓ _ hf
        rcases List.mem_append.mp hφ with hφ | hgoal
        rotate_left
        · exact a2 _ _ _ hgoal
        · split at hφ
          next hax =>
            rw [List.mem_singleton] at hφ
            subst hφ
            rcases axInst_cases hax with hb | hc
            · exact .botL (.tail _ hb)
            · exact (G4.ofMem hc).weaken _
          next => simp at hφ

/-! ### Adequacy — her (∀∃), read in-habitat

Her dependent property (∀∃): if `S` is derivable then for every
p-partition `(Sʳ, Sⁱ)`, `⊢ Sʳ · (∃pSⁱ ⇒ ∀pSⁱ | ∅)`.  In the
dictionary this is the Pitts pair: for a G4iLL-derivation of
`Γ ∪ Δ ⊢ C` with `Δ` p-free,

* (E)  `p ∉ C` →  `iemE p _ Γ ⊥, Δ ⊢ C`          (`C` on the r-side)
* (A)  `iemE p _ Γ C, Δ ⊢ iemA p _ Γ C`          (`C` on the i-side)

by induction on the derivation (her Lemma 7 inducts on derivation
depth for the modal rules; the centered/G4ip rules ride the 2019
paper).  The fuel is threaded existentially (`∀ fuel > n`) — with her
strictly-descending tables each premise IH is consumed one level
down, so no fuel monotonicity and no `E_step`-style cut is needed
anywhere, in sharp contrast to the retention calculus's P4a.

**Status of the case analysis** (see the sorry-side notes):

* the two-sided bookkeeping and the right rules land exactly as in
  her text, consumed-form `G4.mp` replacing every logic-level glue
  step — no cut needed;
* `laxL` with the box on the **Δ-side and the succedent on the
  i-side** — her (DPN)-L◯ *first case* — is **flawed in her paper**:
  she writes "an application of L◯ gives ⊢ Γʳ,◯ψ,∃pSⁱ ⇒ ◯φ, and
  since S₁ⁱ = Sⁱ this is what we had to show", but the stated target
  of that case is `Γʳ,◯ψ,∃pSⁱ ⇒ ∀pSⁱ` (her own case split, three
  lines above), and `L◯` cannot close `ψ ⟿ ◯ψ` under the non-circle
  succedent `∀pSⁱ`.  The repair known from the repo's retention
  development (v2/v3's self-referential ◯-goal disjunct
  `◯(E(Γ) ⇢ A(Γ ⇒ ◯D))`, consumed by exactly this commute) recurses
  at the *same* sequent and is therefore inexpressible in her
  DM-terminating recursion — the flaw is independent of the
  completeness gap.
-/

section Adequacy

/-- Locate a rule's principal on one side of a split context. -/
private theorem split_principal {P : PLLFormula} {Γ₀ Θ₀ Γ Δ : List PLLFormula}
    (hp : Γ₀.Perm (P :: Θ₀)) (hs : Γ₀.Perm (Γ ++ Δ)) :
    (P ∈ Γ ∧ Θ₀.Perm (Γ.erase P ++ Δ)) ∨
    (P ∈ Δ ∧ Θ₀.Perm (Γ ++ Δ.erase P)) := by
  have h1 : (P :: Θ₀).Perm (Γ ++ Δ) := hp.symm.trans hs
  rcases List.mem_append.mp (h1.subset (.head _)) with h | h
  · left
    refine ⟨h, ?_⟩
    have h2 : (Γ ++ Δ).Perm (P :: (Γ.erase P ++ Δ)) :=
      (List.perm_cons_erase h).append_right Δ
    exact (h1.trans h2).cons_inv
  · right
    refine ⟨h, ?_⟩
    have h2 : (Γ ++ Δ).Perm (P :: (Γ ++ Δ.erase P)) :=
      ((List.perm_cons_erase h).append_left Γ).trans List.perm_middle
    exact (h1.trans h2).cons_inv

private theorem pfree_of_erase {p : String} {Δ : List PLLFormula}
    {P : PLLFormula} (hΔ : ∀ ψ ∈ Δ, p ∉ ψ.atoms) :
    ∀ ψ ∈ Δ.erase P, p ∉ ψ.atoms :=
  fun ψ hψ => hΔ ψ (List.mem_of_mem_erase hψ)

/-- **The adequacy pair.**  Proved: both axioms, all right rules, and
`laxL` on either side with the succedent on the r-side.  The
remaining cases are sorry-isolated with a verdict note each; the one
*flawed-in-print* case is `laxL`/Δ-side/(A). -/
theorem iem_adequate (p : String) :
    ∀ {Γ₀ : List PLLFormula} {C : PLLFormula}, G4 Γ₀ C →
    ∃ n : Nat, ∀ fuel, n < fuel → ∀ (Γ Δ : List PLLFormula),
    Γ₀.Perm (Γ ++ Δ) → (∀ ψ ∈ Δ, p ∉ ψ.atoms) →
    ((p ∉ C.atoms → G4 (iemE p fuel Γ falsePLL :: Δ) C) ∧
      G4 (iemE p fuel Γ C :: Δ) (iemA p fuel Γ C)) := by
  intro Γ₀ C d
  induction d with
  | @init Γ₀ a h =>
      refine ⟨0, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
          rcases List.mem_append.mp (hs.subset h) with hγ | hδ
          · constructor
            · intro hp
              -- a ≠ p from p-freeness of the goal; the ∃ᵃᵗ atom
              -- conjunct of `iemE` supplies `a` — project it.
              have hap : ¬ a = p := by
                simp only [atoms_prop, Finset.mem_singleton] at hp
                exact fun hc => hp hc.symm
              simp only [iemE]
              refine G4.andAll_elim ?_ (.init (.head _))
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              exact List.mem_filterMap.mpr
                ⟨prop a, hγ, by simp [eAtomList, hap]⟩
            · -- the axiom ⊤-disjunct of `iemA` (S is an At-instance)
              simp only [iemA]
              refine G4.orAll_intro (φ := truePLL) ?_ (G4.truePLL_intro _)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              rw [if_pos (by simp [isAxInst, List.contains_iff_mem, hγ])]
              exact .head _
          · -- a ∈ Δ (p-free side): (E) is `init`; (A) lands the ∀ᵃᵗ
            -- goal-atom disjunct `a` (a ≠ p because a ∈ Δ is p-free).
            have hap : ¬ a = p := by
              have := hΔ _ hδ
              simp only [atoms_prop, Finset.mem_singleton] at this
              exact fun hc => this hc.symm
            refine ⟨fun _ => .init (.tail _ hδ), ?_⟩
            simp only [iemA]
            refine G4.orAll_intro (φ := prop a) ?_ (.init (.tail _ hδ))
            refine List.mem_append.mpr (.inl ?_)
            refine List.mem_append.mpr (.inl ?_)
            refine List.mem_append.mpr (.inr ?_)
            simp [aGoalClauses, hap]
  | @botL Γ₀ C h =>
      refine ⟨0, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
          rcases List.mem_append.mp (hs.subset h) with hγ | hδ
          · constructor
            · intro _
              simp only [iemE]
              refine G4.andAll_elim ?_ (.botL (.head _))
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              exact List.mem_filterMap.mpr ⟨falsePLL, hγ, by simp [eAtomList]⟩
            · simp only [iemA]
              refine G4.orAll_intro (φ := truePLL) ?_ (G4.truePLL_intro _)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              refine List.mem_append.mpr (.inl ?_)
              rw [if_pos (by simp [isAxInst, List.contains_iff_mem, hγ])]
              exact .head _
          · exact ⟨fun _ => .botL (.tail _ hδ), .botL (.tail _ hδ)⟩
  | @andR Γ₀ A B d₁ d₂ ih₁ ih₂ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      obtain ⟨n₂, IH₂⟩ := ih₂
      refine ⟨max n₁ n₂ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₂ : n₂ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      have h₂' : n₂ < f + 1 := by omega
      constructor
      · intro hpC
        rw [atoms_and, Finset.mem_union] at hpC
        push_neg at hpC
        exact .andR ((IH₁ (f+1) h₁' Γ Δ hs hΔ).1 hpC.1)
          ((IH₂ (f+1) h₂' Γ Δ hs hΔ).1 hpC.2)
      · simp only [iemA]
        refine G4.orAll_intro
          (φ := ((iemE p f Γ A).ifThen (iemA p f Γ A)).and
                ((iemE p f Γ B).ifThen (iemA p f Γ B))) ?_ ?_
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
            (List.mem_append.mpr (.inr (by simp [aGoalClauses]))))))
        · exact .andR
            (.impR (G4.weaken₂ _ (IH₁ f h₁ Γ Δ hs hΔ).2))
            (.impR (G4.weaken₂ _ (IH₂ f h₂ Γ Δ hs hΔ).2))
  | @orR1 Γ₀ A B d₁ ih₁ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      refine ⟨n₁ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      constructor
      · intro hpC
        rw [atoms_or, Finset.mem_union] at hpC
        push_neg at hpC
        exact .orR1 ((IH₁ (f+1) h₁' Γ Δ hs hΔ).1 hpC.1)
      · simp only [iemA]
        refine G4.orAll_intro
          (φ := (iemE p f Γ A).ifThen (iemA p f Γ A)) ?_ ?_
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
            (List.mem_append.mpr (.inr (by simp [aGoalClauses]))))))
        · exact .impR (G4.weaken₂ _ (IH₁ f h₁ Γ Δ hs hΔ).2)
  | @orR2 Γ₀ A B d₁ ih₁ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      refine ⟨n₁ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      constructor
      · intro hpC
        rw [atoms_or, Finset.mem_union] at hpC
        push_neg at hpC
        exact .orR2 ((IH₁ (f+1) h₁' Γ Δ hs hΔ).1 hpC.2)
      · simp only [iemA]
        refine G4.orAll_intro
          (φ := (iemE p f Γ B).ifThen (iemA p f Γ B)) ?_ ?_
        · refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
            (List.mem_append.mpr (.inr ?_)))))
          simp [aGoalClauses]
        · exact .impR (G4.weaken₂ _ (IH₁ f h₁ Γ Δ hs hΔ).2)
  | @impR Γ₀ A B d₁ ih₁ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      refine ⟨n₁ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      constructor
      · intro hpC
        rw [atoms_ifThen, Finset.mem_union] at hpC
        push_neg at hpC
        -- A joins the p-free side: no clause consumption at all
        have hΔ' : ∀ ψ ∈ A :: Δ, p ∉ ψ.atoms := by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hpC.1
          · exact hΔ ψ hψ
        have hs' : (A :: Γ₀).Perm (Γ ++ (A :: Δ)) :=
          (hs.cons A).trans List.perm_middle.symm
        refine .impR (G4.perm ((IH₁ (f+1) h₁' Γ (A :: Δ) hs' hΔ').1 hpC.2)
          ?_)
        exact G4.swap₁ _ _ _
      · -- the R→ disjunct, split on p ∈ A exactly as in her table
        have hs' : (A :: Γ₀).Perm ((A :: Γ) ++ Δ) := hs.cons A
        have hIH := (IH₁ f h₁ (A :: Γ) Δ hs' hΔ).2
        by_cases hpA : p ∈ A.atoms
        · simp only [iemA]
          refine G4.orAll_intro
            (φ := (iemE p f (A :: Γ) B).ifThen (iemA p f (A :: Γ) B)) ?_ ?_
          · refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr ?_)))))
            simp [aGoalClauses, hpA]
          · exact .impR (G4.weaken₂ _ hIH)
        · simp only [iemA]
          refine G4.orAll_intro
            (φ := A.ifThen (iemA p f (A :: Γ) B)) ?_ ?_
          · refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr ?_)))))
            simp [aGoalClauses, hpA]
          · -- consume the guarded E-clause `A → E(A::Γ ⇒ B)` by G4.mp
            refine .impR (G4.perm ?_ (G4.swap₁ _ _ _))
            simp only [iemE]
            refine G4.andAll_elim
              (φ := A.ifThen (iemE p f (A :: Γ) B)) ?_ ?_
            · refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inl (List.mem_append.mpr
                  (.inr ?_)))))))
              simp [eGoalClauses, hpA]
            · exact G4.mp (List.Perm.refl _) (G4.ofMem (.head _))
                (G4.weaken₂ _ hIH)
  | @laxR Γ₀ D d₁ ih₁ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      refine ⟨n₁ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      constructor
      · intro hpC
        rw [atoms_somehow] at hpC
        exact .laxR ((IH₁ (f+1) h₁' Γ Δ hs hΔ).1 hpC)
      · -- land the R◯-instance disjunct `◯∀p(Γ ⇒ D)` through the
        -- R◯-instance conjunct `◯∃p(Γ ⇒ D)` of the E-hypothesis:
        -- laxL the conjunct against the boxed disjunct — the monad
        -- glue that replaces her `R◯; L◯` composition.
        simp only [iemA]
        refine G4.orAll_intro (φ := (iemA p f Γ D).somehow) ?_ ?_
        · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
            (List.mem_append.mpr (.inr (by simp [aGoalClauses]))))))
        · simp only [iemE]
          refine G4.andAll_elim (φ := (iemE p f Γ D).somehow) ?_ ?_
          · refine List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inl (List.mem_append.mpr
                (.inr ?_)))))))
            simp [eGoalClauses]
          · exact .laxL (List.Perm.refl _) (.laxR (IH₁ f h₁ Γ Δ hs hΔ).2)
  | @laxL Γ₀ Θ₀ χ W h d₁ ih₁ =>
      obtain ⟨n₁, IH₁⟩ := ih₁
      refine ⟨n₁ + 1, ?_⟩
      intro fuel hf Γ Δ hs hΔ
      cases fuel with
      | zero => omega
      | succ f =>
      have h₁ : n₁ < f := by omega
      have h₁' : n₁ < f + 1 := by omega
      rcases split_principal h hs with ⟨hγ, hΘ⟩ | ⟨hδ, hΘ⟩
      · -- box on the Γ-side: open through the box-opener conjunct
        -- ((E)-side) and the L◯-instance pair ((A)-side)
        have hsplit1 : (χ :: Θ₀).Perm ((χ :: Γ.erase (somehow χ)) ++ Δ) :=
          hΘ.cons χ
        constructor
        · intro hpC
          simp only [iemE]
          refine G4.andAll_elim
            (φ := (iemE p f (χ :: Γ.erase (somehow χ)) falsePLL).somehow)
            ?_ ?_
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
              (List.mem_append.mpr (.inr (List.mem_flatMap.mpr
                ⟨somehow χ, hγ, by simp [eOpenClauses]⟩))))))
          · exact .laxL (List.Perm.refl _)
              ((IH₁ f h₁ _ Δ hsplit1 hΔ).1 hpC)
        · simp only [iemA]
          refine G4.orAll_intro
            (φ := (iemA p f (χ :: Γ.erase (somehow χ)) W.somehow).somehow)
            ?_ ?_
          · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inr
              (List.mem_flatMap.mpr ⟨somehow χ, hγ, by
                simp [aCtxClauses]⟩))))
          · simp only [iemE]
            refine G4.andAll_elim
              (φ := (iemE p f (χ :: Γ.erase (somehow χ)) W.somehow).somehow)
              ?_ ?_
            · exact List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
                (List.mem_append.mpr (.inl (List.mem_append.mpr (.inl
                  (List.mem_append.mpr (.inr (List.mem_flatMap.mpr
                    ⟨somehow χ, hγ, List.Mem.head _⟩))))))))))
            · exact .laxL (List.Perm.refl _)
                (.laxR (IH₁ f h₁ _ Δ hsplit1 hΔ).2)
      · -- box on the Δ-side (p-free)
        have hχp : p ∉ χ.atoms := by
          have := hΔ _ hδ
          simpa [atoms_somehow] using this
        have hΔ' : ∀ ψ ∈ χ :: Δ.erase (somehow χ), p ∉ ψ.atoms := by
          intro ψ hψ
          rcases List.mem_cons.mp hψ with rfl | hψ
          · exact hχp
          · exact pfree_of_erase hΔ _ hψ
        have hsplit1 : (χ :: Θ₀).Perm (Γ ++ (χ :: Δ.erase (somehow χ))) :=
          (hΘ.cons χ).trans List.perm_middle.symm
        constructor
        · intro hpC
          -- succedent on the r-side: her (DPN)-L◯ *second* case — the
          -- L◯-closure is legitimate (goal ◯W is a circle formula)
          refine .laxL (((List.perm_cons_erase hδ).cons _).trans
            (G4.swap₁ _ _ _)) ?_
          exact (((IH₁ (f+1) h₁' Γ _ hsplit1 hΔ').1 hpC).perm
            (G4.swap₁ _ _ _))
        · -- **HOLDOUT — her (DPN)-L◯ FIRST case, flawed in print.**
          -- Target: `iemE p (f+1) Γ ◯W, Δ ⊢ iemA p (f+1) Γ ◯W` with
          -- `◯χ ∈ Δ`.  The IH (same Γ-part, same succedent, fuel
          -- f+1) gives the target with `χ` in place of `◯χ`; closing
          -- the box needs `L◯` under the succedent `∀pSⁱ`, which is
          -- a big disjunction, NOT a circle formula — the rule does
          -- not apply.  Her text (arXiv v1, proof of Lemma 7, case
          -- L◯) states the target `Γʳ,◯ψ,∃pSⁱ ⇒ ∀pSⁱ` for this
          -- case, then derives `Γʳ,◯ψ,∃pSⁱ ⇒ ◯φ` — the *other*
          -- case's sequent — and concludes "this is what we had to
          -- show".  No disjunct of her `∀pSⁱ` absorbs a Δ-side box
          -- either: the L◯-instance and γ-disjuncts range over
          -- Γⁱ-side boxes/implications only, and the R◯-disjunct
          -- `◯∀p(Γⁱ⇒φ)` needs an IH at `(Γ,ψ ⇒ φ)`, which the
          -- derivation (ending in L◯) does not supply.  The
          -- retention-side repair (v2/v3's self-referential ◯-goal
          -- disjunct `◯(E(Γ) ⇢ A(Γ ⇒ ◯D))`, whose consumption is
          -- exactly this commute) recurses at the SAME sequent and
          -- is inexpressible in her ≪-terminating recursion: fuel
          -- (or Bílková-style truncation) is needed — that is the
          -- precise content the repo's route-T supplies and her
          -- framework lacks.  Flaw independent of the completeness
          -- gap.
          sorry
  | _ =>
      -- Remaining rule cases (andL, orL, the five implication left
      -- rules, and the two lax implication rules), both sides.
      -- Verdict per the dry-run against `eSound`/`aSound` (whose
      -- proved cases consume the *identical* clause shapes):
      -- * Γ-side: each rule's instance clause is landed exactly as
      --   its (∀l)-consumption in `aSound` — the IHs supply the
      --   premise pair, the E-hypothesis's matching conjunct
      --   supplies each guard via `G4.andAll_elim`, and `G4.mp`
      --   (consumed-form) fires the `∀pS₁ → ∃pS₂`-shaped conjuncts;
      --   `impLLax`/`impLLaxLax` land their `ι∀ᴿ`/`ι∃ᴿ` pairs with
      --   the γ-conjunct as its own witness (as in `eSound`).  No
      --   step needs cut; mechanical, following P4a's case text with
      --   `G4.mp` for `G4s.mp_adm` and clause-projection for
      --   `E_step`.
      -- * Δ-side: her centered (DPN)⁺ re-application — fire the same
      --   rule on the p-free principal in the target; premise IHs
      --   apply at the same Γ-part.  Succedent-independent for every
      --   left rule (their conclusions do not constrain `Sˢ`), so no
      --   analogue of the L◯ flaw arises; `impLLaxLax` with
      --   principal and witness on opposite sides uses the
      --   `eGammaClauses`/`aGammaClauses` γ-forms (witness
      --   anticipation), which `eSound`/`aSound` show are
      --   self-witnessing.
      sorry

end Adequacy

/-! ## Verdict (task #13): Iemhoff's UI proof in its own habitat

**Calculus.**  `PLLND.G4` of `LaxLogic/PLLG4.lean`, re-checked against
Figures 2.2/2.3 of arXiv:2209.08976v1 — it *is* her G4iLL (delta: the
repo's `impLBot`, absent from her figure since `⊥` is not an atom for
her; clauses supplied and flagged).

**Cut status** (checked, not assumed): not admissible — re-exported
below from `PLLG4Gap.lean`; contraction fails too.  Hence her Fact 3
("G4iLL is balanced"), justified by the refuted Corollary 1
(G3iLL ≡ G4iLL), is FALSE, and her Theorem 5 (the 2019 engine, which
*requires* a balanced calculus) is fed a false premise.  Every "⊢" in
her §6.7 is `⊢_L` (the logic) — her proof is a proof about PLL
*conditional on the equivalence*, not about G4iLL-derivability.

**The tables** are transcribed faithfully (sequent-indexed, `⊥` for
her empty succedent): the 2019 standard assignment for the centered
rules and axioms, the special `R→`/`L1→`/`L4→` assignments (§5), her
lax assignments (§6.6) including the `L◯→`-nonprincipal γ-forms, box
openers, and the subset plumbing `⋀{∃p(Θ⇒) | Θ ⊆ Sᵃ}`.  Her recursion
terminates on the DM order ≪ (her Fact 1/2); mechanically the pair is
fueled, with `seqMeasure` (a `4^weight` linearisation of ≪, decreasing
clause-by-clause) the documented sufficient bound, so the packaged
interpolant is computed from the sequent alone — uniformity is not
affected by the fuel device.

**In-habitat verdict, property by property** (`⊢` = G4iLL, no cut):

* p-freeness: PROVED (`iem_pfree`).
* (∃r)/(∀l) — her independent properties: PROVED (`iem_sound`) except
  the single conjunct `∃pS₁` of her `L4→` `ι∃ᴿ = ∃pS₁ ∧ (∀pS₁→∃pS₂)`:
  her proof of (IPP)∃ uses "⊢ ⋀Sᵃ → ⋀S₁ᵃ" + composition — cut.  The
  premise-1 context `B→D, Γ∖F` is not rule-reachable from `Γ` without
  changing the goal, so no induction supplies it.  Pitts'/UIML's
  guarded shape `(E(S₁)→A(S₁)) → E(D,Γ∖F)` for the same rule IS
  in-habitat provable (the `L4→` case of `aSound` shows the guarded
  consumption pattern working); her deviation from Pitts' shape is
  the precise local obstruction.  Everything else closes with two
  admissible tools proved here with no cut:
  - `G4.iden` — general identity;
  - `G4.guardMP`/`G4.mp` — **consumed-form** modus ponens against a
    context implication (`Δ ⊢ X` and `Y,Δ ⊢ C` give `X→Y,Δ ⊢ C`).
    The *retained* form is G3's `L→` and fails (it would give
    G3iLL ⊆ G4iLL); the consumed form is admissible, and its `laxL`
    case closes exactly because `impLLaxLax` lets `◯W→Y` consume the
    box being opened — her `L◯→` device is what makes her own glue
    admissible.  This is the sharpest *positive* content of the
    in-habitat reading.
* (∀∃) — the dependent property (adequacy, `iem_adequate`): both
  axioms, all four right rules, and `laxL` on the Γ-side (both
  components) and Δ-side-(E) are PROVED, with clause-projection
  replacing P4a's `E_step`-cut (her strictly-descending premises make
  fuel-monotonicity unnecessary — no cut anywhere in the glue).  The
  nine remaining left-rule cases are mechanical by the same
  consumption patterns their clauses already exhibit in
  `eSound`/`aSound` (notes at the catch-all).  **One case is flawed
  in print and sorry-isolated: (DPN)-L◯, first case** — Δ-side box,
  succedent on the i-side.  Her text states the target
  `Γʳ,◯ψ,∃pSⁱ ⇒ ∀pSⁱ`, derives `Γʳ,◯ψ,∃pSⁱ ⇒ ◯φ` (the other case's
  sequent) and declares it "what we had to show"; the missing step —
  closing `ψ ⟿ ◯ψ` under the succedent `∀pSⁱ` — is not an `L◯`
  instance (`∀pSⁱ` is a disjunction, not a circle formula), and no
  disjunct of her `∀pSⁱ` anticipates a Δ-side box (her waiting
  devices cover Δ-side atoms via `∀ᵃᵗ` and Δ-side boxes only as
  `L◯→`-witnesses via the γ-forms, which need `◯α→β ∈ Γⁱ`).

**Delta-to-complete-calculus analysis.**  The repair known from this
repo's retention development is the ◯-goal disjunct
`◯(E(Γ) ⇢ A(Γ ⇒ ◯D))` (v2), consumed by precisely this Δ-side `laxL`
commute — but it recurses at the *same* sequent, so it is
inexpressible in her ≪-terminating recursion: one needs fuel + a
height-dominated adequacy invariant (P4a) or Bílková-style truncation
(route T/v3).  So the two halves of her paper fail in complementary
ways: the calculus is incomplete for PLL (retention repairs needed,
`PLLG4Gap`), and the quantifier recursion is complete-but-blind to
the Δ-side box commute (fuel/truncation needed).  The retention
repair makes the same-sequent disjunct *meaningful* (cumulative
contexts absorb what termination paid for) — the two repairs are the
same phenomenon seen from the two sides of Cor 8.1.

**Overall.**  Against the task's dichotomy: the evidence is (b)-with-
structure — her per-rule interpolant assignment is sound *for the
logic modulo the refuted bridge*, and mostly sound in-habitat (all of
(∀l), all but one conjunct of (∃r), and the adequacy commutes proved
here), but her proof contains one local flaw independent of the
completeness gap — the (DPN)-L◯ first case — whose only known repairs
live outside her termination discipline; her `L4→` ∃-assignment
additionally deviates from Pitts' in a way that costs (IPP)∃
in-habitat.  Confidence: the L◯ mismatch is verbatim in her text
(quoted above) and machine-locatable; whether the *statement* "UI
holds for G4iLL-derivability" survives with different tables remains
open (the flawed case's target is PLL-true; a G4iLL counterexample
would need every `∀pSⁱ`-disjunct to fail against a derivable premise
— not found in the instances probed, and decidable per instance via
`PLLDecide` since both quantifier values compute). -/

/-- Cut fails in G4iLL (re-export; `PLLG4Gap.lean`): `◯p` cuts
between derivable premises onto the underivable gap sequent. -/
example :
    G4 [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] ((prop "p").somehow) ∧
    G4 [(prop "p").somehow, PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] (prop "r") ∧
    ¬ G4 [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] (prop "r") :=
  PLLG4Gap.cut_not_admissible

/-- Contraction fails in G4iLL (re-export). -/
example :
    G4 [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa, PLLG4Gap.Fa] (prop "r") ∧
    ¬ G4 [PLLG4Gap.Ga.somehow, PLLG4Gap.Fa] (prop "r") :=
  PLLG4Gap.contraction_not_admissible

end G4UI
end PLLND
