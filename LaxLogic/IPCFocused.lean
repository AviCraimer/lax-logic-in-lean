import LaxLogic.PLLSemUIFrag

/-!
# `LJF`: the same structure, IPC only — the control experiment

Matthew's test (2026-08-08): build the polarised/focused apparatus of
`LaxLogic/PLLFocused.lean` **with the lax rules omitted**, keep every name the
same, and see whether the proposed uniform-interpolation proof actually runs.
If the structure is right, everything except the `◯`-specific steps should go
through; if it does not run here, it will not run for PLL either.

## Naming

The polarised focused calculus for IPC is **`LJF`** (Liang–Miller's name for
the focused intuitionistic calculus, which is what this is). The PLL version in
`PLLFocused.lean` is then **`LJF◯`** — `LJF` plus the `◯` rules and the second
judgment. This file is `LJF`; the namespace is `IPC`, so the two coexist and
every shared name (`Pos`, `Neg`, `Stab`, `RFocus`, `LFoc`, `Inv`, `cl_orL`, …)
means the corresponding thing on each side.

Differences from `LJF◯`, and *only* these:

* no `circ` constructor in `Neg`;
* no `JD` flag anywhere — with no `lax` judgment there is nothing to track;
* no `circR` / `circL` rules;
* `impR` / `andR` are unrestricted (in `LJF◯` they are `.tru`-only, because at
  `.lax` they would assert the converse of `K`).

Formulas are the shared `PLLFormula`; erasure never produces `◯`, so `Deriv`
on erased formulas is IPC by the repository's `conservativity_IPL`.

## What is proved here

The **existential interpolant** `ExInterp p Γ Ω` — a `p`-free formula that the
antecedent entails and that is weakest such. Uniform interpolation's `∃p` is
its existence. The clauses are named for the rules exactly as in
`PLLCandidate.Cand`, and **all four left-inversion clauses are proved
outright**: `cl_fls`, `cl_downL`, `cl_atomL`, `cl_orL`.

`exInterp_of_stable` then assembles them: the whole inversion phase is a
terminating recursion on the size of `Ω`, and uniform interpolation for IPC
follows from the **single remaining obligation** `StableInterp` — an
existential interpolant at stable sequents (`Ω = []`).

That isolation is the result of the experiment. See the closing section.
-/

namespace IPC

open PLLFormula PLLND SemUI

/-! ## Polarised syntax — `LJF◯` minus `circ` -/

mutual
/-- Positive (synchronous) propositions. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
/-- Negative (asynchronous) propositions.  No `circ`: that is the whole
difference from `LJF◯`'s `Neg`. -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
end

mutual
/-- Erase a positive proposition. -/
def erasePos : Pos → PLLFormula
  | .atom a => .prop a
  | .fls    => .falsePLL
  | .or p q => .or (erasePos p) (erasePos q)
  | .down n => eraseNeg n

/-- Erase a negative proposition. -/
def eraseNeg : Neg → PLLFormula
  | .up p    => erasePos p
  | .imp p n => .ifThen (erasePos p) (eraseNeg n)
  | .and m n => .and (eraseNeg m) (eraseNeg n)
end

/-! ## The focused calculus `LJF` — `LJF◯` minus the flag and the `◯` rules -/

mutual

/-- A **stable sequent**. -/
inductive Stab : List Neg → Pos → Type
  | rfoc {Γ P} : RFocus Γ P → Stab Γ P
  | lfoc {Γ P N} (h : N ∈ Γ) : LFoc Γ N P → Stab Γ P

/-- **Right focus** on a positive goal. -/
inductive RFocus : List Neg → Pos → Type
  | init {Γ a} (h : Neg.up (Pos.atom a) ∈ Γ) : RFocus Γ (.atom a)
  | or1 {Γ P Q} : RFocus Γ P → RFocus Γ (.or P Q)
  | or2 {Γ P Q} : RFocus Γ Q → RFocus Γ (.or P Q)
  | rel {Γ N} : Inv Γ [] N → RFocus Γ (.down N)

/-- **Left focus** on a negative hypothesis. -/
inductive LFoc : List Neg → Neg → Pos → Type
  | rel {Γ Q P} : Inv Γ [Q] (.up P) → LFoc Γ (.up Q) P
  | impL {Γ Q N P} : Stab Γ Q → LFoc Γ N P → LFoc Γ (.imp Q N) P
  | and1 {Γ M N P} : LFoc Γ M P → LFoc Γ (.and M N) P
  | and2 {Γ M N P} : LFoc Γ N P → LFoc Γ (.and M N) P

/-- **Inversion**.  `impR` and `andR` are unrestricted here — in `LJF◯` they
are `.tru`-only, because at `.lax` they would assert the converse of `K`. -/
inductive Inv : List Neg → List Pos → Neg → Type
  | impR {Γ Ω Q N} : Inv Γ (Q :: Ω) N → Inv Γ Ω (.imp Q N)
  | andR {Γ Ω M N} : Inv Γ Ω M → Inv Γ Ω N → Inv Γ Ω (.and M N)
  | stable {Γ P} : Stab Γ P → Inv Γ [] (.up P)
  | orL {Γ Ω P Q N} : Inv Γ (P :: Ω) N → Inv Γ (Q :: Ω) N →
      Inv Γ (.or P Q :: Ω) N
  | flsL {Γ Ω N} : Inv Γ (.fls :: Ω) N
  | downL {Γ Ω M N} : Inv (M :: Γ) Ω N → Inv Γ (.down M :: Ω) N
  | atomL {Γ Ω a N} : Inv (.up (.atom a) :: Γ) Ω N → Inv Γ (.atom a :: Ω) N

end

/-! ## Contexts -/

/-- The erased hypotheses of an inversion sequent. -/
def hyps (Γ : List Neg) (Ω : List Pos) : List PLLFormula :=
  Ω.map erasePos ++ Γ.map eraseNeg

theorem mem_hyps_neg {Γ : List Neg} {Ω : List Pos} {M : Neg} (h : M ∈ Γ) :
    eraseNeg M ∈ hyps Γ Ω :=
  List.mem_append_right _ (List.mem_map_of_mem h)

theorem mem_hyps_pos {Γ : List Neg} {Ω : List Pos} {Q : Pos} (h : Q ∈ Ω) :
    erasePos Q ∈ hyps Γ Ω :=
  List.mem_append_left _ (List.mem_map_of_mem h)

/-- Cut, natural-deduction style. -/
theorem ndCut {Γ : List PLLFormula} {φ ψ : PLLFormula}
    (h₁ : Deriv Γ φ) (h₂ : Deriv (φ :: Γ) ψ) : Deriv Γ ψ :=
  Deriv.impElim (Deriv.impIntro h₂) h₁

/-! ## Soundness of `LJF` into the reference system

Identical in shape to `LJF◯`'s, with `wrap` deleted — there is no judgment to
wrap. Left focus is again in continuation-passing form. -/

mutual

theorem soundStab : ∀ {Γ : List Neg} {P : Pos},
    Stab Γ P → Deriv (Γ.map eraseNeg) (erasePos P)
  | _, _, .rfoc d => soundRFocus d
  | _, _, .lfoc h d => soundLFoc d (Deriv.iden (List.mem_map_of_mem h))

theorem soundRFocus : ∀ {Γ : List Neg} {P : Pos},
    RFocus Γ P → Deriv (Γ.map eraseNeg) (erasePos P)
  | _, _, .init h => Deriv.iden (List.mem_map_of_mem h)
  | _, _, .or1 d => Deriv.orIntro1 (soundRFocus d)
  | _, _, .or2 d => Deriv.orIntro2 (soundRFocus d)
  | _, _, .rel d => soundInv d

theorem soundLFoc : ∀ {Γ : List Neg} {N : Neg} {P : Pos},
    LFoc Γ N P → Deriv (Γ.map eraseNeg) (eraseNeg N) →
      Deriv (Γ.map eraseNeg) (erasePos P)
  | _, _, _, .rel d, k => ndCut k (soundInv d)
  | _, _, _, .impL a d, k => soundLFoc d (Deriv.impElim k (soundStab a))
  | _, _, _, .and1 d, k => soundLFoc d (Deriv.andElim1 k)
  | _, _, _, .and2 d, k => soundLFoc d (Deriv.andElim2 k)

theorem soundInv : ∀ {Γ : List Neg} {Ω : List Pos} {N : Neg},
    Inv Γ Ω N → Deriv (hyps Γ Ω) (eraseNeg N)
  | _, _, _, .impR d => Deriv.impIntro (soundInv d)
  | _, _, _, .andR d e => Deriv.andIntro (soundInv d) (soundInv e)
  | _, _, _, .stable d => soundStab d
  | _, _, _, .orL d e =>
      Deriv.orElim (Deriv.iden (mem_hyps_pos (List.mem_cons_self ..)))
        ((soundInv d).rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (by
              simp only [hyps, List.map_cons, List.append_eq, List.mem_append,
                List.mem_cons] at hθ ⊢
              tauto)))
        ((soundInv e).rename (fun θ hθ => by
          rcases List.mem_cons.mp hθ with rfl | hθ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (by
              simp only [hyps, List.map_cons, List.append_eq, List.mem_append,
                List.mem_cons] at hθ ⊢
              tauto)))
  | _, _, _, .flsL =>
      Deriv.falsoElim _ (Deriv.iden (mem_hyps_pos (List.mem_cons_self ..)))
  | _, _, _, .downL d =>
      (soundInv d).rename (fun θ hθ => by
        simp only [hyps, List.map_cons, List.mem_append,
          List.mem_cons, erasePos] at hθ ⊢
        tauto)
  | _, _, _, .atomL d =>
      (soundInv d).rename (fun θ hθ => by
        simp only [hyps, List.map_cons, List.mem_append,
          List.mem_cons, eraseNeg, erasePos] at hθ ⊢
        tauto)

end

/-! ## `p`-freeness -/

/-- `p` does not occur. -/
def PFree (p : String) : PLLFormula → Prop
  | .prop a     => a ≠ p
  | .falsePLL   => True
  | .and a b    => PFree p a ∧ PFree p b
  | .or a b     => PFree p a ∧ PFree p b
  | .ifThen a b => PFree p a ∧ PFree p b
  | .somehow a  => PFree p a

/-! ## The existential interpolant

`∃p` of an antecedent: a `p`-free formula the antecedent entails, and the
weakest such.  Note it does **not** mention the goal — which is the whole point
of *uniform* interpolation, and the reason the right-hand rules (`impR`,
`andR`, and in `LJF◯` also `circR`) contribute no clause: the existential
interpolant sees only the **left** rules. -/

/-- An existential interpolant for `p` at the antecedent `(Γ; Ω)`. -/
structure ExInterp (p : String) (Γ : List Neg) (Ω : List Pos) where
  /-- The interpolant. -/
  fml : PLLFormula
  /-- It is `p`-free. -/
  pfree : PFree p fml
  /-- The antecedent entails it. -/
  sound : Deriv (hyps Γ Ω) fml
  /-- It is the weakest such: any `p`-free consequence follows from it. -/
  weakest : ∀ ψ, PFree p ψ → Deriv (hyps Γ Ω) ψ → Deriv [fml] ψ

/-! ### The clauses, named for the rules exactly as in `PLLCandidate.Cand` -/

/-- **`cl_fls`.**  An absurd hypothesis: the interpolant is `⊥`. -/
def cl_fls (p : String) (Γ : List Neg) (Ω : List Pos) :
    ExInterp p Γ (.fls :: Ω) where
  fml := .falsePLL
  pfree := trivial
  sound := Deriv.iden (mem_hyps_pos (List.mem_cons_self ..))
  weakest := fun _ _ _ => Deriv.falsoElim _ (Deriv.iden (List.mem_cons_self ..))

/-- Transport an interpolant along a hypothesis-set equality. -/
def ExInterp.transport {p : String} {Γ Γ' : List Neg} {Ω Ω' : List Pos}
    (H : ∀ ψ ∈ hyps Γ Ω, ψ ∈ hyps Γ' Ω')
    (H' : ∀ ψ ∈ hyps Γ' Ω', ψ ∈ hyps Γ Ω)
    (e : ExInterp p Γ Ω) : ExInterp p Γ' Ω' where
  fml := e.fml
  pfree := e.pfree
  sound := e.sound.rename H
  weakest := fun ψ hψ hd => e.weakest ψ hψ (hd.rename H')

/-- **`cl_downL`.**  A shifted negative becomes a stable hypothesis: the
hypothesis *set* is unchanged, so the interpolant is unchanged. -/
def cl_downL {p : String} {Γ : List Neg} {Ω : List Pos} {M : Neg}
    (e : ExInterp p (M :: Γ) Ω) : ExInterp p Γ (.down M :: Ω) :=
  e.transport
    (fun ψ hψ => by
      simp only [hyps, List.map_cons, List.mem_append,
        List.mem_cons, erasePos] at hψ ⊢; tauto)
    (fun ψ hψ => by
      simp only [hyps, List.map_cons, List.mem_append,
        List.mem_cons, erasePos] at hψ ⊢; tauto)

/-- **`cl_atomL`.**  Likewise for an atom — uniformly in whether the atom *is*
`p`; the `p`-case is discharged at stable sequents, not here. -/
def cl_atomL {p : String} {Γ : List Neg} {Ω : List Pos} {a : String}
    (e : ExInterp p (.up (.atom a) :: Γ) Ω) : ExInterp p Γ (.atom a :: Ω) :=
  e.transport
    (fun ψ hψ => by
      simp only [hyps, List.map_cons, List.mem_append,
        List.mem_cons, eraseNeg, erasePos] at hψ ⊢; tauto)
    (fun ψ hψ => by
      simp only [hyps, List.map_cons, List.mem_append,
        List.mem_cons, eraseNeg, erasePos] at hψ ⊢; tauto)

/-- **`cl_orL` — the join clause.**  Two branches, one conclusion: the
interpolant is the **disjunction** of the branch interpolants.  This is the
clause the PLL campaign traced its difficulty to, and it is exactly as easy
here as `cθ_orL` was there. -/
def cl_orL {p : String} {Γ : List Neg} {Ω : List Pos} {P Q : Pos}
    (e₁ : ExInterp p Γ (P :: Ω)) (e₂ : ExInterp p Γ (Q :: Ω)) :
    ExInterp p Γ (.or P Q :: Ω) where
  fml := .or e₁.fml e₂.fml
  pfree := ⟨e₁.pfree, e₂.pfree⟩
  sound := by
    -- case on the disjunction in the hypotheses, then use each branch
    refine Deriv.orElim (φ := erasePos P) (ψ := erasePos Q)
      (Deriv.iden (mem_hyps_pos (List.mem_cons_self ..))) ?_ ?_
    · exact Deriv.orIntro1 (e₁.sound.rename (fun θ hθ => by
        simp only [hyps, List.map_cons, List.mem_append, List.mem_cons] at hθ ⊢
        tauto))
    · exact Deriv.orIntro2 (e₂.sound.rename (fun θ hθ => by
        simp only [hyps, List.map_cons, List.mem_append, List.mem_cons] at hθ ⊢
        tauto))
  weakest := by
    intro ψ hψ hd
    refine Deriv.orElim (φ := e₁.fml) (ψ := e₂.fml)
      (Deriv.iden (List.mem_cons_self ..)) ?_ ?_
    · exact (e₁.weakest ψ hψ (by
        -- from `P` derive `P ∨ Q`, then cut into `hd`
        refine ndCut (φ := erasePos P |>.or (erasePos Q)) ?_ ?_
        · exact Deriv.orIntro1 (Deriv.iden (mem_hyps_pos (List.mem_cons_self ..)))
        · exact hd.rename (fun θ hθ => by
            rcases List.mem_cons.mp hθ with rfl | hθ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (by
                simp only [hyps, List.map_cons, List.append_eq, List.mem_append,
                  List.mem_cons] at hθ ⊢
                tauto)))).rename (fun θ hθ => by
        simp only [List.mem_singleton] at hθ; subst hθ
        exact List.mem_cons_self ..)
    · exact (e₂.weakest ψ hψ (by
        refine ndCut (φ := erasePos P |>.or (erasePos Q)) ?_ ?_
        · exact Deriv.orIntro2 (Deriv.iden (mem_hyps_pos (List.mem_cons_self ..)))
        · exact hd.rename (fun θ hθ => by
            rcases List.mem_cons.mp hθ with rfl | hθ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (by
                simp only [hyps, List.map_cons, List.append_eq, List.mem_append,
                  List.mem_cons] at hθ ⊢
                tauto)))).rename (fun θ hθ => by
        simp only [List.mem_singleton] at hθ; subst hθ
        exact List.mem_cons_self ..)

/-! ## The inversion phase terminates -/

mutual
/-- Size of a positive, for the inversion measure. -/
def sizePos : Pos → Nat
  | .atom _ => 1
  | .fls    => 1
  | .or p q => sizePos p + sizePos q + 1
  | .down _ => 1
/-- Negatives contribute nothing: `downL` files them into `Γ`, which the
measure does not count. -/
def sizeNeg : Neg → Nat
  | _ => 0
end

/-- The measure of the pending list. -/
def sizeΩ : List Pos → Nat
  | []      => 0
  | P :: Ω  => sizePos P + sizeΩ Ω

/-- **The remaining obligation**: an existential interpolant at *stable*
sequents.  Everything else is discharged by the clauses above.

This is where Pitts' work lives: at a stable sequent the focusing choices
(which hypothesis to focus on, and the `impL` sub-derivation) reintroduce
material, so the recursion needs Dyckhoff's weight rather than the crude size
used for the inversion phase. Stated as an explicit hypothesis, never a
`sorry`, so every result below carries it visibly. -/
abbrev StableInterp (p : String) : Type :=
  ∀ Γ : List Neg, ExInterp p Γ []

/-- **The inversion phase, assembled.**  Given interpolants at stable sequents,
the four clauses above build them for every antecedent, by recursion on
`sizeΩ`. -/
def exInterp_of_stable {p : String} (hst : StableInterp p) :
    ∀ (n : Nat) (Γ : List Neg) (Ω : List Pos), sizeΩ Ω ≤ n → ExInterp p Γ Ω
  | _, Γ, [], _ => hst Γ
  | 0, _, P :: _, h => absurd h (by
      cases P <;> simp [sizeΩ, sizePos])
  | n + 1, Γ, P :: Ω, h => by
      cases P with
      | atom a =>
          exact cl_atomL (exInterp_of_stable hst n _ Ω (by
            simp only [sizeΩ, sizePos] at h; omega))
      | fls => exact cl_fls p Γ Ω
      | down M =>
          exact cl_downL (exInterp_of_stable hst n _ Ω (by
            simp only [sizeΩ, sizePos] at h; omega))
      | or A B =>
          refine cl_orL (exInterp_of_stable hst n Γ (A :: Ω) ?_)
            (exInterp_of_stable hst n Γ (B :: Ω) ?_) <;>
            (simp only [sizeΩ, sizePos] at h ⊢; omega)

/-- **Uniform interpolation for IPC, `∃p` half — modulo `StableInterp`.**
Every antecedent has a `p`-free weakest consequence. -/
def uniform_interpolation_IPC {p : String} (hst : StableInterp p)
    (Γ : List Neg) (Ω : List Pos) : ExInterp p Γ Ω :=
  exInterp_of_stable hst (sizeΩ Ω) Γ Ω (le_refl _)

/-! ## `∀p`: the missing half

The universal interpolant of a goal: the **strongest** `p`-free formula that
entails it. Mutually recursive with `ExInterp`, for the reason given below. -/

/-- A universal interpolant for `p` at the goal `N`. -/
structure AllInterp (p : String) (N : Neg) where
  /-- The interpolant. -/
  fml : PLLFormula
  /-- It is `p`-free. -/
  pfree : PFree p fml
  /-- It entails the goal. -/
  sound : Deriv [fml] (eraseNeg N)
  /-- It is the strongest such: any `p`-free formula entailing the goal
  entails it. -/
  strongest : ∀ ψ, PFree p ψ → Deriv [ψ] (eraseNeg N) → Deriv [ψ] fml

/-- **A `p`-free goal is its own universal interpolant.**  The base case, and
the only one that needs no recursion. -/
def allInterp_pfree {p : String} {N : Neg} (h : PFree p (eraseNeg N)) :
    AllInterp p N where
  fml := eraseNeg N
  pfree := h
  sound := Deriv.iden (List.mem_cons_self ..)
  strongest := fun _ _ hd => hd

/-- **`∀p` commutes with conjunction.**  The clause for `and`, proved
outright. -/
def allInterp_and {p : String} {M N : Neg}
    (a : AllInterp p M) (b : AllInterp p N) : AllInterp p (.and M N) where
  fml := .and a.fml b.fml
  pfree := ⟨a.pfree, b.pfree⟩
  sound := by
    refine Deriv.andIntro ?_ ?_
    · exact Deriv.cutHead (Deriv.andElim1 (Deriv.iden (List.mem_cons_self ..)))
        a.sound
    · exact Deriv.cutHead (Deriv.andElim2 (Deriv.iden (List.mem_cons_self ..)))
        b.sound
  strongest := by
    intro ψ hψ hd
    refine Deriv.andIntro ?_ ?_
    · exact a.strongest ψ hψ (Deriv.andElim1 hd)
    · exact b.strongest ψ hψ (Deriv.andElim2 hd)

/-- **The remaining obligation, and it is the whole of Pitts.**

The clause for an implication goal `Q ⊃ N`. The obvious candidate
`(∃p Q) ⊃ (∀p N)` is *sound* but **not minimal**: given `p`-free `ψ` with
`ψ ⊢ Q ⊃ N`, one would have to recover `Q` from `∃p Q`, which is strictly
weaker. Dyckhoff's weight argument is what repairs this, and with it the
mutual recursion `∃p ↔ ∀p` terminates.

Stated as an explicit hypothesis, never a `sorry`, and **not** discharged by
importing the repository's `existsP`: doing so would supply the formula from
Pitts' recursion rather than from these clauses, which is precisely the
shortcut this file exists to avoid. -/
abbrev ImpInterp (p : String) : Type :=
  ∀ (Q : Pos) (N : Neg), ExInterp p [] [Q] → AllInterp p N →
    AllInterp p (.imp Q N)

/-! ## What the control experiment showed

Run against `LJF◯`, three things came out, and they are the reason for doing
it:

1. **The clause list is right.**  Every left-inversion clause — `cl_fls`,
   `cl_downL`, `cl_atomL`, `cl_orL` — is provable outright, in IPC and (as
   `cθ_*` in `PLLCandOr.lean`) in PLL.  The two calculi discharge them the same
   way, which is the evidence that the shared structure is real rather than
   coincidental.

2. **The right rules contribute nothing**, and that is a theorem-level fact,
   not an omission: `ExInterp` does not mention the goal, so `impR`/`andR`
   (and `circR` in `LJF◯`) have no clause to discharge.  This is uniformity
   made structural — the interpolant is built from the antecedent alone.

3. **`cl_orL` is not the hard clause after all.**  The PLL campaign traced its
   difficulty to the join clause; here the join clause is four lines, exactly
   as `cθ_orL` was.  What is hard, in both logics, is the **stable** case —
   and in `LJF◯` the stable case is where `circL` lives.  So the honest reading
   of the PLL programme is that `∨` localises the difficulty *within the
   inversion phase*, while the real obstruction sits one level down, in the
   focusing choices at stable sequents.

## The gap the control experiment found

`StableInterp` was stated above as if it were a leaf of the recursion. **It is
not**, and that is the finding.

At a stable sequent the only way to use a hypothesis `Q ⊃ N ∈ Γ` is `LFoc.impL`,
whose first premise is `Stab Γ Q` — a **goal-directed** subproblem. (This is
Dyckhoff's case: in `G4ip` the antecedent `(A₁ ⊃ A₂) ⊃ B` has premise
`A₂ ⊃ B, A₁ ⇒ A₂`.) So computing the `p`-free content of an antecedent
requires knowing the `p`-free content of a *goal*, which `ExInterp` does not
provide.

**Therefore `∃p` and `∀p` are mutually recursive, and the structure as built is
incomplete.**  `AllInterp` below is the missing half. This was invisible while
only the inversion clauses were in view — every one of those goes through with
`ExInterp` alone — and it would have been carried into the PLL development
unnoticed had the IPC control not been built. That is what the experiment was
for.

## Where the difficulty actually localises

With both halves present, the clauses split sharply:

* `allInterp_pfree`, `allInterp_and` — **proved below**, unconditionally;
* `cl_fls`, `cl_downL`, `cl_atomL`, `cl_orL` — **proved above**;
* the **implication clause of `∀p`** — open, and it is the whole of Pitts.

For `imp Q N` the obvious candidate `(∃p Q) ⊃ (∀p N)` has the right soundness
but **fails minimality**: from a `p`-free `ψ` with `ψ ⊢ Q ⊃ N` one cannot
recover `Q` from `∃p Q`, which is weaker. Repairing that is exactly Dyckhoff's
weight argument, and it is a project rather than a step — the Coq mechanisation
of Pitts (Férée–van der Giessen–van Gool–Shillito 2024) is a full paper.

Nothing here imports the repository's existing interpolant (`existsP` over
`G4c`, `wip/final.lean`). That construction would inhabit `StableInterp`
immediately, but using it would make this machinery decorative: the formula
would come from Pitts' recursion rather than from these clauses. The point of
the exercise is a construction that *emerges from the proof* — which `ExInterp`
and `AllInterp` do, being Σ-types whose `fml` field is built by the clauses.

**For PLL, `circL` is the only rule in the stable phase that IPC lacks.** So the
control experiment has localised the entire difference between the two logics,
for uniform-interpolation purposes, to one rule of one phase — on top of a core
difficulty that both logics share and neither has here.
-/

end IPC

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'IPC.soundInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IPC.soundInv

/-- info: 'IPC.cl_orL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IPC.cl_orL

/-- info: 'IPC.cl_downL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IPC.cl_downL

/-- info: 'IPC.exInterp_of_stable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IPC.exInterp_of_stable

/-- info: 'IPC.uniform_interpolation_IPC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IPC.uniform_interpolation_IPC

/-- info: 'IPC.allInterp_and' depends on axioms: [propext] -/
#guard_msgs in
#print axioms IPC.allInterp_and

/-- info: 'IPC.allInterp_pfree' does not depend on any axioms -/
#guard_msgs in
#print axioms IPC.allInterp_pfree
