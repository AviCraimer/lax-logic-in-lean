/-!
# `LJF`: a focused calculus for intuitionistic logic, from the ground up

This file is **self-contained on purpose**.  It imports nothing from the rest
of the development: not `Deriv`, not `G4c`, not the existing interpolation
machinery.  Everything `LJF` needs — weakening, identity expansion, cut — is
built here, for `LJF`, from its own rules.

Matthew's instruction (2026-08-08), and the reason for it:

* the *technique* is what is under test, so borrowing cut-admissibility or
  completeness from another calculus would measure that calculus's metatheory
  rather than this one's;
* a self-contained development reads as a single argument, which a patchwork
  of imports from three calculi does not;
* and reuse is the exact shape of the back-door that nearly imported the
  existing interpolant through `existsP`.

## Naming

`LJF` is Liang–Miller's focused intuitionistic calculus.  What is built here is
the **canonical-polarity instance** of it: every connective sits at its own
polarity (`∨`, `⊥`, atoms positive; `⊃`, `∧` negative) and atoms are *not*
assignable.  Full `LJF` allows the polarity of atoms to be chosen; that freedom
is not needed here and is not implemented, so this is faithful to `LJF` as a
fragment, not as the whole system.  The lax extension in `PLLFocused.lean` is
`LJF◯` — `LJF` plus `◯` and the second judgment.

## The four judgments

    Inv    Γ ; Ω ⇒ N      inversion (asynchronous) phase
    Stab   Γ     ⇒ P      stable sequent: nothing left to invert
    RFocus Γ    ⇒ [P]     right focus on a positive goal
    LFoc   Γ [N] ⇒ P      left focus on a negative hypothesis

`Γ` is the stable context of negatives, `Ω` the queue of positives still to be
inverted.  Focus is entered only at a stable sequent, and left only at a shift.
-/


namespace LJF

/-! ## Polarised syntax -/

mutual
/-- Positive (synchronous) propositions. -/
inductive Pos where
  | atom : String → Pos
  | fls  : Pos
  | or   : Pos → Pos → Pos
  | down : Neg → Pos
  deriving DecidableEq
/-- Negative (asynchronous) propositions. -/
inductive Neg where
  | up   : Pos → Neg
  | imp  : Pos → Neg → Neg
  | and  : Neg → Neg → Neg
  deriving DecidableEq
end

/-! ## The calculus -/

mutual

/-- A **stable sequent**: `Ω` is empty and the goal is positive, so the only
moves left are to focus, on the right or on a hypothesis. -/
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

/-- **Inversion.**  Right rules act on the goal, left rules on the head of
`Ω`; `stable` is the exit, available only when `Ω` is empty and the goal is a
shift.  `Ω` is a stack: the head-only discipline is canonical because every
inversion rule is invertible, so the processing order is immaterial. -/
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

/-! ## Contexts: the subset relation

Contraction and exchange are free because the context is used by membership;
only weakening needs an argument, and one traversal gives all three. -/

/-- `Γ'` contains everything in `Γ`. -/
def Sub (Γ Γ' : List Neg) : Prop := ∀ N, N ∈ Γ → N ∈ Γ'

namespace Sub

theorem refl (Γ : List Neg) : Sub Γ Γ := fun _ h => h

theorem trans {Γ Γ' Γ'' : List Neg} (h₁ : Sub Γ Γ') (h₂ : Sub Γ' Γ'') :
    Sub Γ Γ'' := fun N h => h₂ N (h₁ N h)

/-- Extending both sides by the same hypothesis. -/
theorem cons {Γ Γ' : List Neg} (X : Neg) (h : Sub Γ Γ') :
    Sub (X :: Γ) (X :: Γ') := by
  intro N hN
  rcases List.mem_cons.mp hN with rfl | hN
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (h N hN)

/-- Extending the target. -/
theorem grow {Γ : List Neg} (X : Neg) : Sub Γ (X :: Γ) :=
  fun _ h => List.mem_cons_of_mem _ h

end Sub

/-! ## Weakening

One mutual traversal, structural in the derivation. -/

mutual

/-- Weakening of a stable sequent. -/
def Stab.wk : {Γ Γ' : List Neg} → {P : Pos} → Sub Γ Γ' → Stab Γ P → Stab Γ' P
  | _, _, _, H, .rfoc d   => .rfoc (RFocus.wk H d)
  | _, _, _, H, .lfoc h d => .lfoc (H _ h) (LFoc.wk H d)

/-- Weakening under right focus. -/
def RFocus.wk : {Γ Γ' : List Neg} → {P : Pos} → Sub Γ Γ' → RFocus Γ P → RFocus Γ' P
  | _, _, _, H, .init h => .init (H _ h)
  | _, _, _, H, .or1 d  => .or1 (RFocus.wk H d)
  | _, _, _, H, .or2 d  => .or2 (RFocus.wk H d)
  | _, _, _, H, .rel d  => .rel (Inv.wk H d)

/-- Weakening under left focus. -/
def LFoc.wk : {Γ Γ' : List Neg} → {N : Neg} → {P : Pos} →
    Sub Γ Γ' → LFoc Γ N P → LFoc Γ' N P
  | _, _, _, _, H, .rel d    => .rel (Inv.wk H d)
  | _, _, _, _, H, .impL a d => .impL (Stab.wk H a) (LFoc.wk H d)
  | _, _, _, _, H, .and1 d   => .and1 (LFoc.wk H d)
  | _, _, _, _, H, .and2 d   => .and2 (LFoc.wk H d)

/-- Weakening of an inversion sequent. -/
def Inv.wk : {Γ Γ' : List Neg} → {Ω : List Pos} → {N : Neg} →
    Sub Γ Γ' → Inv Γ Ω N → Inv Γ' Ω N
  | _, _, _, _, H, .impR d   => .impR (Inv.wk H d)
  | _, _, _, _, H, .andR d e => .andR (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, H, .stable d => .stable (Stab.wk H d)
  | _, _, _, _, H, .orL d e  => .orL (Inv.wk H d) (Inv.wk H e)
  | _, _, _, _, _, .flsL     => .flsL
  | _, _, _, _, H, .downL d  => .downL (Inv.wk (Sub.cons _ H) d)
  | _, _, _, _, H, .atomL d  => .atomL (Inv.wk (Sub.cons _ H) d)

end

/-! ## Size

The measure for identity expansion (and, later, for cut on the cut formula).
Shifts cost one, so `sizeNeg M < sizePos (down M)` and `sizePos P <
sizeNeg (up P)`: crossing a shift always makes the formula strictly smaller,
which is what lets the two expansions call each other. -/

mutual
/-- Size of a positive. -/
def sizePos : Pos → Nat
  | .atom _  => 1
  | .fls     => 1
  | .or P Q  => sizePos P + sizePos Q + 1
  | .down N  => sizeNeg N + 1
/-- Size of a negative. -/
def sizeNeg : Neg → Nat
  | .up P    => sizePos P + 1
  | .imp P N => sizePos P + sizeNeg N + 1
  | .and M N => sizeNeg M + sizeNeg N + 1
end

theorem sizePos_pos (P : Pos) : 0 < sizePos P := by
  cases P <;> simp [sizePos] <;> omega

theorem sizeNeg_pos (N : Neg) : 0 < sizeNeg N := by
  cases N <;> simp [sizeNeg] <;> omega

/-! ## Identity expansion

`LJF`'s only axiom is `init`, at atoms.  That every proposition entails itself
is therefore a **theorem**, and it is proved by the two functions below, which
are the two halves of the same induction on the formula.

* `posRestore Q` says: *inverting `Q` on the left gives it back on the right*.
  To prove `Γ; Q,Ω ⇒ N` it suffices to prove `Γ'; Ω ⇒ N` in the extended
  context `Γ'` produced by inverting `Q`, **with a right focus on `Q` in hand**.
  This is the precise sense in which left inversion loses nothing.

* `idNegK N` says: *if `N` is usable, `N` is provable*.  Given a continuation
  that turns any left focus on `N` into a stable sequent, it builds `Γ ⇒ N`.

The continuations are what make the two mutually recursive without any cut:
`posRestore` hands its caller a `RFocus`, and `idNegK` consumes an `LFoc`. -/

mutual

/-- **Left inversion of a positive returns it on the right.** -/
def posRestore (Q : Pos) (Γ : List Neg) (Ω : List Pos) (N : Neg)
    (k : ∀ Γ', Sub Γ Γ' → RFocus Γ' Q → Inv Γ' Ω N) : Inv Γ (Q :: Ω) N :=
  match Q, k with
  | .atom a, k =>
      .atomL (k (.up (.atom a) :: Γ) (Sub.grow _) (.init (List.mem_cons_self ..)))
  | .fls, _ => .flsL
  | .down M, k =>
      .downL (k (M :: Γ) (Sub.grow _)
        (.rel (idNegK M (M :: Γ)
          (fun _ _ hs lf => .lfoc (hs _ (List.mem_cons_self ..)) lf))))
  | .or P₁ P₂, k =>
      .orL (posRestore P₁ Γ Ω N (fun Γ' hs r => k Γ' hs (.or1 r)))
           (posRestore P₂ Γ Ω N (fun Γ' hs r => k Γ' hs (.or2 r)))
termination_by sizePos Q
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos]
  all_goals omega

/-- **A usable negative is a provable negative.** -/
def idNegK (N : Neg) (Γ : List Neg)
    (k : ∀ Γ' P, Sub Γ Γ' → LFoc Γ' N P → Stab Γ' P) : Inv Γ [] N :=
  match N, k with
  | .up P, k =>
      .stable (k Γ P (Sub.refl Γ)
        (.rel (posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r)))))
  | .imp Q M, k =>
      .impR (posRestore Q Γ [] M (fun Γ' hs r =>
        idNegK M Γ' (fun Γ'' P hs' lf =>
          k Γ'' P (Sub.trans hs hs') (.impL (.rfoc (RFocus.wk hs' r)) lf))))
  | .and M₁ M₂, k =>
      .andR (idNegK M₁ Γ (fun Γ' P hs lf => k Γ' P hs (.and1 lf)))
            (idNegK M₂ Γ (fun Γ' P hs lf => k Γ' P hs (.and2 lf)))
termination_by sizeNeg N
decreasing_by
  all_goals simp_wf
  all_goals simp only [sizePos, sizeNeg]
  all_goals omega

end

/-- **Identity, negative form**: every hypothesis proves itself. -/
def idNeg (N : Neg) (Γ : List Neg) (h : N ∈ Γ) : Inv Γ [] N :=
  idNegK N Γ (fun _ _ hs lf => .lfoc (hs _ h) lf)

/-- **Identity, positive form**: `P ⇒ P`, with `P` inverted on the left and
focused on the right. -/
def idPos (P : Pos) (Γ : List Neg) : Inv Γ [P] (.up P) :=
  posRestore P Γ [] (.up P) (fun _ _ r => .stable (.rfoc r))


/-! # Part 2: the uniform interpolant, by weighted recursion

## Where the weight enters, and why it is necessary

The interpolant must be **uniform**: one `p`-free formula per antecedent,
serving every goal and every derivation at once.  So it cannot be defined by
recursion on a derivation — it must be defined by recursion on the *sequent*,
following the rules of the calculus applied backwards.

A naive structural measure does not survive that recursion, because the
clauses do not merely decompose — they **transform**:

* currying `(M₁∧M₂ ⊃ N) ↝ (M₁ ⊃ (M₂ ⊃ N))` preserves the naive size;
* splitting `(Q₁∨Q₂ ⊃ N) ↝ (Q₁ ⊃ N), (Q₂ ⊃ N)` *duplicates* `N`;
* inverting a goal `Q ⊃ N` moves `Q` into the context, which *grows*.

The weight repairs all three at once.  Each connective is assigned a cost —
here `atom = ⊥ = 1`, `∨` and `⊃` and `↓` cost `+1`, `∧` costs `+3`, `↑` costs
`0` — and a context is measured by `Σ 3^(weight)`.  The exponential is doing
the work of a multiset order: replacing one hypothesis of weight `w` by at
most two hypotheses of weight `≤ w − 1` drops the sum, because
`2·3^(w−1) < 3^w`.  The costs themselves are **solved for** from the clause
set: each clause contributes an inequality (currying forces `∧ ≥ 3` given the
shift costs; goal-inversion forces `3^{wQ} + 3^{wN} < 3^{wQ+wN+1}`, true since
both weights are positive), and the assignment above is a solution.  Dyckhoff's
weights for `G4ip` are a solution to the same kind of system for a different
rule set; ours differ because the shifts change the clause set.

Why it is necessary and not merely convenient: termination of proof *search*
could be had by loop-checking, but a loop-checker yields no formula.  The
interpolant is *built by* the recursion, so its existence needs structural
well-foundedness — the weight is what turns "the calculus terminates" into
"the interpolant exists".  It is also what buys predicativity: the
interpolation candidate is a least fixed point, and Girard-style candidates
take such fixed points impredicatively; the weight lets this one be reached by
well-founded recursion instead.
-/


/-! ## The weight -/

mutual
/-- Weight of a positive.  `atom = ⊥ = 1`; `∨` costs `+1`; `↓` costs `+1`. -/
def wPos : Pos → Nat
  | .atom _ => 1
  | .fls    => 1
  | .or P Q => wPos P + wPos Q + 1
  | .down M => wNeg M + 1
/-- Weight of a negative.  `↑` costs `0`; `⊃` costs `+1`; `∧` costs `+3`
(currying `(M₁∧M₂ ⊃ N) ↝ (M₁ ⊃ (M₂ ⊃ N))` forces `∧ > ⊃ + ↓`, given `↓ = 1`). -/
def wNeg : Neg → Nat
  | .up P    => wPos P
  | .imp Q N => wPos Q + wNeg N + 1
  | .and M N => wNeg M + wNeg N + 3
end

theorem wPos_pos (P : Pos) : 0 < wPos P := by
  cases P <;> simp [wPos] <;> omega

theorem wNeg_pos (N : Neg) : 0 < wNeg N := by
  cases N with
  | up P => simpa [wNeg] using wPos_pos P
  | imp Q N => simp only [wNeg]; omega
  | and M N => simp only [wNeg]; omega

/-! ## Powers of three: the little arithmetic kit, from scratch -/

theorem p3_pos (n : Nat) : 0 < 3 ^ n := Nat.pow_pos (by omega)

theorem p3_mono {a b : Nat} (h : a ≤ b) : 3 ^ a ≤ 3 ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem p3_strict {a b : Nat} (h : a < b) : 3 ^ a < 3 ^ b := by
  calc 3 ^ a < 3 ^ a * 3 := by have := p3_pos a; omega
    _ = 3 ^ (a + 1) := by rw [Nat.pow_succ]
    _ ≤ 3 ^ b := p3_mono (by omega)

/-- Two summands strictly under the bound: `3^a + 3^b < 3^c` when `a,b < c`. -/
theorem p3_add {a b c : Nat} (ha : a < c) (hb : b < c) :
    3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a < 3^c` when `a < c`. -/
theorem p3_2 {a c : Nat} (ha : a + 1 ≤ c) : 2 * 3 ^ a < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 1) := p3_mono (by omega)
  have h3 : 3 ^ c = 3 ^ (c - 1) * 3 := by
    rw [← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 1)
  omega

/-- `2·3^a + 3^b < 3^c` when `a + 2 ≤ c` and `b + 1 ≤ c`. -/
theorem p3_21 {a b c : Nat} (ha : a + 2 ≤ c) (hb : b + 1 ≤ c) :
    2 * 3 ^ a + 3 ^ b < 3 ^ c := by
  have h1 : 3 ^ a ≤ 3 ^ (c - 2) := p3_mono (by omega)
  have h2 : 3 ^ b ≤ 3 ^ (c - 2) * 3 := by
    have : 3 ^ b ≤ 3 ^ (c - 1) := p3_mono (by omega)
    have e : 3 ^ (c - 1) = 3 ^ (c - 2) * 3 := by
      rw [← Nat.pow_succ]; congr 1; omega
    omega
  have h3 : 3 ^ c = 3 ^ (c - 2) * 3 * 3 := by
    rw [← Nat.pow_succ, ← Nat.pow_succ]; congr 1; omega
  have := p3_pos (c - 2)
  omega

/-! ## Context measure -/

/-- `Σ 3^(weight)` over a context. -/
def sum3 : List Neg → Nat
  | []     => 0
  | N :: Γ => 3 ^ wNeg N + sum3 Γ

theorem sum3_append (Γ Δ : List Neg) :
    sum3 (Γ ++ Δ) = sum3 Γ + sum3 Δ := by
  induction Γ with
  | nil => simp [sum3]
  | cons N Γ ih => simp [sum3, ih]; omega

/-! ## Inversion of a positive, as data

`invertPos Q` is the list of **branches** produced by fully inverting `Q` on
the left; each branch is the list of stable hypotheses it contributes.
`⊥` has no branches; `∨` concatenates; an atom or a shift is one branch with
one hypothesis. -/

def invertPos : Pos → List (List Neg)
  | .atom a  => [[.up (.atom a)]]
  | .fls     => []
  | .or P Q  => invertPos P ++ invertPos Q
  | .down M  => [[M]]

/-- Each branch weighs no more than the positive it came from. -/
theorem invertPos_le : ∀ (P : Pos), ∀ b ∈ invertPos P, sum3 b ≤ 3 ^ wPos P
  | .atom a, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp [sum3, wNeg, wPos]
  | .fls, b, hb => by simp [invertPos] at hb
  | .or P Q, b, hb => by
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.le_trans (invertPos_le P b hb)
          (p3_mono (by simp only [wPos]; omega))
      · exact Nat.le_trans (invertPos_le Q b hb)
          (p3_mono (by simp only [wPos]; omega))
  | .down M, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega
termination_by P => sizePos P
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- For a non-atomic positive the inequality is strict — this is what makes
moving a hypothesis's branches into the context a descent. -/
theorem invertPos_lt {P : Pos} (h : ∀ a, P ≠ .atom a) :
    ∀ b ∈ invertPos P, sum3 b < 3 ^ wPos P := by
  cases P with
  | atom a => exact absurd rfl (h a)
  | fls => intro b hb; simp [invertPos] at hb
  | or P Q =>
      intro b hb
      simp only [invertPos, List.mem_append] at hb
      rcases hb with hb | hb
      · exact Nat.lt_of_le_of_lt (invertPos_le P b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos Q; omega))
      · exact Nat.lt_of_le_of_lt (invertPos_le Q b hb)
          (p3_strict (by simp only [wPos]; have := wPos_pos P; omega))
  | down M =>
      intro b hb; simp [invertPos] at hb; subst hb
      simp only [sum3, wPos]
      have := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
      omega

/-! ## Positional splits

`splits Γ` lists each member of `Γ` together with the rest of the context —
the tool by which the saturated clauses consume a hypothesis without needing
decidable equality on formulas. -/

def splits : List Neg → List (Neg × List Neg)
  | []     => []
  | X :: Γ => (X, Γ) :: (splits Γ).map (fun ⟨Y, rest⟩ => (Y, X :: rest))

theorem splits_sum {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → sum3 Γ = 3 ^ wNeg X + sum3 rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; rfl
      · cases hEq
        simp only [sum3, ih hZ]; omega

theorem splits_mem {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → X ∈ Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact List.mem_cons_self ..
      · cases hEq; exact List.mem_cons_of_mem _ (ih hZ)



/-! ## Interpolant connectives

The interpolant is a formula of `LJF` itself, carried as a `Neg` (hypotheses
are negative).  Disjunction of negatives goes through the shifts. -/

/-- `⊤` as a negative: `⊥ ⊃ ⊥`. -/
def nTop : Neg := .imp .fls (.up .fls)
/-- `⊥` as a negative. -/
def nBot : Neg := .up .fls
/-- Conjunction of interpolants. -/
def nAnd (M N : Neg) : Neg := .and M N
/-- Disjunction of interpolants: `↑(↓M ∨ ↓N)`. -/
def nOr (M N : Neg) : Neg := .up (.or (.down M) (.down N))
/-- Conjunction of a list, unit `⊤`. -/
def nAndAll : List Neg → Neg := fun l => l.foldr nAnd nTop
/-- Disjunction of a list, unit `⊥`. -/
def nOrAll : List Neg → Neg := fun l => l.foldr nOr nBot

/-- `p`-guard: the unit `C` when the atom is `p`, else `D`.  A named helper
so the aggregate match-arms stay opaque applications, which keeps the
functional-induction cases clean. -/
def pGuard (p a : String) (C D : Neg) : Neg := if a = p then C else D

/-- The head disjunct of an atomic goal: nothing if the atom is `p`. -/
def atomHead (p q : String) : List Neg := if q = p then [] else [.up (.atom q)]

/-- Is the atom `a` a hypothesis (as `↑a`)? -/
def atomMem (a : String) (Γ : List Neg) : Bool :=
  Γ.any (fun | .up (.atom b) => a == b | _ => false)

/-! ## The fire scan

A parked implication `a ⊃ N` fires as soon as its atom is present.  The scan
walks the positional splits and returns the first firable one. -/

def findFire (full : List Neg) : List (Neg × List Neg) → Option (String × Neg × List Neg)
  | [] => none
  | (X, rest) :: more =>
    match X with
    | .imp (.atom a) N =>
        if atomMem a full then some (a, N, rest) else findFire full more
    | _ => findFire full more

theorem findFire_mem {full : List Neg} :
    ∀ {l : List (Neg × List Neg)} {a N rest},
      findFire full l = some (a, N, rest) → (Neg.imp (.atom a) N, rest) ∈ l := by
  intro l
  induction l with
  | nil => intro a N rest h; simp [findFire] at h
  | cons XR more ih =>
      intro a N rest h
      obtain ⟨X, R⟩ := XR
      match X, h with
      | .imp (.atom b) N', h => ?_
      | .up P, h => exact List.mem_cons_of_mem _ (ih h)
      | .imp .fls N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.or Q₁ Q₂) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .imp (.down M) N', h => exact List.mem_cons_of_mem _ (ih h)
      | .and M₁ M₂, h => exact List.mem_cons_of_mem _ (ih h)
      simp only [findFire] at h
      by_cases hM : atomMem b full
      · simp [hM] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact List.mem_cons_self ..
      · simp [hM] at h
        exact List.mem_cons_of_mem _ (ih h)

/-- Goal component of the measure. -/
def goalW : Option Neg → Nat
  | none   => 0
  | some G => 3 ^ wNeg G

/-! ## The descent lemmas

One lemma per clause of the recursion below, each stating its measure descent
in exactly the shape the termination checker asks for.  Together they are the
spent form of the weight inequalities. -/

theorem dec_park {t d e : Nat} : 2 * t + (3 ^ e + d) < 2 * (3 ^ e + t) + d := by
  have := p3_pos e; omega

theorem dec_drop {t e : Nat} : t < 3 ^ e + t := by
  have := p3_pos e; omega

theorem dec_shift1 {m t : Nat} : 3 ^ m + t < 3 ^ (m + 1) + t := by
  have := p3_strict (a := m) (b := m + 1) (by omega); omega

theorem dec_and {m n t : Nat} :
    3 ^ m + (3 ^ n + t) < 3 ^ (m + n + 3) + t := by
  have := p3_add (a := m) (b := n) (c := m + n + 3) (by omega) (by omega)
  omega

theorem dec_impor {a b n t : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    3 ^ (a + n + 1) + (3 ^ (b + n + 1) + t) < 3 ^ (a + b + 1 + n + 1) + t := by
  have := p3_add (a := a + n + 1) (b := b + n + 1) (c := a + b + 1 + n + 1)
    (by omega) (by omega)
  omega

theorem dec_stripshift {x n t : Nat} :
    3 ^ (x + n + 1) + t < 3 ^ (x + 1 + n + 1) + t := by
  have := p3_strict (a := x + n + 1) (b := x + 1 + n + 1) (by omega); omega

theorem dec_curry {m₁ m₂ n t : Nat} :
    3 ^ (m₁ + 1 + (m₂ + 1 + n + 1) + 1) + t <
      3 ^ (m₁ + m₂ + 3 + 1 + n + 1) + t := by
  have := p3_strict (a := m₁ + 1 + (m₂ + 1 + n + 1) + 1)
    (b := m₁ + m₂ + 3 + 1 + n + 1) (by omega)
  omega

theorem dec_orctx {P Q : Pos} {b : List Neg} {t : Nat}
    (hb : b ∈ invertPos (Pos.or P Q)) :
    sum3 b + t < 3 ^ (wPos P + wPos Q + 1) + t := by
  have h := invertPos_lt (P := Pos.or P Q) (by intro a h; nomatch h) b hb
  simp only [wPos] at h; omega

theorem dec_fire {done rest : List Neg} {a : String} {N : Neg}
    (hf : findFire done (splits done) = some (a, N, rest)) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum (findFire_mem hf)
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_qimp {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_qimp_g {done rest : List Neg} {a : String} {N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.atom a) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_qimp h) (by omega)

theorem dec_dyk1 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + 0 := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_21 (a := wNeg N' + 1 + wNeg N + 1) (b := wPos Q' + wNeg N' + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega) (by have := wNeg_pos N; omega)
  omega

theorem dec_dyk1_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest +
        3 ^ (wPos Q' + wNeg N' + 1) <
      2 * 0 + sum3 done + g := by
  have := dec_dyk1 h; omega

theorem dec_dyk0 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ (wNeg N' + 1 + wNeg N + 1) + 0) + sum3 rest + 0 <
      2 * 0 + sum3 done + 0 := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N' + 1 + wNeg N + 1)
    (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; omega)
  omega

theorem dec_dyk2 {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega

theorem dec_dyk2_g {done rest : List Neg} {Q' : Pos} {N' N : Neg} {g : Nat}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * (3 ^ wNeg N + 0) + sum3 rest < 2 * 0 + sum3 done + g :=
  Nat.lt_of_lt_of_le (dec_dyk2 h) (by omega)

theorem dec_orA {P Q : Pos} {b todo : List Neg} {d g : Nat}
    (hb : b ∈ invertPos (Pos.or P Q)) :
    2 * (sum3 b + sum3 todo) + d + 0 <
      2 * (3 ^ (wPos P + wPos Q + 1) + sum3 todo) + d + g := by
  have h1 := invertPos_lt (P := Pos.or P Q) (fun a h => Pos.noConfusion h) b hb
  simp only [wPos] at h1
  omega

theorem dec_ainv0 {Q : Pos} {b : List Neg} {N : Neg} {d : Nat}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + d + 0 < 2 * 0 + d + 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have := p3_2 (a := wPos Q) (c := wPos Q + wNeg N + 1)
    (by have := wNeg_pos N; omega)
  omega

theorem dec_ainv {Q : Pos} {b : List Neg} {N : Neg} {d : Nat}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + d + 3 ^ wNeg N < 2 * 0 + d + 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have := p3_21 (a := wPos Q) (b := wNeg N) (c := wPos Q + wNeg N + 1)
    (by have := wNeg_pos N; omega) (by have := wPos_pos Q; omega)
  omega



/-! ## The uniform interpolant

One recursion computes both quantifiers.  `interp p todo done goal`:

* `goal = none` — **`∃p` mode**: the strongest `p`-free consequence of the
  context `todo ++ done`;
* `goal = some G` — **`∀p` mode**: the weakest `p`-free hypothesis that,
  beside the context, suffices for `G`.

`todo` is the unprocessed part of the context; `done` holds the parked
members, which come in exactly three shapes — atoms `↑a`, implications
`a ⊃ N` whose atom is not yet available, and the Dyckhoff implications
`↓(Q' ⊃ N') ⊃ N`.

The processing clauses consume the head of `todo` and replace it by strictly
lighter material (the residual): this is where each weight inequality is
spent, and each clause is annotated with its inequality.  The aggregate
clauses (at `todo = []`) first fire any parked implication whose atom has
arrived, then read the interpolant off the saturated context.

The measure is `2·sum3 todo + sum3 done + goalW goal`: parking moves a
hypothesis from the doubled side to the single side, so even the bookkeeping
steps are strict, and no lexicographic order is needed. -/

set_option maxHeartbeats 2000000 in
def interp (p : String) : (todo done : List Neg) → (goal : Option Neg) → Neg
  -- ── processing phase: consume the head of `todo` ──
  -- park an atom
  | .up (.atom a) :: todo, done, g =>
      interp p todo (.up (.atom a) :: done) g
  -- absurd hypothesis: `∨` over no branches is `⊥`, `∧` over none is `⊤`
  | .up .fls :: _, _, none => nBot
  | .up .fls :: _, _, some _ => nTop
  -- context split: `∨` of branch results in `∃p` mode, `∧` in `∀p` mode
  -- [sum3 b < 3^(w P∨Q), both branches]
  | .up (.or P Q) :: todo, done, none =>
      nOrAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ => interp p (b ++ todo) done none))
  -- context split in ∀p mode: each branch conjunct guarded by the branch's
  -- ∃p, for the same reason as the implication goal — minimality would
  -- otherwise demand deriving one branch's ∀p from another branch's ∃p.
  | .up (.or P Q) :: todo, done, some G =>
      nAndAll ((invertPos (.or P Q)).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p (b ++ todo) done none))
            (interp p (b ++ todo) done (some G))))
  -- a shifted negative moves into the context  [w M < w ↑↓M = w M + 1]
  | .up (.down M) :: todo, done, g =>
      interp p (M :: todo) done g
  -- a conjunction splits  [3^wM + 3^wN < 3^(wM+wN+3)]
  | .and M N :: todo, done, g =>
      interp p (M :: N :: todo) done g
  -- `⊥ ⊃ N` is inert: drop it
  | .imp .fls _ :: todo, done, g =>
      interp p todo done g
  -- `a ⊃ N` parks until its atom arrives
  | .imp (.atom a) N :: todo, done, g =>
      interp p todo (.imp (.atom a) N :: done) g
  -- `(Q₁∨Q₂) ⊃ N` splits  [3^(wQ₁+wN+1) + 3^(wQ₂+wN+1) < 3^(wQ₁+wQ₂+1+wN+1)]
  | .imp (.or Q₁ Q₂) N :: todo, done, g =>
      interp p (.imp Q₁ N :: .imp Q₂ N :: todo) done g
  -- `↓↑P' ⊃ N` strips the double shift  [w drops by 1]
  | .imp (.down (.up P')) N :: todo, done, g =>
      interp p (.imp P' N :: todo) done g
  -- currying: `↓(M₁∧M₂) ⊃ N  ↝  ↓M₁ ⊃ (↓M₂ ⊃ N)`  [w: +5 vs +4 — the
  -- inequality that forces `∧` to cost 3]
  | .imp (.down (.and M₁ M₂)) N :: todo, done, g =>
      interp p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done g
  -- the Dyckhoff implication parks
  | .imp (.down (.imp Q' N')) N :: todo, done, g =>
      interp p todo (.imp (.down (.imp Q' N')) N :: done) g
  -- ── aggregate phase: `todo` exhausted ──
  | [], done, g =>
    match hf : findFire done (splits done) with
    -- a parked `a ⊃ N` whose atom has arrived fires  [3^wN < 3^(wN+2)]
    | some (_, N, rest) => interp p [N] rest g
    | none =>
      match g with
      -- ∃p mode: conjunction over the saturated context
      | none =>
          nAndAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
            match X with
            -- a surviving atom is its own p-free content
            | .up (.atom a) => pGuard p a nTop (.up (.atom a))
            -- `a ⊃ N`, atom absent: guard the recursion by the atom
            | .imp (.atom a) N =>
                pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
            -- the Dyckhoff implication: what it yields, guarded by what
            -- the goal interpolant of its antecedent demands — PAIRED with
            -- the ∃p of the residual station, which the minimality
            -- dispatch projects (third clause the (ii) induction forced;
            -- sound because done ⊢ res via resSim)
            | .imp (.down (.imp Q' N')) N =>
                nAnd
                  (.imp (.down (interp p [.imp (.down N') N] rest
                                 (some (.imp Q' N'))))
                       (interp p [N] rest none))
                  (interp p [.imp (.down N') N] rest none)
            -- unreachable shapes park nothing
            | _ => nTop))
      -- ∀p mode: by the goal
      | some G =>
        match G with
        -- goal inversion  [2·sum3 b + 3^wN < 3^(wQ+wN+1)]
        -- ∀p at an implication goal: each branch conjunct is GUARDED by the
        -- branch's ∃p — without the guard, minimality fails (it would demand
        -- E(Γ) ⊢ E(Γ+b), which is false); with it, soundness still closes
        -- because eSound supplies the guard.  This is the clause the (ii)
        -- induction forces.
        | .imp Q N =>
            nAndAll ((invertPos Q).attach.map
              (fun ⟨b, hb⟩ =>
                .imp (.down (interp p b done none))
                  (interp p b done (some N))))
        | .and M N =>
            nAnd (interp p [] done (some M)) (interp p [] done (some N))
        -- context attacks: ways the saturated context can advance any goal;
        -- inlined per goal shape so each aggregate case is self-contained
        | .up (.atom q) =>
            if atomMem q done then nTop
            else nOrAll (atomHead p q ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.atom q))))
              | _, _ => nBot))
        | .up .fls =>
            nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up Pos.fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up Pos.fls)))
              | _, _ => nBot))
        | .up (.or P₁ P₂) =>
            nOrAll ([interp p [] done (some (.up P₁)),
                     interp p [] done (some (.up P₂))] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.or P₁ P₂))))
              | _, _ => nBot))
        | .up (.down M) =>
            nOrAll ([interp p [] done (some M)] ++
              (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (Pos.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (Pos.down M))))
              | _, _ => nBot))
  termination_by todo done goal => 2 * sum3 todo + sum3 done + goalW goal
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_drop
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact p3_strict (by first
          | omega
          | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
          | (have := wNeg_pos M; have := wNeg_pos N; omega))
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact dec_fire (by assumption)
      | exact dec_qimp (by assumption)
      | exact dec_qimp_g (by assumption)
      | exact dec_dyk1 (by assumption)
      | (have h1 := dec_dyk1 (by assumption); omega)
      | exact dec_dyk1_g (by assumption)
      | exact dec_dyk2 (by assumption)
      | exact dec_dyk2_g (by assumption)
      | exact dec_ainv (by assumption)
      | exact dec_ainv0 (by assumption)
      | exact dec_orA (by assumption)
      | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)


/-! ## `p`-freeness -/

mutual
/-- The atom `p` does not occur (positives). -/
def PFreeP (p : String) : Pos → Prop
  | .atom a  => a ≠ p
  | .fls     => True
  | .or P Q  => PFreeP p P ∧ PFreeP p Q
  | .down M  => PFreeN p M
/-- The atom `p` does not occur (negatives). -/
def PFreeN (p : String) : Neg → Prop
  | .up P    => PFreeP p P
  | .imp Q N => PFreeP p Q ∧ PFreeN p N
  | .and M N => PFreeN p M ∧ PFreeN p N
end

theorem pfree_nTop {p : String} : PFreeN p nTop := by
  simp [nTop, PFreeN, PFreeP]

theorem pfree_nBot {p : String} : PFreeN p nBot := by
  simp [nBot, PFreeN, PFreeP]

theorem pfree_nAnd {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nAnd M N) :=
  ⟨hM, hN⟩

theorem pfree_nOr {p : String} {M N : Neg}
    (hM : PFreeN p M) (hN : PFreeN p N) : PFreeN p (nOr M N) :=
  ⟨hM, hN⟩

theorem pfree_nAndAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nAndAll l) := by
  induction l with
  | nil => exact pfree_nTop
  | cons x l ih =>
      exact pfree_nAnd (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_nOrAll {p : String} {l : List Neg}
    (h : ∀ x ∈ l, PFreeN p x) : PFreeN p (nOrAll l) := by
  induction l with
  | nil => exact pfree_nBot
  | cons x l ih =>
      exact pfree_nOr (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem pfree_pGuard {p a : String} {C D : Neg}
    (hC : PFreeN p C) (hD : a ≠ p → PFreeN p D) : PFreeN p (pGuard p a C D) := by
  unfold pGuard; split
  · exact hC
  · exact hD (by assumption)

theorem pfree_atomHead {p q : String} : ∀ x ∈ atomHead p q, PFreeN p x := by
  unfold atomHead; split
  · intro x hx; exact absurd hx (List.not_mem_nil)
  · intro x hx
    rcases List.mem_singleton.mp hx with rfl
    rename_i h
    simpa only [PFreeN, PFreeP] using h

/-- **The interpolant never mentions `p`.**  Every clause either keeps `p` out
by construction, or is guarded by the `a == p` test that replaces the would-be
conjunct or disjunct by its unit. -/
theorem interp_pfree (p : String) :
    ∀ (todo done : List Neg) (g : Option Neg), PFreeN p (interp p todo done g) := by
  intro todo done g
  fun_induction interp p todo done g with
  | case1 => assumption
  | case2 => exact pfree_nBot
  | case3 => exact pfree_nTop
  | case4 =>
      rename_i ih
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      exact ih b hb
  | case5 =>
      rename_i ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      refine ⟨?_, ?_⟩ <;>
        first | exact ih1 b hb | exact ih2 b | exact ih1 b | exact ih2 b hb
  | case6 => assumption
  | case7 => assumption
  | case8 => assumption
  | case9 => assumption
  | case10 => assumption
  | case11 => assumption
  | case12 => assumption
  | case13 => assumption
  | case14 => assumption
  | case15 =>
      rename_i ih4 ih3 ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P =>
          cases P with
          | atom a =>
              exact pfree_pGuard pfree_nTop
                (fun h => by simpa only [PFreeN, PFreeP] using h)
          | fls => exact pfree_nTop
          | or _ _ => exact pfree_nTop
          | down _ => exact pfree_nTop
      | imp Q N =>
          cases Q with
          | atom a =>
              exact pfree_pGuard pfree_nTop
                (fun h => ⟨h, by
                  first
                  | exact ih4 rest a N hXr
                  | exact ih3 rest a N hXr
                  | exact ih2 rest a N hXr
                  | exact ih1 rest a N hXr⟩)
          | fls => exact pfree_nTop
          | or _ _ => exact pfree_nTop
          | down M =>
              cases M with
              | up _ => exact pfree_nTop
              | and _ _ => exact pfree_nTop
              | imp Q' N' =>
                  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
                    first
                    | exact ih1 rest Q' N' N hXr
                    | exact ih2 rest Q' N' N hXr
                    | exact ih3 rest Q' N' N hXr
                    | exact ih4 rest Q' N' N hXr
      | and _ _ => exact pfree_nTop
  | case16 =>
      rename_i ih2 ih1
      apply pfree_nAndAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨b, hb⟩, rfl⟩ := hx
      refine ⟨?_, ?_⟩ <;>
        first | exact ih1 b hb | exact ih2 b | exact ih1 b | exact ih2 b hb
  | case17 => exact ⟨by assumption, by assumption⟩
  | case18 => exact pfree_nTop
  | case19 =>
      rename_i q hq ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact pfree_atomHead x hx
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case20 =>
      rename_i ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      simp only [List.mem_map, List.mem_attach, true_and] at hx
      obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
      cases X with
      | up P => cases P <;> exact pfree_nBot
      | imp Q N =>
          cases Q with
          | atom a =>
              exact pfree_pGuard pfree_nBot
                (fun h => pfree_nAnd h (ih3 rest a N hXr))
          | fls => exact pfree_nBot
          | or _ _ => exact pfree_nBot
          | down M =>
              cases M with
              | up _ => exact pfree_nBot
              | and _ _ => exact pfree_nBot
              | imp Q' N' =>
                  exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
      | and _ _ => exact pfree_nBot
  | case21 =>
      rename_i ihP ihQ ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ihP
        · rcases List.mem_singleton.mp hx with rfl
          exact ihQ
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot
  | case22 =>
      rename_i ihM ih3 ih2 ih1
      apply pfree_nOrAll
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · rcases List.mem_singleton.mp hx with rfl
        exact ihM
      · simp only [List.mem_map, List.mem_attach, true_and] at hx
        obtain ⟨⟨⟨X, rest⟩, hXr⟩, rfl⟩ := hx
        cases X with
        | up P => cases P <;> exact pfree_nBot
        | imp Q N =>
            cases Q with
            | atom a =>
                exact pfree_pGuard pfree_nBot
                  (fun h => pfree_nAnd h (ih3 rest a N hXr))
            | fls => exact pfree_nBot
            | or _ _ => exact pfree_nBot
            | down M =>
                cases M with
                | up _ => exact pfree_nBot
                | and _ _ => exact pfree_nBot
                | imp Q' N' =>
                    exact pfree_nAnd (ih2 rest Q' N' N hXr) (ih1 rest Q' N' N hXr)
        | and _ _ => exact pfree_nBot

/-! ## The contract that remains

With `interp` total and `interp_pfree` proved, the components of the Σ-type
are in place: the formula, built by the clauses, and its `p`-freeness.  The
characteristic properties are the remaining obligations, stated as the
contract for the next stretch — all four internal to `LJF`, none touching
another calculus:

* **(E1) soundness of `∃p`**:
  `Inv (todo ++ done) [] (interp p todo done none)`
* **(A1) soundness of `∀p`**:
  `Inv (interp p todo done (some G) :: todo ++ done) [] G`
* **(E2) minimality of `∃p`**: for `p`-free `Δ` and `ψ`,
  `Inv (todo ++ done ++ Δ) [] ψ  →  Inv (interp p todo done none :: Δ) [] ψ`
* **(A2) minimality of `∀p`**: for `p`-free `Δ`,
  `Inv (todo ++ done ++ Δ) [] G  →
     Inv (interp p todo done none :: Δ) [] (interp p todo done (some G))`

**Status (2026-08-09, final)**: E1 and A1 are `eSound`/`aSound`, proved
unconditionally in Part 4.  E2 and A2 are `eMinF`/`aMinF` in Part 6, proved
unconditionally — the saturated case is discharged inline, and the
statements `SatE2`/`SatA2` naming it are discharged as `satE2`/`satA2`.  The minimality analysis also
forced the E-guards on the two branching `∀p` clauses of `interp`.

The toolkit they need, also internal: a hypothesis-simulation traversal
(replace uses of one hypothesis by a derived simulator — powers E1/A1 and the
easy inversion directions of E2/A2), and branch extraction
(`Inv Δ (P :: Ω) C → ∀ b ∈ invertPos P, Inv (b ++ Δ) Ω C`, from the
determinism of the inversion phase).  The one expected mountain is the
`E2`/`A2` case for the Dyckhoff implication — the focused form of the
`(A⊃B)⊃C` argument; if it resists, it is to be carried as an explicit
hypothesis, never a `sorry`. -/


/-! # Part 3: the toolkit for the characteristic properties

Six tools, each internal to `LJF`, each structural, none using cut:

* `routeStab` — CPS re-targeting of a stable proof of a positive `P`: every
  right focus on `P` is handed to a continuation, every left-focus chain and
  goal-side inversion is rebuilt with the new target.  Its instances do the
  work classically assigned to cut: shift release, disjunction routing,
  ex falso from a provable `⊥`.
* `invBranches` — realise `invertPos` on the left: branch derivations
  assemble into the inversion of the positive.
* `extract` — the converse, at any position of `Ω`: the inversion phase is
  deterministic, so a pending positive can be replayed along any one branch.
* `stableFire` — fire a shifted hypothesis `↑R` at a stable sequent, given
  stable continuations for every branch of `R`.
* `upMerge` — eliminate a shifted hypothesis into a negative goal, by
  recursion on the goal; the leaf case is `stableFire`.
* `simStab` — hypothesis simulation: replace every use of one hypothesis
  `H` by derivations manufactured on the other side.  The `init` uses of an
  atomic `H` reduce to left-focus uses via `idPos`, so one handler covers
  everything.
-/

/-! ## Routing a positive conclusion -/

mutual

/-- Re-target a stable proof: any right focus on `P` is passed to `k`. -/
def routeStab {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ P → Stab Δ P₀
  | _, hs, .rfoc r => k hs r
  | _, hs, .lfoc h lf => .lfoc h (routeLFoc k hs lf)

/-- Re-target below a left focus. -/
def routeLFoc {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ → LFoc Δ H P → LFoc Δ H P₀
  | _, _, hs, .rel d => .rel (routeInv k hs d)
  | _, _, hs, .impL s lf => .impL s (routeLFoc k hs lf)
  | _, _, hs, .and1 lf => .and1 (routeLFoc k hs lf)
  | _, _, hs, .and2 lf => .and2 (routeLFoc k hs lf)

/-- Re-target through the inversion of a released antecedent.  The goal is a
shift, so `impR`/`andR` cannot occur and the traversal is total. -/
def routeInv {Δ₀ : List Neg} {P P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → RFocus Δ' P → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω (.up P) → Inv Δ Ω (.up P₀)
  | _, _, hs, .stable s => .stable (routeStab k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (routeInv k hs d₁) (routeInv k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (routeInv k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (routeInv k (hs.trans (Sub.grow _)) d)

end

/-- Disjunction introduction at the stable level, left side. -/
def stabOr1 {Δ : List Neg} {A B : Pos} (s : Stab Δ A) : Stab Δ (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or1 r)) (Sub.refl Δ) s

/-- Disjunction introduction at the stable level, right side. -/
def stabOr2 {Δ : List Neg} {A B : Pos} (s : Stab Δ B) : Stab Δ (.or A B) :=
  routeStab (Δ₀ := Δ) (fun _ r => .rfoc (.or2 r)) (Sub.refl Δ) s

/-! ## Forced-shape extractors -/

/-- An inversion with empty `Ω` and shifted goal must be `stable`. -/
def unStable {Δ : List Neg} {P : Pos} : Inv Δ [] (.up P) → Stab Δ P
  | .stable s => s

/-- A right focus on a shift must be `rel`. -/
def relOf {Δ : List Neg} {M : Neg} : RFocus Δ (.down M) → Inv Δ [] M
  | .rel d => d

/-- An inversion with empty `Ω` and implication goal must be `impR`. -/
def impROf {Δ : List Neg} {Q : Pos} {N : Neg} :
    Inv Δ [] (.imp Q N) → Inv Δ [Q] N
  | .impR d => d

/-- An inversion with empty `Ω` and conjunction goal must be `andR`: left. -/
def andROf1 {Δ : List Neg} {M N : Neg} : Inv Δ [] (.and M N) → Inv Δ [] M
  | .andR d _ => d

/-- Right. -/
def andROf2 {Δ : List Neg} {M N : Neg} : Inv Δ [] (.and M N) → Inv Δ [] N
  | .andR _ e => e

/-! ## Realising and replaying the inversion of a positive -/

/-- Branch derivations assemble into the inversion of the positive. -/
def invBranches : ∀ (R : Pos) {Γ : List Neg} {Ω : List Pos} {N : Neg},
    (∀ b ∈ invertPos R, Inv (b ++ Γ) Ω N) → Inv Γ (R :: Ω) N
  | .atom a, _, _, _, h =>
      .atomL (h [.up (.atom a)] (by simp [invertPos]))
  | .fls, _, _, _, _ => .flsL
  | .or P Q, _, _, _, h =>
      .orL (invBranches P (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inl hb)))
           (invBranches Q (fun b hb =>
              h b (by simp only [invertPos, List.mem_append]; exact .inr hb)))
  | .down M, _, _, _, h => .downL (h [M] (by simp [invertPos]))
termination_by R => sizePos R
decreasing_by all_goals (simp_wf; simp only [sizePos]; omega)

/-- **Replay along a branch.**  A pending positive anywhere in `Ω` can be
extracted along any one branch of its inversion — the inversion phase is
deterministic, so the derivation already contains that branch. -/
def extract : ∀ {Γ : List Neg} (Ω₁ : List Pos) {R : Pos} {Ω₂ : List Pos}
    {C : Neg}, Inv Γ (Ω₁ ++ R :: Ω₂) C →
    ∀ b ∈ invertPos R, Inv (b ++ Γ) (Ω₁ ++ Ω₂) C
  -- extraction point at the head
  | _, [], .atom a, _, _, .atomL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  | _, [], .fls, _, _, .flsL, b, hb => by simp [invertPos] at hb
  | _, [], .or P Q, _, _, .orL d₁ d₂, b, hb =>
      if hP : b ∈ invertPos P then extract [] d₁ b hP
      else extract [] d₂ b (by
        simp only [invertPos, List.mem_append] at hb
        exact hb.resolve_left hP)
  | _, [], .down M, _, _, .downL d, b, hb => by
      simp only [invertPos, List.mem_singleton] at hb; subst hb; exact d
  -- goal rules commute past the extraction point
  | _, [], _, _, _, .impR d, b, hb => .impR (extract [_] d b hb)
  | _, [], _, _, _, .andR d e, b, hb => .andR (extract [] d b hb) (extract [] e b hb)
  | _, S :: Ω₁, _, _, _, .impR d, b, hb => .impR (extract (_ :: S :: Ω₁) d b hb)
  | _, S :: Ω₁, _, _, _, .andR d e, b, hb =>
      .andR (extract (S :: Ω₁) d b hb) (extract (S :: Ω₁) e b hb)
  -- left rules on the head of `Ω₁` are rebuilt
  | _, .or _ _ :: Ω₁, _, _, _, .orL d₁ d₂, b, hb =>
      .orL (extract (_ :: Ω₁) d₁ b hb) (extract (_ :: Ω₁) d₂ b hb)
  | _, .fls :: _, _, _, _, .flsL, _, _ => .flsL
  | _, .down M :: Ω₁, _, _, _, .downL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.downL
  | _, .atom a :: Ω₁, _, _, _, .atomL d, b, hb =>
      (extract Ω₁ d b hb).wk (fun X hX => by
        rcases List.mem_append.mp hX with hX | hX
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ hX)
        · rcases List.mem_cons.mp hX with rfl | hX
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ hX))
      |> Inv.atomL



/-! ## Firing a shifted hypothesis, and merging its branches -/

/-- Fire `↑R ∈ Δ` at a stable sequent: stable continuations for every branch
of `R` assemble into one stable proof. -/
def stableFire {Δ : List Neg} {R : Pos} {P₀ : Pos} (h : Neg.up R ∈ Δ)
    (s : ∀ b ∈ invertPos R, Stab (b ++ Δ) P₀) : Stab Δ P₀ :=
  .lfoc h (.rel (invBranches R (fun b hb => .stable (s b hb))))

/-- **Eliminate a shifted hypothesis into a negative goal.**  By recursion on
the goal: implications invert their antecedent (`invBranches`) and push the
branch family through (`extract` + reordering), conjunctions project, and at
a shifted goal the hypothesis fires (`stableFire`).  This subsumes ex falso
(`R = ⊥`: the branch family is vacuous), disjunction elimination, and the
inversion of a shifted hypothesis. -/
def upMerge : ∀ (G : Neg) {Γ : List Neg} {R : Pos}, Neg.up R ∈ Γ →
    (∀ b ∈ invertPos R, Inv (b ++ Γ) [] G) → Inv Γ [] G
  | .imp Q N, Γ, R, h, D =>
      .impR (invBranches Q (fun c hc =>
        upMerge N (List.mem_append_right c h) (fun b hb =>
          (extract [] (impROf (D b hb)) c hc).wk (fun X hX => by
            rcases List.mem_append.mp hX with hX | hX
            · exact List.mem_append_right _ (List.mem_append_left _ hX)
            · rcases List.mem_append.mp hX with hX | hX
              · exact List.mem_append_left _ hX
              · exact List.mem_append_right _ (List.mem_append_right _ hX)))))
  | .and M N, _, _, h, D =>
      .andR (upMerge M h (fun b hb => andROf1 (D b hb)))
            (upMerge N h (fun b hb => andROf2 (D b hb)))
  | .up P, _, _, h, D =>
      .stable (stableFire h (fun b hb => unStable (D b hb)))

/-! ## Hypothesis simulation

Replace every use of one hypothesis `H` by material manufactured on the
target side.  A use is either a left focus on `H` — handled by `fl` — or, for
atomic `H`, an `init`; the latter reduces to the former through `idPos`, so
`fl` alone suffices. -/

theorem memBoth {H M : Neg} {Γ Δ : List Neg}
    (hm : ∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) :
    ∀ X, X ∈ M :: Γ → X = H ∨ X ∈ M :: Δ := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact .inr (List.mem_cons_self ..)
  · exact (hm X hX).imp id (List.mem_cons_of_mem _)

mutual

/-- Simulation at a stable sequent. -/
def simStab {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → Stab Γ P → Stab Δ P
  | _, _, _, hm, hs, .rfoc r => simRFocus fl hm hs r
  | _, _, _, hm, hs, @Stab.lfoc _ _ N h lf =>
      if e : N = H then fl hs (e ▸ simLFoc fl hm hs lf)
      else .lfoc ((hm _ h).resolve_left e) (simLFoc fl hm hs lf)

/-- Simulation under right focus.  Returns a stable proof, because an `init`
use of an atomic `H` must be re-routed through `fl` (via `idPos`), and that
produces a stable proof, not a focus. -/
def simRFocus {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → RFocus Γ P → Stab Δ P
  | _, _, _, hm, hs, @RFocus.init _ a h =>
      if e : Neg.up (.atom a) = H then fl hs (e ▸ LFoc.rel (idPos (.atom a) _))
      else .rfoc (.init ((hm _ h).resolve_left e))
  | _, _, _, hm, hs, .or1 r => stabOr1 (simRFocus fl hm hs r)
  | _, _, _, hm, hs, .or2 r => stabOr2 (simRFocus fl hm hs r)
  | _, _, _, hm, hs, .rel d => .rfoc (.rel (simInv fl hm hs d))

/-- Simulation under a left focus on some other hypothesis. -/
def simLFoc {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {H' : Neg} {P : Pos}, (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) →
      Sub Δ₀ Δ → LFoc Γ H' P → LFoc Δ H' P
  | _, _, _, _, hm, hs, .rel d => .rel (simInv fl hm hs d)
  | _, _, _, _, hm, hs, .impL s lf =>
      .impL (simStab fl hm hs s) (simLFoc fl hm hs lf)
  | _, _, _, _, hm, hs, .and1 lf => .and1 (simLFoc fl hm hs lf)
  | _, _, _, _, hm, hs, .and2 lf => .and2 (simLFoc fl hm hs lf)

/-- Simulation through inversion. -/
def simInv {H : Neg} {Δ₀ : List Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P) :
    ∀ {Γ Δ : List Neg} {Ω : List Pos} {C : Neg},
      (∀ X, X ∈ Γ → X = H ∨ X ∈ Δ) → Sub Δ₀ Δ → Inv Γ Ω C → Inv Δ Ω C
  | _, _, _, _, hm, hs, .impR d => .impR (simInv fl hm hs d)
  | _, _, _, _, hm, hs, .andR d e =>
      .andR (simInv fl hm hs d) (simInv fl hm hs e)
  | _, _, _, _, hm, hs, .stable s => .stable (simStab fl hm hs s)
  | _, _, _, _, hm, hs, .orL d₁ d₂ =>
      .orL (simInv fl hm hs d₁) (simInv fl hm hs d₂)
  | _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, hm, hs, .downL d =>
      .downL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)
  | _, _, _, _, hm, hs, .atomL d =>
      .atomL (simInv fl (memBoth hm) (hs.trans (Sub.grow _)) d)

end

/-- The common instantiation: strip the head hypothesis, simulating its
uses. -/
def simHyp {H : Neg} {Γ Δ₀ : List Neg} {C : Neg}
    (fl : ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' → LFoc Δ' H P → Stab Δ' P)
    (hΓ : Sub Γ Δ₀) (d : Inv (H :: Γ) [] C) : Inv Δ₀ [] C :=
  simInv fl (fun X hX => (List.mem_cons.mp hX).imp id (hΓ X)) (Sub.refl Δ₀) d

/-! ## Interpolant-connective introductions and eliminations -/

/-- `⊤` needs nothing. -/
def nTopIntro {Γ : List Neg} : Inv Γ [] nTop := .impR .flsL

/-- Conjunction of a list, introduction. -/
def nAndAllIntro : ∀ {l : List Neg} {Γ : List Neg},
    (∀ x ∈ l, Inv Γ [] x) → Inv Γ [] (nAndAll l)
  | [], _, _ => nTopIntro
  | x :: l, _, h =>
      .andR (h x (List.mem_cons_self ..))
        (nAndAllIntro (fun y hy => h y (List.mem_cons_of_mem _ hy)))

/-- Focused projection out of a list conjunction. -/
def lfocAndAll : ∀ {l : List Neg} {x : Neg} {Δ : List Neg} {P : Pos},
    x ∈ l → LFoc Δ x P → LFoc Δ (nAndAll l) P
  | y :: l, x, _, _, hx, lf =>
      if e : x = y then .and1 (e ▸ lf)
      else .and2 (lfocAndAll (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) lf)

/-- Disjunction of a list, introduction at a member. -/
def nOrAllIntro : ∀ {l : List Neg} {x : Neg} {Γ : List Neg},
    x ∈ l → Inv Γ [] x → Inv Γ [] (nOrAll l)
  | y :: l, x, _, hx, d =>
      if e : x = y then .stable (.rfoc (.or1 (.rel (e ▸ d))))
      else .stable (.rfoc (.or2 (.rel (nOrAllIntro (by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd rfl e
        · exact hx) d))))

/-- Disjunction of a list, elimination: a case per member. -/
def nOrAllElim : ∀ {l : List Neg} {Γ : List Neg} (G : Neg), nOrAll l ∈ Γ →
    (∀ x ∈ l, ∀ {Γ' : List Neg}, Sub Γ Γ' → Inv (x :: Γ') [] G) → Inv Γ [] G
  | [], _, G, h, _ =>
      upMerge G (R := .fls) h (fun b hb => by simp [invertPos] at hb)
  | x :: l, Γ, G, h, D =>
      upMerge G h (fun b hb =>
        if e : b = [x] then
          e ▸ (D x (List.mem_cons_self ..) (Sub.refl _) |>.wk
            (fun Y hY => by
              rcases List.mem_cons.mp hY with rfl | hY
              · exact List.mem_append_left _ (List.mem_cons_self ..)
              · exact List.mem_append_right _ hY))
        else by
          have hb' : b = [nOrAll l] := by
            simp only [invertPos, List.mem_append, List.mem_singleton] at hb
            exact hb.resolve_left e
          subst hb'
          exact nOrAllElim G (List.mem_append_left _ (List.mem_cons_self ..))
            (fun y hy _ hs => D y (List.mem_cons_of_mem _ hy)
              (fun Z hZ => hs Z (List.mem_cons_of_mem _ hZ))))

/-- A `true` `atomMem` is a membership. -/
theorem atomMem_mem {a : String} {Γ : List Neg} (h : atomMem a Γ = true) :
    Neg.up (.atom a) ∈ Γ := by
  simp only [atomMem, List.any_eq_true] at h
  obtain ⟨x, hx, he⟩ := h
  match x, he with
  | .up (.atom b), he =>
      have : a = b := by simpa [BEq.comm] using he
      subst this; exact hx



/-! # Part 4: soundness of both modes

`eSound`: the context proves its `∃p` interpolant.  `aSound`: the `∀p`
interpolant, beside the context, proves the goal.  Mutual, by the same
weighted recursion as `interp` itself.  This section: the support layer. -/

/-! ## Small membership lemmas -/

theorem subPark {X : Neg} {t d : List Neg} :
    Sub (t ++ X :: d) (X :: (t ++ d)) := by
  intro N h
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

theorem subParkInv {X : Neg} {t d : List Neg} :
    Sub (X :: (t ++ d)) (t ++ X :: d) := by
  intro N h
  simp only [List.mem_append, List.mem_cons] at h ⊢
  rcases h with h | h | h
  · exact .inr (.inl h)
  · exact .inl h
  · exact .inr (.inr h)

theorem splits_sub {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → Sub rest Γ := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨Z, rest'⟩, hZ, hEq⟩
      · cases h; exact Sub.grow Y
      · cases hEq; exact Sub.cons Y (ih hZ)

theorem findFire_atom {full : List Neg} :
    ∀ {l : List (Neg × List Neg)} {a N rest},
      findFire full l = some (a, N, rest) → atomMem a full = true := by
  intro l
  induction l with
  | nil => intro a N rest h; simp [findFire] at h
  | cons XR more ih =>
      intro a N rest h
      obtain ⟨X, R⟩ := XR
      match X, h with
      | .imp (.atom b) N', h => ?_
      | .up P, h => exact ih h
      | .imp .fls N', h => exact ih h
      | .imp (.or Q₁ Q₂) N', h => exact ih h
      | .imp (.down M) N', h => exact ih h
      | .and M₁ M₂, h => exact ih h
      simp only [findFire] at h
      by_cases hM : atomMem b full
      · simp [hM] at h; obtain ⟨rfl, _, _⟩ := h; exact hM
      · simp [hM] at h; exact ih h

/-! ## The residual simulator

Uses of the residual `↓N′ ⊃ N` are manufactured from the Dyckhoff hypothesis
`↓(Q′ ⊃ N′) ⊃ N` itself: a use supplies a stable proof of `↓N′`; routing it
(`routeStab`) releases an inversion of `N′`, which — weakened under the
inversion of `Q′` — rebuilds the stronger antecedent `↓(Q′ ⊃ N′)`, and the
hypothesis fires.  This is the derivability of `(A⊃B)⊃C ⊢ B⊃C`, in focused
form, with no cut. -/

def resSim {Q' : Pos} {N' N : Neg} {Δ₀ : List Neg}
    (hX : Neg.imp (.down (.imp Q' N')) N ∈ Δ₀) :
    ∀ {Δ' : List Neg} {P : Pos}, Sub Δ₀ Δ' →
      LFoc Δ' (.imp (.down N') N) P → Stab Δ' P
  | _, _, hs, .impL s' lf'' =>
      routeStab
        (k := fun {Δ''} hs' r =>
          .lfoc (hs' _ (hs _ hX))
            (.impL
              (.rfoc (.rel (.impR (invBranches Q' (fun c _ =>
                (relOf r).wk (fun Z hZ => List.mem_append_right c hZ))))))
              (lf''.wk hs')))
        (Sub.refl _) s'

/-! ## The attack handlers

Each attack disjunct of a `∀p` interpolant, once produced by `nOrAllElim`,
is consumed by one of these.  They take the interpolant premises as
arguments, so they sit outside the mutual recursion. -/

/-- Attack via `a ⊃ N ∈ Γ'`: the disjunct `↑a ∧ A″` supplies the atom (left
component) and the continuation interpolant (right component). -/
def atkQimp {a : String} {N A'' G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and (.up (.atom a)) A'' ∈ Γ')
    (hX : Neg.imp (.atom a) N ∈ Γ')
    (hrest : Sub rest Γ')
    (DN : Inv (A'' :: N :: rest) [] G) : Inv Γ' [] G :=
  -- strip A″ (project the right component), then N (fire the implication,
  -- proving its atom from the left component)
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (.lfoc (hs _ hx) (.and1 (.rel (idPos (.atom a) _)))) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      DN)



/-- Attack via the Dyckhoff hypothesis: the disjunct `A₁ ∧ A₂` supplies the
antecedent interpolant (left component) and the continuation interpolant
(right component). -/
def atkDyk {Q' : Pos} {N' N A₁ A₂ G : Neg} {rest Γ' : List Neg}
    (hx : Neg.and A₁ A₂ ∈ Γ')
    (hX : Neg.imp (.down (.imp Q' N')) N ∈ Γ')
    (hrest : Sub rest Γ')
    (D₁ : Inv (A₁ :: .imp (.down N') N :: rest) [] (.imp Q' N'))
    (D₂ : Inv (A₂ :: N :: rest) [] G) : Inv Γ' [] G :=
  -- the antecedent Q′ ⊃ N′, residual uses simulated from the hypothesis
  let dM' : Inv Γ' [] (.imp Q' N') :=
    simHyp (fl := resSim hX) (Sub.refl Γ')
      (simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and1 lf))
        (Sub.cons _ hrest)
        D₁)
  -- main line: strip A₂ (right component), then N (fire the hypothesis)
  simHyp
    (fl := fun hs lf => .lfoc (hs _ hX)
      (.impL (.rfoc (.rel (dM'.wk hs))) lf))
    (Sub.refl Γ')
    (simHyp
      (fl := fun hs lf =>
        .lfoc (hs _ (List.mem_cons_of_mem _ hx)) (.and2 lf))
      (Sub.cons N hrest)
      D₂)

/-- Choice-free witness for membership in a mapped list: the witness is
*found* by scanning, since `∃`-elimination cannot target `Type`. -/
def memMapWitness {α β : Type} [DecidableEq β] (f : α → β) :
    ∀ (l : List α) (y : β), y ∈ l.map f → {a : α // a ∈ l ∧ f a = y}
  | a :: l, y, h =>
      if e : f a = y then ⟨a, List.mem_cons_self .., e⟩
      else
        have h' : y ∈ l.map f := by
          simp only [List.map_cons, List.mem_cons] at h
          exact h.resolve_left (fun hy => e hy.symm)
        let ⟨w, hw, he⟩ := memMapWitness f l y h'
        ⟨w, List.mem_cons_of_mem _ hw, he⟩



/-! ## Reusable context shuffles -/

theorem subBranch1 {b t d : List Neg} {X : Neg} :
    Sub ((b ++ t) ++ d) (b ++ (X :: (t ++ d))) := by
  intro Z hZ
  simp only [List.mem_append, List.mem_cons] at hZ ⊢
  rcases hZ with (hZ | hZ) | hZ
  · exact .inl hZ
  · exact .inr (.inr (.inl hZ))
  · exact .inr (.inr (.inr hZ))

theorem subBranch2 {b t d : List Neg} {X Y : Neg} :
    Sub ((b ++ t) ++ d) (b ++ (X :: Y :: (t ++ d))) := by
  intro Z hZ
  simp only [List.mem_append, List.mem_cons] at hZ ⊢
  rcases hZ with (hZ | hZ) | hZ
  · exact .inl hZ
  · exact .inr (.inr (.inr (.inl hZ)))
  · exact .inr (.inr (.inr (.inr hZ)))

/-- `⊥` as a hypothesis proves anything. -/
def nBotElim {Γ : List Neg} (G : Neg) (h : nBot ∈ Γ) : Inv Γ [] G :=
  upMerge G (R := .fls) h (fun _ hb => by simp [invertPos] at hb)

/-- The fire step of `aSound`, one term for every goal shape: the fired
`a ⊃ N'` is simulated through the context, its atom argument coming from
the saturated station, and the recursive derivation at the residual
station is weakened back in. -/
def fireASound {p : String} {done : List Neg} {a : String} {N' : Neg}
    {rest : List Neg} {G : Neg}
    (hf : findFire done (splits done) = some (a, N', rest))
    (rec : Inv (interp p [N'] rest (some G) :: ([N'] ++ rest)) [] G) :
    Inv (interp p [N'] rest (some G) :: done) [] G :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_of_mem _
          (splits_mem (findFire_mem hf))))
        (.impL (.rfoc (.init (hs _ (List.mem_cons_of_mem _
          (atomMem_mem (findFire_atom hf)))))) lf))
    (Sub.cons _ (splits_sub (findFire_mem hf)))
    (rec.wk (by
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))

/-! ## Soundness of both modes

`eSound`: the context proves its `∃p` interpolant.
`aSound`: the `∀p` interpolant, beside the context, proves the goal.
Mutual, by the same weighted recursion as `interp`; every case is a
construction — no inner induction over derivations is needed for soundness. -/

set_option hygiene false in
/-- The decreasing farm of the soundness mutual (`eSound`/`aSound`). Hygiene is off so entries naming call-site variables resolve there. -/
macro "ljf_dec_sound" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_drop
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact p3_strict (by first
          | omega
          | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
          | (have := wNeg_pos M; have := wNeg_pos N; omega))
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact dec_fire (by assumption)
      | exact dec_qimp (by assumption)
      | exact dec_qimp_g (by assumption)
      | exact dec_dyk1 (by assumption)
      | (have h1 := dec_dyk1 (by assumption); omega)
      | exact dec_dyk1_g (by assumption)
      | exact dec_dyk2 (by assumption)
      | exact dec_dyk2_g (by assumption)
      | exact dec_ainv (by assumption)
      | exact dec_ainv0 (by assumption)
      | exact dec_orA (by assumption)
      | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_park) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk1 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk1_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk2 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_dyk2_g (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_ainv (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_ainv0 (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_orctx (by assumption)) (by omega)))

set_option hygiene false in
/-- The decreasing farm of the E-side traversal (`eMinF` and the `T*` family). One definition, eight uses; edit here to tune all farms. -/
macro "ljf_dec_e" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_add_right _ _)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h1 := dec_dykC (by assumption); omega)
        | (simp_arith; done)
        | exact dec_fireT (by assumption)
        | exact dec_dykT (by assumption)
        | (have h := dec_fireT (findFire_mem (by assumption)); omega)
        | (have h := dec_fireT (by assumption); omega)
        | (have h := dec_dykT (by assumption); omega)
        | exact Nat.lt_of_lt_of_le (dec_fireT (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dykT (by assumption)) (by omega)
        | exact dec_dyk0 (by assumption)
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | exact dec_curry
        | exact dec_stripshift
        | exact dec_impor (wPos_pos _) (wPos_pos _)
        | exact dec_orctx (by assumption)
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
        | exact p3_strict (by first
            | omega
            | (have := wPos_pos P₁; have := wPos_pos P₂; omega)
            | (have := wNeg_pos M; have := wNeg_pos N; omega))
        | exact dec_qimp_g (by assumption)
        | exact dec_dyk1 (by assumption)
        | (have h1 := dec_dyk1 (by assumption); omega)
        | exact dec_dyk1_g (by assumption)
        | exact dec_dyk2 (by assumption)
        | exact dec_dyk2_g (by assumption)
        | exact dec_ainv (by assumption)
        | exact dec_ainv0 (by assumption)
        | exact dec_orA (by assumption)
        | exact Nat.lt_of_lt_of_le (dec_qimp_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk1 (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk1_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk2 (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_dyk2_g (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_ainv (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_orA (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_orctx (by assumption)) (by omega)
        | (have h1 := p3_pos (wNeg M); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
           omega)
        | (have h1 := dec_and (m := wNeg M) (n := wNeg N) (t := 0); omega)
        | (have h1 := dec_curry (m₁ := wNeg M₁) (m₂ := wNeg M₂) (n := wNeg N)
             (t := 0); omega)
        | (have h1 := dec_stripshift (x := wPos P') (n := wNeg N) (t := 0)
           omega)
        | (have h1 := dec_impor (a := wPos Q₁) (b := wPos Q₂) (n := wNeg N)
             (t := 0) (wPos_pos _) (wPos_pos _); omega)
        | (have h1 := p3_pos (1 + wNeg N + 1); omega)
        | (have h1 := p3_pos (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic))

set_option hygiene false in
/-- The decreasing farm of the A-side traversal (`aMinF`, `UEntry`, the `U*` family, `dykAntC`). One definition, nine uses. -/
macro "ljf_dec_a" : tactic => `(tactic| (
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
            (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        | exact Nat.lt_of_lt_of_le
            (Nat.lt_of_le_of_lt (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
              (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
            (Nat.le_add_right _ _)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h1 := dec_dykC (by assumption); omega)
        | (simp_arith; done)
        | exact dec_fireT (by assumption)
        | exact dec_dykT (by assumption)
        | (have h := dec_fireT (findFire_mem (by assumption)); omega)
        | (have h := dec_fireT (by assumption); omega)
        | (have h := dec_dykT (by assumption); omega)
        | (have h := dec_fireS (findFire_mem (by assumption)); omega)
        | (have h := dec_fireS (by assumption); omega)
        | (have h := dec_dykC (by assumption); omega)
        | exact dec_dyk0 (by assumption)
        | exact dec_park
        | exact dec_drop
        | exact dec_shift1
        | exact dec_and
        | exact dec_curry
        | exact dec_stripshift
        | exact dec_impor (wPos_pos _) (wPos_pos _)
        | exact dec_orctx (by assumption)
        | (have h1 := invertPos_lt (P := Pos.or _ _)
             (by intro a h; nomatch h) _ (by assumption)
           simp only [wPos] at h1; omega)
        | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
        | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
        | (have h1 := dec_dyk1 (by assumption); omega)
        | (have h1 := dec_ainv (by assumption); omega)
        | (have h1 := dec_ainvS (by assumption); omega)
        | (have h1 := dec_ainv0 (by assumption); omega)
        | (have h1 := dec_orA (by assumption); omega)
        | (have h1 := p3_pos (wNeg M); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega)
           omega)
        | (have h1 := dec_and (m := wNeg M) (n := wNeg N) (t := 0); omega)
        | (have h1 := dec_curry (m₁ := wNeg M₁) (m₂ := wNeg M₂) (n := wNeg N)
             (t := 0); omega)
        | (have h1 := dec_stripshift (x := wPos P') (n := wNeg N) (t := 0)
           omega)
        | (have h1 := dec_impor (a := wPos Q₁) (b := wPos Q₂) (n := wNeg N)
             (t := 0) (wPos_pos _) (wPos_pos _); omega)
        | (have h1 := p3_pos (1 + wNeg N + 1); omega)
        | (have h1 := p3_pos (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1); omega)
        | (have h1 := p3_succ (wNeg M); have h2 := p3_pos (wNeg M); omega)
        | (have h1 := p3_pos (wPos P₀); omega)
        | (have h1 := p3_strict (a := wPos P₁) (b := wPos P₁ + wPos P₂ + 1)
             (by have := wPos_pos P₂; omega); omega)
        | (have h1 := p3_strict (a := wPos P₂) (b := wPos P₁ + wPos P₂ + 1)
             (by have := wPos_pos P₁; omega); omega)
        | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + wNeg N + 3)
             (by omega); omega)
        | (have h1 := p3_strict (a := wNeg N) (b := wNeg M + wNeg N + 3)
             (by omega); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic))


set_option maxHeartbeats 2000000 in
mutual

def eSound (p : String) : ∀ (todo done : List Neg),
    Inv (todo ++ done) [] (interp p todo done none)
  | .up (.atom a) :: todo, done => by
      rw [interp]
      exact (eSound p todo (.up (.atom a) :: done)).wk subPark
  | .up .fls :: todo, done => by
      rw [interp]
      exact .stable (.lfoc (List.mem_cons_self ..) (.rel .flsL))
  | .up (.or P Q) :: todo, done => by
      rw [interp]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      refine nOrAllIntro
        (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩)) ?_
      exact (eSound p (b ++ todo) done).wk subBranch1
  | .up (.down M) :: todo, done => by
      rw [interp]
      refine upMerge _ (List.mem_cons_self ..) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (eSound p (M :: todo) done).wk (Sub.cons M (Sub.grow _))
  | .and M N :: todo, done => by
      rw [interp]
      exact simHyp
        (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
              (.and1 lf))
          (Sub.cons N (Sub.grow _))
          (eSound p (M :: N :: todo) done))
  | .imp .fls N :: todo, done => by
      rw [interp]
      exact (eSound p todo done).wk (Sub.grow _)
  | .imp (.atom a) N :: todo, done => by
      rw [interp]
      exact (eSound p todo (.imp (.atom a) N :: done)).wk subPark
  | .imp (.or Q₁ Q₂) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..)) (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.grow _))
          (eSound p (.imp Q₁ N :: .imp Q₂ N :: todo) done))
  | .imp (.down (.up P')) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_self ..))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.grow _)
        (eSound p (.imp P' N :: todo) done)
  | .imp (.down (.and M₁ M₂)) N :: todo, done => by
      rw [interp]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStab (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStab (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_self ..))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.grow _)
        (eSound p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done)
  | .imp (.down (.imp Q' N')) N :: todo, done => by
      rw [interp]
      exact (eSound p todo (.imp (.down (.imp Q' N')) N :: done)).wk subPark
  | [], done => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          simp only [hf]
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (splits_mem (findFire_mem hf)))
                (.impL (.rfoc (.init (hs _ (atomMem_mem (findFire_atom hf)))))
                  lf))
            (splits_sub (findFire_mem hf))
            (eSound p [N] rest)
      | none =>
          simp only [hf]
          refine nAndAllIntro ?_
          intro x hx
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
          subst hEq
          cases X with
          | up P0 =>
              cases P0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    exact .stable (.rfoc (.init (splits_mem hXr)))
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down _ => exact nTopIntro
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]; exact nTopIntro
                  · simp only [pGuard, if_neg hap]
                    refine .impR (.atomL ?_)
                    exact simHyp
                      (fl := fun hs lf =>
                        .lfoc (hs _ (List.mem_cons_of_mem _ (splits_mem hXr)))
                          (.impL (.rfoc (.init (hs _ (List.mem_cons_self ..))))
                            lf))
                      (fun Z hZ =>
                        List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                      (eSound p [N] rest)
              | fls => exact nTopIntro
              | or _ _ => exact nTopIntro
              | down M0 =>
                  cases M0 with
                  | up _ => exact nTopIntro
                  | and _ _ => exact nTopIntro
                  | imp Q' N' =>
                      refine .andR (.impR (.downL ?_))
                        (simHyp (fl := resSim (splits_mem hXr))
                          (splits_sub hXr)
                          (eSound p [.imp (.down N') N] rest))
                      have hXd : Neg.imp (.down (.imp Q' N')) N ∈
                          (interp p [.imp (.down N') N] rest
                            (some (.imp Q' N')) :: ([] ++ done)) :=
                        List.mem_cons_of_mem _ (splits_mem hXr)
                      have dM' : Inv (interp p [.imp (.down N') N] rest
                          (some (.imp Q' N')) :: ([] ++ done)) []
                          (.imp Q' N') :=
                        simHyp (fl := resSim hXd) (Sub.refl _)
                          ((aSound p [.imp (.down N') N] rest
                              (.imp Q' N')).wk (by
                            intro Z hZ
                            rcases List.mem_cons.mp hZ with rfl | hZ
                            · exact List.mem_cons_of_mem _
                                (List.mem_cons_self ..)
                            · rcases List.mem_cons.mp hZ with rfl | hZ
                              · exact List.mem_cons_self ..
                              · exact List.mem_cons_of_mem _
                                  (List.mem_cons_of_mem _
                                    (splits_sub hXr Z hZ))))
                      exact simHyp
                        (fl := fun hs lf =>
                          .lfoc (hs _ hXd)
                            (.impL (.rfoc (.rel (dM'.wk hs))) lf))
                        (fun Z hZ =>
                          List.mem_cons_of_mem _ (splits_sub hXr Z hZ))
                        (eSound p [N] rest)
          | and _ _ => exact nTopIntro

  termination_by todo done => 2 * sum3 todo + sum3 done
  decreasing_by ljf_dec_sound

def aSound (p : String) : ∀ (todo done : List Neg) (G : Neg),
    Inv (interp p todo done (some G) :: (todo ++ done)) [] G
  | .up (.atom a) :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.up (.atom a) :: done) G).wk (Sub.cons _ subPark)
  | .up .fls :: todo, done, G => by
      rw [interp]
      exact upMerge G (R := .fls)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        (fun _ hb => by simp [invertPos] at hb)
  | .up (.or P Q) :: todo, done, G => by
      rw [interp]
      refine upMerge G (R := .or P Q)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
            (lfocAndAll (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
              (.impL
                (.rfoc (.rel ((eSound p (b ++ todo) done).wk (fun Z hZ =>
                  hs _ (subBranch2 Z (by
                    rcases List.mem_append.mp hZ with hZ | hZ
                    · exact List.mem_append_left _ hZ
                    · exact List.mem_append_right _ hZ))))))
                lf)))
        (subBranch2)
        (aSound p (b ++ todo) done G)
  | .up (.down M) :: todo, done, G => by
      rw [interp]
      refine upMerge G (R := .down M)
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
      intro b hb
      simp only [invertPos, List.mem_singleton] at hb
      subst hb
      exact (aSound p (M :: todo) done G).wk (by
        intro Z hZ
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ hZ)))
  | .and M N :: todo, done, G => by
      rw [interp]
      exact simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
            (.and2 lf))
        (Sub.refl _)
        (simHyp
          (fl := fun hs lf =>
            .lfoc (hs _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) (.and1 lf))
          (Sub.cons N (Sub.cons _ (Sub.grow _)))
          ((aSound p (M :: N :: todo) done G).wk (by
            intro Z hZ
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..))
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ hZ)))))
  | .imp .fls N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo done G).wk (Sub.cons _ (Sub.grow _))
  | .imp (.atom a) N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.imp (.atom a) N :: done) G).wk (Sub.cons _ subPark)
  | .imp (.or Q₁ Q₂) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp Q₂ N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (stabOr2 s) lf1))
        (Sub.refl _)
        (simHyp (H := .imp Q₁ N)
          (fl := fun hs lf => match lf with
            | .impL s lf1 =>
                .lfoc (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
                  (.impL (stabOr1 s) lf1))
          (Sub.cons _ (Sub.cons _ (Sub.grow _)))
          ((aSound p (.imp Q₁ N :: .imp Q₂ N :: todo) done G).wk (by
            intro Z hZ
            rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_self ..))
            · rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · rcases List.mem_cons.mp hZ with rfl | hZ
                · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
                · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ hZ)))))
  | .imp (.down (.up P')) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp P' N)
        (fl := fun hs lf => match lf with
          | .impL s lf1 =>
              .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
                (.impL (.rfoc (.rel (.stable s))) lf1))
        (Sub.refl _)
        ((aSound p (.imp P' N :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, G => by
      rw [interp]
      exact simHyp (H := .imp (.down M₁) (.imp (.down M₂) N))
        (fl := fun {Δa} {_} hs lf => match lf with
          | LFoc.impL s₁ (LFoc.impL s₂ lf2) =>
              routeStab (Δ₀ := Δa)
                (k := fun {Δb} hsb r₁ =>
                  routeStab (Δ₀ := Δb)
                    (k := fun {Δc} hsc r₂ =>
                      .lfoc (hsc _ (hsb _ (hs _ (List.mem_cons_of_mem _
                          (List.mem_cons_self ..)))))
                        (.impL
                          (.rfoc (.rel (.andR ((relOf r₁).wk hsc) (relOf r₂))))
                          (lf2.wk (fun Z hZ => hsc _ (hsb _ hZ)))))
                    (Sub.refl _) (s₂.wk hsb))
                (Sub.refl _) s₁)
        (Sub.refl _)
        ((aSound p (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done G).wk (by
          intro Z hZ
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ hZ))))
  | .imp (.down (.imp Q' N')) N :: todo, done, G => by
      rw [interp]
      exact (aSound p todo (.imp (.down (.imp Q' N')) N :: done) G).wk
        (Sub.cons _ subPark)
  | [], done, .imp Q N => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.imp Q N))
      | none =>
          simp only [hf]
          refine .impR (invBranches Q ?_)
          intro b hb
          exact simHyp
            (fl := fun hs lf =>
              .lfoc (hs _ (List.mem_append_right _ (List.mem_cons_self ..)))
                (lfocAndAll
                  (List.mem_map_of_mem (List.mem_attach _ ⟨b, hb⟩))
                  (.impL
                    (.rfoc (.rel ((eSound p b done).wk (fun Z hZ => hs _ (by
                      rcases List.mem_append.mp hZ with hZ | hZ
                      · exact List.mem_append_left _ hZ
                      · exact List.mem_append_right _
                          (List.mem_cons_of_mem _ hZ))))))
                    lf)))
            (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact List.mem_append_left _ hZ
              · exact List.mem_append_right _ (List.mem_cons_of_mem _
                  (List.mem_append_right _ hZ)))
            (aSound p b done N)
  | [], done, .and M N => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.and M N))
      | none =>
          simp only [hf]
          refine .andR ?_ ?_
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and1 lf))
              (Sub.grow _)
              (aSound p [] done M)
          · exact simHyp
              (fl := fun hs lf =>
                .lfoc (hs _ (List.mem_cons_self ..)) (.and2 lf))
              (Sub.grow _)
              (aSound p [] done N)
  | [], done, .up (.atom q) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.atom q)))
      | none =>
          simp only [hf]
          by_cases hq : atomMem q done = true
          · simp only [hq, if_true]
            exact .stable (.rfoc (.init (List.mem_cons_of_mem _
              (atomMem_mem hq))))
          · simp only [hq, if_false]
            refine nOrAllElim _ (List.mem_cons_self ..) ?_
            intro x hx Γ' hsub
            if hx1 : x ∈ atomHead p q then
              by_cases hqp : q = p
              · simp [atomHead, hqp] at hx1
              · simp only [atomHead, if_neg hqp, List.mem_singleton] at hx1
                subst hx1
                exact .stable (.rfoc (.init (List.mem_cons_self ..)))
            else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.atom q)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.atom q)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up .fls => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up .fls))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ ([] : List Neg) then
            exact absurd hx1 (List.not_mem_nil)
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up .fls))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up .fls))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up (.or P₁ P₂) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.or P₁ P₂)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some (.up P₁)),
              interp p [] done (some (.up P₂))] then
            if e1 : x = interp p [] done (some (.up P₁)) then
              subst e1
              exact .stable (stabOr1 (unStable ((aSound p [] done
                (.up P₁)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
            else
              have e2 : x = interp p [] done (some (.up P₂)) := by
                rcases List.mem_cons.mp hx1 with h | h
                · exact absurd h e1
                · exact List.mem_singleton.mp h
              subst e2
              exact .stable (stabOr2 (unStable ((aSound p [] done
                (.up P₂)).wk (by
                  intro Z hZ
                  rcases List.mem_cons.mp hZ with rfl | hZ
                  · exact List.mem_cons_self ..
                  · exact List.mem_cons_of_mem _
                      (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.or P₁ P₂)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.or P₁ P₂)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
  | [], done, .up (.down M) => by
      rw [interp]
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          simp only [hf]
          exact fireASound hf (aSound p [N'] rest (.up (.down M)))
      | none =>
          simp only [hf]
          refine nOrAllElim _ (List.mem_cons_self ..) ?_
          intro x hx Γ' hsub
          if hx1 : x ∈ [interp p [] done (some M)] then
            rcases List.mem_singleton.mp hx1 with rfl
            exact .stable (.rfoc (.rel ((aSound p [] done M).wk (by
              intro Z hZ
              rcases List.mem_cons.mp hZ with rfl | hZ
              · exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem _
                  (hsub _ (List.mem_cons_of_mem _ hZ))))))
          else
          have hx2 : x ∈ (splits done).attach.map _ :=
            (List.mem_append.mp hx).resolve_left hx1
          obtain ⟨⟨⟨X, rest⟩, hXr⟩, hmem, hEq⟩ := memMapWitness _ _ x hx2
          subst hEq
          cases X with
          | up P0 => cases P0 <;> exact nBotElim _ (List.mem_cons_self ..)
          | imp Q0 N =>
              cases Q0 with
              | atom a =>
                  by_cases hap : a = p
                  · simp only [pGuard, if_pos hap]
                    exact nBotElim _ (List.mem_cons_self ..)
                  · simp only [pGuard, if_neg hap]
                    exact atkQimp (List.mem_cons_self ..)
                      (List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                      (fun Z hZ => List.mem_cons_of_mem _
                        (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                      (aSound p [N] rest (.up (.down M)))
              | fls => exact nBotElim _ (List.mem_cons_self ..)
              | or _ _ => exact nBotElim _ (List.mem_cons_self ..)
              | down M0 =>
                  cases M0 with
                  | up _ => exact nBotElim _ (List.mem_cons_self ..)
                  | and _ _ => exact nBotElim _ (List.mem_cons_self ..)
                  | imp Q' N' =>
                      exact atkDyk (List.mem_cons_self ..)
                        (List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_mem hXr))))
                        (fun Z hZ => List.mem_cons_of_mem _
                          (hsub _ (List.mem_cons_of_mem _ (splits_sub hXr Z hZ))))
                        (aSound p [.imp (.down N') N] rest (.imp Q' N'))
                        (aSound p [N] rest (.up (.down M)))
          | and _ _ => exact nBotElim _ (List.mem_cons_self ..)

  termination_by todo done G => 2 * sum3 todo + sum3 done + 3 ^ wNeg G
  decreasing_by ljf_dec_sound

end



end LJF

namespace LJF

/-! # Part 5: the inverse transformations and the saturated-case statements

Each processing clause of `interp` has an *inverse* transformation —
replacing uses of the consumed hypothesis by uses of its residual — proved
as a `simulate` instance.  The saturated case is *named* by the statements
`SatE2`/`SatA2` (and the Dyckhoff dispatch by `DykAnt`); Part 6's inner
induction discharges them unconditionally (`satE2`/`satA2`/`dykAnt` at the
end of the file).  The parametrised minimality functions `eMin`/`aMin`
that historically lived here are superseded by `eMinF`/`aMinF` and
preserved in `Archive/ljf-simp-round1-superseded.lean`.

## The inverse transformations -/

/-! Forced-shape analysers, top level so the index specialises. -/

/-- A left focus on a conjunction projects. -/
def lfocAnd {Δ : List Neg} {M N : Neg} {P : Pos} :
    LFoc Δ (.and M N) P → LFoc Δ M P ⊕ LFoc Δ N P
  | .and1 lf => .inl lf
  | .and2 lf => .inr lf

/-- A left focus on an implication is `impL`. -/
def lfocImp {Δ : List Neg} {Q : Pos} {N : Neg} {P : Pos} :
    LFoc Δ (.imp Q N) P → Stab Δ Q × LFoc Δ N P
  | .impL s lf => (s, lf)

/-- A left focus on a shift is `rel`. -/
def lfocUp {Δ : List Neg} {Q : Pos} {P : Pos} :
    LFoc Δ (.up Q) P → Inv Δ [Q] (.up P)
  | .rel d => d

/-- There is no right focus on `⊥`. -/
def rfocFls {Δ : List Neg} {A : Sort _} : RFocus Δ .fls → A := nofun

/-- A right focus on a disjunction picks a side. -/
def rfocOr {Δ : List Neg} {A B : Pos} :
    RFocus Δ (.or A B) → RFocus Δ A ⊕ RFocus Δ B
  | .or1 r => .inl r
  | .or2 r => .inr r

/-- Uses of `M ∧ N` become uses of `M` and `N`. -/
def invAndHyp {M N : Neg} {Γ : List Neg} {C : Neg}
    (d : Inv (.and M N :: Γ) [] C) : Inv (M :: N :: Γ) [] C :=
  simHyp (H := .and M N)
    (fl := fun hs lf => match lfocAnd lf with
      | .inl lf' => .lfoc (hs _ (List.mem_cons_self ..)) lf'
      | .inr lf' =>
          .lfoc (hs _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) lf')
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `⊥ ⊃ N` are vacuous: the antecedent proof routes to nothing —
`RFocus _ ⊥` has no constructor. -/
def invImpFls {N : Neg} {Γ : List Neg} {C : Neg}
    (d : Inv (.imp .fls N :: Γ) [] C) : Inv Γ [] C :=
  simHyp (H := .imp .fls N)
    (fl := fun _ lf =>
      routeStab (k := fun _ r => rfocFls r) (Sub.refl _) (lfocImp lf).1)
    (Sub.refl _)
    d

/-- Uses of `(Q₁∨Q₂) ⊃ N` route through the split residuals. -/
def invImpOr {Q₁ Q₂ : Pos} {N : Neg} {Γ : List Neg} {C : Neg}
    (d : Inv (.imp (.or Q₁ Q₂) N :: Γ) [] C) :
    Inv (.imp Q₁ N :: .imp Q₂ N :: Γ) [] C :=
  simHyp (H := .imp (.or Q₁ Q₂) N)
    (fl := fun hs lf =>
      routeStab
        (k := fun hs' r => match rfocOr r with
          | .inl r₁ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
                (.impL (.rfoc r₁) ((lfocImp lf).2.wk hs'))
          | .inr r₂ =>
              .lfoc (hs' _ (hs _ (List.mem_cons_of_mem _
                  (List.mem_cons_self ..))))
                (.impL (.rfoc r₂) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ))
    d

/-- Uses of `↓↑P′ ⊃ N` strip the double shift. -/
def invStrip {P' : Pos} {N : Neg} {Γ : List Neg} {C : Neg}
    (d : Inv (.imp (.down (.up P')) N :: Γ) [] C) : Inv (.imp P' N :: Γ) [] C :=
  simHyp (H := .imp (.down (.up P')) N)
    (fl := fun hs lf =>
      routeStab
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (unStable (relOf r)) ((lfocImp lf).2.wk hs')))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of `↓(M₁∧M₂) ⊃ N` fire the curried residual twice. -/
def invCurry {M₁ M₂ N : Neg} {Γ : List Neg} {C : Neg}
    (d : Inv (.imp (.down (.and M₁ M₂)) N :: Γ) [] C) :
    Inv (.imp (.down M₁) (.imp (.down M₂) N) :: Γ) [] C :=
  simHyp (H := .imp (.down (.and M₁ M₂)) N)
    (fl := fun hs lf =>
      routeStab
        (k := fun hs' r =>
          .lfoc (hs' _ (hs _ (List.mem_cons_self ..)))
            (.impL (.rfoc (.rel (andROf1 (relOf r))))
              (.impL (.rfoc (.rel (andROf2 (relOf r))))
                ((lfocImp lf).2.wk hs'))))
        (Sub.refl _) (lfocImp lf).1)
    (fun Z hZ => List.mem_cons_of_mem _ hZ)
    d

/-- Uses of a shifted hypothesis restrict to any one branch of its
inversion — the derivation already contains that branch (`extract`). -/
def invUp {R : Pos} {Γ : List Neg} {C : Neg}
    (d : Inv (.up R :: Γ) [] C) (b : List Neg) (hb : b ∈ invertPos R) :
    Inv (b ++ Γ) [] C :=
  simHyp (H := .up R)
    (fl := fun {Δ'} {_} hs lf =>
      unStable ((extract [] (lfocUp lf) b hb).wk (fun Z hZ => by
        rcases List.mem_append.mp hZ with hZ | hZ
        · exact hs _ (List.mem_append_left _ hZ)
        · exact hZ)))
    (fun Z hZ => List.mem_append_right _ hZ)
    d

end LJF

namespace LJF

/-! ## Splitting a context member -/

theorem splits_mem_split {Γ : List Neg} :
    ∀ {X rest}, (X, rest) ∈ splits Γ → ∀ Z ∈ Γ, Z = X ∨ Z ∈ rest := by
  induction Γ with
  | nil => intro X rest h; simp [splits] at h
  | cons Y Γ ih =>
      intro X rest h Z hZ
      simp only [splits, List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨⟨W, rest'⟩, hW, hEq⟩
      · cases h
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inl rfl
        · exact .inr hZ
      · cases hEq
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact .inr (List.mem_cons_self ..)
        · rcases ih hW Z hZ with e | hZ
          · exact .inl e
          · exact .inr (List.mem_cons_of_mem _ hZ)

/-- Uses of a fired implication become uses of its conclusion. -/
def invFireHyp {a : String} {N : Neg} {done rest Δext : List Neg} {C : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done)
    (d : Inv (done ++ Δext) [] C) : Inv (N :: (rest ++ Δext)) [] C :=
  simInv (H := .imp (.atom a) N)
    (fl := fun hs lf => .lfoc (hs _ (List.mem_cons_self ..)) (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_append.mp hZ with hZ | hZ
      · rcases splits_mem_split h Z hZ with e | hZ
        · exact .inl e
        · exact .inr (List.mem_cons_of_mem _ (List.mem_append_left _ hZ))
      · exact .inr (List.mem_cons_of_mem _ (List.mem_append_right _ hZ)))
    (Sub.refl _) d

/-! ## Context shuffles for the minimality reductions -/

theorem subParkOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) ((t ++ X :: d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (subParkInv _ hZ)
  · exact List.mem_append_right _ hZ

theorem subHeadOut {X : Neg} {t d Δ : List Neg} :
    Sub (((X :: t) ++ d) ++ Δ) (X :: ((t ++ d) ++ Δ)) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · rcases List.mem_cons.mp hZ with rfl | hZ
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hZ)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ hZ)

theorem subChainIn {b t d Δ : List Neg} :
    Sub (b ++ ((t ++ d) ++ Δ)) (((b ++ t) ++ d) ++ Δ) := by
  intro Z hZ
  rcases List.mem_append.mp hZ with hZ | hZ
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ hZ))
  · rcases List.mem_append.mp hZ with hZ | hZ
    · rcases List.mem_append.mp hZ with hZ | hZ
      · exact List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ hZ))
      · exact List.mem_append_left _ (List.mem_append_right _ hZ)
    · exact List.mem_append_right _ hZ

/-! ## The two open obligations, and minimality modulo them -/

/-- The context is `p`-free. -/
def PFreeCtx (p : String) (Δ : List Neg) : Prop := ∀ N ∈ Δ, PFreeN p N

/-- Saturation: no parked implication can fire. -/
def Saturated (done : List Neg) : Prop :=
  findFire done (splits done) = none

/-- Every member appears in `splits`. -/
theorem splits_of_mem {Γ : List Neg} {X : Neg} (h : X ∈ Γ) :
    ∃ rest, (X, rest) ∈ splits Γ := by
  induction Γ with
  | nil => simp at h
  | cons Y Γ ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Γ, List.mem_cons_self ..⟩
      · obtain ⟨rest, hr⟩ := ih h
        exact ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The three shapes parking can produce.  `SatE2`/`SatA2` are FALSE without
this restriction (e.g. `done = [↑q ∧ ↑q]` is saturated but its `∃p`
interpolant is the default `⊤`, which does not prove `q`); the recursion
only ever reaches saturated contexts of these shapes, so the restriction
costs nothing. -/
inductive ParkedN : Neg → Prop
  | atom (a : String) : ParkedN (.up (.atom a))
  | qimp (a : String) (N : Neg) : ParkedN (.imp (.atom a) N)
  | dyk (Q' : Pos) (N' N : Neg) : ParkedN (.imp (.down (.imp Q' N')) N)

/-- Every member is a parked shape. -/
def ParkedCtx (done : List Neg) : Prop := ∀ X ∈ done, ParkedN X

theorem ParkedCtx.nil : ParkedCtx [] := fun _ h => absurd h (List.not_mem_nil)

theorem ParkedCtx.cons {X : Neg} {done : List Neg}
    (hX : ParkedN X) (h : ParkedCtx done) : ParkedCtx (X :: done) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hX
  · exact h Z hZ

theorem ParkedCtx.sub {done rest : List Neg}
    (hs : Sub rest done) (h : ParkedCtx done) : ParkedCtx rest :=
  fun Z hZ => h Z (hs Z hZ)

/-- What `findFire = none` says about each scanned pair. -/
theorem findFire_none_spec {full : List Neg} :
    ∀ {l : List (Neg × List Neg)}, findFire full l = none →
      ∀ {a N rest}, (Neg.imp (.atom a) N, rest) ∈ l →
        atomMem a full = false := by
  intro l
  induction l with
  | nil => intro _ a N rest h; simp at h
  | cons XR more ih =>
      intro hn a N rest h
      obtain ⟨X, R⟩ := XR
      rcases List.mem_cons.mp h with hEq | h
      · cases hEq
        simp only [findFire] at hn
        by_cases hM : atomMem a full
        · simp [hM] at hn
        · simpa using hM
      · refine ih ?_ h
        match X, hn with
        | .imp (.atom b) N', hn => ?_
        | .up P, hn => exact hn
        | .imp .fls N', hn => exact hn
        | .imp (.or Q₁ Q₂) N', hn => exact hn
        | .imp (.down M) N', hn => exact hn
        | .and M₁ M₂, hn => exact hn
        simp only [findFire] at hn
        by_cases hM : atomMem b full
        · simp [hM] at hn
        · simpa [hM] using hn

/-- At a saturated context, a parked implication's atom is absent.  In
particular a `p ⊃ N` member excludes `↑p`. -/
theorem saturated_atom_absent {done : List Neg} (hsat : Saturated done)
    {a : String} {N : Neg} (h : Neg.imp (.atom a) N ∈ done) :
    atomMem a done = false := by
  obtain ⟨rest, hr⟩ := splits_of_mem h
  exact findFire_none_spec hsat hr

/-- `atomMem` is complete for membership. -/
theorem atomMem_of_mem {a : String} {Γ : List Neg}
    (h : Neg.up (.atom a) ∈ Γ) : atomMem a Γ = true := by
  simp only [atomMem, List.any_eq_true]
  exact ⟨_, h, by simp⟩

/-- Minimality of `∃p` at a saturated context — the inner induction over
derivations at saturated sequents, the heart of Pitts' argument.
Discharged unconditionally by `satE2` at the end of the file. -/
def SatE2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (ψ : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    Inv (done ++ Δ) [] ψ → Inv (interp p [] done none :: Δ) [] ψ

/-- Minimality of `∀p` at a saturated context.  Discharged unconditionally
by `satA2` at the end of the file. -/
def SatA2 (p : String) : Type :=
  ∀ (done Δ : List Neg) (G : Neg), Saturated done → ParkedCtx done →
    PFreeCtx p Δ →
    Inv (done ++ Δ) [] G →
    Inv (interp p [] done none :: Δ) [] (interp p [] done (some G))


end LJF

namespace LJF

/-! # Part 6: the saturated case — the inner induction

The plan, fixed by the analysis of 2026-08-09:

* One traversal over the four judgments, structural in the derivation, at a
  fixed saturated parked station `done`, with the context split as
  `done`-part plus a `p`-free kept part `K`.
* Uses of `done`-members are dispatched through the matching conjunct of the
  interpolant; the continuation after a fire is packaged as a derivation
  over the fired context (`d_cont`), cleaned of residual uses of the fired
  member, and handed to the minimality function at strictly smaller measure.
* Proofs of the atom `p` at the main line are eliminated by **composition**:
  `init` on `↑p` is impossible (saturation excludes `↑p` beside `p ⊃ M`;
  the kept side is `p`-free), so every such proof bottoms out in a fire
  whose body releases the `p`-material — and at that node all pieces exist
  to compose the outer `p ⊃ M` use with the inner fire directly.
* The single dispatch that does not close by these means is the Dyckhoff
  antecedent — deriving `∀p` of the antecedent at the residual station from
  a main-line stable proof of it.  It is isolated as `DykAnt`, one
  statement serving both modes.

## Preliminaries -/

/-- `p`-freeness for a pending list. -/
def PFreeΩ (p : String) (Ω : List Pos) : Prop := ∀ Q ∈ Ω, PFreeP p Q

theorem PFreeΩ.nil {p : String} : PFreeΩ p [] := fun _ h => absurd h (List.not_mem_nil)

theorem PFreeΩ.cons {p : String} {Q : Pos} {Ω : List Pos}
    (hQ : PFreeP p Q) (h : PFreeΩ p Ω) : PFreeΩ p (Q :: Ω) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hQ
  · exact h Z hZ

theorem PFreeΩ.head {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeP p Q := h Q (List.mem_cons_self ..)

theorem PFreeΩ.tail {p : String} {Q : Pos} {Ω : List Pos}
    (h : PFreeΩ p (Q :: Ω)) : PFreeΩ p Ω :=
  fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)

/-- Locate a member's split, constructively. -/
def splitAt : (Γ : List Neg) → (X : Neg) → X ∈ Γ → {rest // (X, rest) ∈ splits Γ}
  | Y :: Γ, X, h =>
      if e : X = Y then
        ⟨Γ, by cases e; exact List.mem_cons_self ..⟩
      else
        have h' : X ∈ Γ := by
          rcases List.mem_cons.mp h with rfl | h'
          · exact absurd rfl e
          · exact h'
        let ⟨rest, hr⟩ := splitAt Γ X h'
        ⟨Y :: rest, List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun zr => (zr.1, Y :: zr.2)) hr)⟩

/-- The `∃p` conjunct of a `q`-implication member, and its membership in the
interpolant's conjunction list. -/
theorem qimpConjMem {p : String} {done : List Neg} {a : String} {N : Neg}
    {rest : List Neg} (hXr : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- Likewise for a surviving atom. -/
theorem atomConjMem {p : String} {done : List Neg} {a : String}
    {rest : List Neg} (hXr : (Neg.up (.atom a), rest) ∈ splits done) :
    pGuard p a nTop (.up (.atom a)) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- And for a Dyckhoff member. -/
theorem dykConjMem {p : String} {done : List Neg} {Q' : Pos} {N' N : Neg}
    {rest : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done) :
    nAnd
      (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
           (interp p [N] rest none))
      (interp p [.imp (.down N') N] rest none) ∈
      ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | _ => nTop)) :=
  List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hXr⟩)

/-- **The isolated obligation** — the Dyckhoff antecedent dispatch: from a
main-line stable proof of the antecedent `↓(Q′ ⊃ N′)`, derive the `∀p`
interpolant of the antecedent at the residual station, on the interpolant
side.  One statement serves both modes.  This is Pitts' hardest case
(the `(A⊃B)⊃C` commute), and everything else below is proved outright. -/
def DykAnt (p : String) : Type :=
  ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) []
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))

end LJF

namespace LJF

/-! ## Part 6b: the dispatch helpers

Each is a plain `simulate`/assembly instance — no recursion into the coming
mutual block, so they compile standalone. -/

variable {p : String}

/-- **Fired-context cleanup.**  After a fire of `Q₀ ⊃ N`, residual uses of
the fired implication are redundant: the body `N` is now a hypothesis, so
`impL`-uses drop their antecedent and use `N` directly. -/
def fireClean {Q₀ : Pos} {N : Neg} {Γ' rest K : List Neg} {C : Neg}
    (hsplit : ∀ Z ∈ Γ', Z = Neg.imp Q₀ N ∨ Z ∈ rest ∨ Z ∈ K)
    (d : Inv (N :: Γ') [] C) : Inv ((N :: rest) ++ K) [] C :=
  simInv (H := .imp Q₀ N)
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_append_left _ (List.mem_cons_self ..)))
        (lfocImp lf).2)
    (fun Z hZ => by
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact .inr (List.mem_append_left _ (List.mem_cons_self ..))
      · rcases hsplit Z hZ with e | hZ | hZ
        · exact .inl e
        · exact .inr (List.mem_append_left _ (List.mem_cons_of_mem _ hZ))
        · exact .inr (List.mem_append_right _ hZ))
    (Sub.refl _) d

/-- The fire step, as one equation for every mode: when a parked `a ⊃ N'`
fires, the interpolant at the station equals the interpolant at the residual
station, whatever the goal.  Stated by cases because the equation lemmas of
the well-founded `interp` are specialised per fused matcher alternative, so
an abstract goal matches none of them — `rw [interp]` fails on
`interp p [] done (some G)` with `G` a variable. -/
theorem interpFire_eq {p : String} {done : List Neg} {a : String} {N' : Neg}
    {rest : List Neg}
    (hf : findFire done (splits done) = some (a, N', rest)) :
    ∀ g, interp p [] done g = interp p [N'] rest g := by
  intro g
  match g with
  | none | some (.up (.atom _)) | some (.up .fls) | some (.up (.or _ _))
  | some (.up (.down _)) | some (.imp _ _) | some (.and _ _) =>
      rw [interp]; split
      all_goals rename_i heq
      · rw [hf] at heq; cases heq; rfl
      · rw [hf] at heq; cases heq

/-- The saturated `∃p` aggregate, as an equation. -/
theorem interpE_eq {p : String} {done : List Neg} (hsat : Saturated done) :
    interp p [] done none = nAndAll ((splits done).attach.map
      (fun ⟨(X, rest), hXr⟩ =>
        match X with
        | .up (.atom a) => pGuard p a nTop (.up (.atom a))
        | .imp (.atom a) N =>
            pGuard p a nTop (.imp (.atom a) (interp p [N] rest none))
        | .imp (.down (.imp Q' N')) N =>
            nAnd
              (.imp (.down (interp p [.imp (.down N') N] rest
                             (some (.imp Q' N'))))
                   (interp p [N] rest none))
              (interp p [.imp (.down N') N] rest none)
        | _ => nTop)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

/-- Project a surviving atom from the interpolant. -/
def atomAssemble {done K : List Neg} {a : String} {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.up (.atom a)) ∈ L) (hap : ¬ a = p) :
    Stab (interp p [] done none :: K) (.atom a) :=
  .lfoc (List.mem_cons_self ..)
    (hE.symm ▸ lfocAndAll hmem (by
      simp only [pGuard]; rw [if_neg hap]
      exact LFoc.rel (idPos (.atom a) _)))


/-- The context split after locating a member: `done`-side members are the
member itself or in its complement. -/
theorem splitHyp {done K Γ' rest : List Neg} {X : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (hXr : (X, rest) ∈ splits done) :
    ∀ Z ∈ Γ', Z = X ∨ Z ∈ rest ∨ Z ∈ K := by
  intro Z hZ
  rcases hm Z hZ with hd | hK
  · rcases splits_mem_split hXr Z hd with e | hr
    · exact .inl e
    · exact .inr (.inl hr)
  · exact .inr (.inr hK)

end LJF

namespace LJF

/-! ## Part 6c: the inner induction, `∃p` side

The mutual block: `eMinF` (minimality, as before, but with the saturated
case discharged inline) and the traversal components.  Structural in the
derivation at a fixed station; every station-crossing goes through `eMinF`
at strictly smaller measure, so the lexicographic pair `(μ, size)` carries
the whole block. -/


theorem hmConsDone {done K Γ' : List Neg} {M : Neg} (hMd : M ∈ done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inl hMd
  · exact hm Z hZ

theorem hmConsK {done K Γ' : List Neg} {M : Neg}
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) :
    ∀ Z ∈ M :: Γ', Z ∈ done ∨ Z ∈ M :: K := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact .inr (List.mem_cons_self ..)
  · exact (hm Z hZ).imp id (List.mem_cons_of_mem _)

theorem PFreeCtx.cons {p : String} {K : List Neg} {M : Neg}
    (hM : PFreeN p M) (hK : PFreeCtx p K) : PFreeCtx p (M :: K) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hM
  · exact hK Z hZ

/-- The weight inequalities for the traversal's station crossings. -/
theorem dec_fireT {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := 1 + wNeg N + 1) (by omega)
  omega

theorem dec_dykT {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have := p3_2 (a := wNeg N) (c := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  omega



/-! ## Part 7: shift release and the Dyckhoff commute

`relStab`: CPS release of a stable proof of `↓M` — the continuation receives
an inversion of `M` at every point one is produced.  `negOfDownStab` closes
the loop into a plain derivation of `M`, by recursion on `M` (the mirror of
`upMerge`).  `dykCommute` then converts a mixed-context stable proof of the
Dyckhoff antecedent into a derivation over the residual station — uses of
the full hypothesis are manufactured from the residual, because under the
antecedent's own inversion the goal-branch is in context (Dyckhoff's
observation, in focused form). -/

mutual

/-- CPS release of a stable `↓M`-proof. -/
def relStab {Δ₀ : List Neg} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] M → Stab Δ' P₀) :
    ∀ {Δ : List Neg}, Sub Δ₀ Δ → Stab Δ (.down M) → Stab Δ P₀
  | _, hs, .rfoc r => k hs (relOf r)
  | _, hs, .lfoc h lf => .lfoc h (relLF k hs lf)

/-- Release below a left focus. -/
def relLF {Δ₀ : List Neg} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] M → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {H : Neg}, Sub Δ₀ Δ →
      LFoc Δ H (.down M) → LFoc Δ H P₀
  | _, _, hs, .rel d => .rel (relInv k hs d)
  | _, _, hs, .impL s lf => .impL s (relLF k hs lf)
  | _, _, hs, .and1 lf => .and1 (relLF k hs lf)
  | _, _, hs, .and2 lf => .and2 (relLF k hs lf)

/-- Release through inversion; the goal is a shift, so the traversal is
total. -/
def relInv {Δ₀ : List Neg} {M : Neg} {P₀ : Pos}
    (k : ∀ {Δ' : List Neg}, Sub Δ₀ Δ' → Inv Δ' [] M → Stab Δ' P₀) :
    ∀ {Δ : List Neg} {Ω : List Pos}, Sub Δ₀ Δ →
      Inv Δ Ω (.up (.down M)) → Inv Δ Ω (.up P₀)
  | _, _, hs, .stable s => .stable (relStab k hs s)
  | _, _, hs, .orL d₁ d₂ => .orL (relInv k hs d₁) (relInv k hs d₂)
  | _, _, _, .flsL => .flsL
  | _, _, hs, .downL d => .downL (relInv k (hs.trans (Sub.grow _)) d)
  | _, _, hs, .atomL d => .atomL (relInv k (hs.trans (Sub.grow _)) d)

end

/-- **A stable proof of `↓M` yields a derivation of `M`** — by recursion on
`M`, releasing at each stage. -/
def negOfDownStab : ∀ (M : Neg) {Δ : List Neg}, Stab Δ (.down M) → Inv Δ [] M
  | .up P, _, s =>
      .stable (relStab (fun _ d => unStable d) (Sub.refl _) s)
  | .imp Q N, _, s =>
      .impR (invBranches Q (fun c hc =>
        negOfDownStab N (relStab
          (fun {Δ'} hs d =>
            .rfoc (.rel ((extract [] (impROf d) c hc).wk (fun Z hZ => by
              rcases List.mem_append.mp hZ with hZ | hZ
              · exact hs _ (List.mem_append_left _ hZ)
              · exact hZ))))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right c hZ)))))
  | .and M₁ M₂, _, s =>
      .andR
        (negOfDownStab M₁ (relStab
          (fun _ d => .rfoc (.rel (andROf1 d))) (Sub.refl _) s))
        (negOfDownStab M₂ (relStab
          (fun _ d => .rfoc (.rel (andROf2 d))) (Sub.refl _) s))

/-- **The Dyckhoff commute.**  A mixed-context stable proof of the antecedent
`↓(Q′ ⊃ N′)` becomes a derivation of `Q′ ⊃ N′` over the residual station:
uses of the full hypothesis `X = ↓(Q′⊃N′) ⊃ N` are replaced by fires of the
residual `↓N′ ⊃ N`, whose antecedent is recovered because the branch of `Q′`
currently in context closes the released implication (`extract`). -/
def dykCommute {p : String} {Q' : Pos} {N' N : Neg}
    {done rest K Γ' : List Neg}
    (hXr : (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done)
    (hm : ∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K)
    (s : Stab Γ' (.down (.imp Q' N'))) :
    Inv ((Neg.imp (.down N') N :: rest) ++ K) [] (.imp Q' N') :=
  .impR (invBranches Q' (fun b hb =>
    negOfDownStab N'
      (routeStab
        (k := fun {Δ''} hs' r =>
          .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact hs' _ (List.mem_append_left _ hZ)
            · exact hZ))))
        (Sub.refl _)
        (simStab (H := Neg.imp (.down (.imp Q' N')) N)
          (fl := fun {Δ'} _ hs lf =>
            .lfoc
              (hs _ (List.mem_append_right b (List.mem_append_left _
                (List.mem_cons_self ..))))
              (.impL
                (routeStab
                  (k := fun {Δ''} hs' r =>
                    .rfoc (.rel ((extract [] (impROf (relOf r)) b hb).wk
                      (fun Z hZ => by
                        rcases List.mem_append.mp hZ with hZ | hZ
                        · exact hs' _ (hs _ (List.mem_append_left _ hZ))
                        · exact hZ))))
                  (Sub.refl _) (lfocImp lf).1)
                (lfocImp lf).2))
          (fun Z hZ => by
            rcases List.mem_append.mp hZ with hZ | hZ
            · exact .inr (List.mem_append_left _ hZ)
            · rcases hm Z hZ with hd | hk
              · rcases splits_mem_split hXr Z hd with e | hr
                · exact .inl e
                · exact .inr (List.mem_append_right b
                    (List.mem_append_left _ (List.mem_cons_of_mem _ hr)))
              · exact .inr (List.mem_append_right b
                  (List.mem_append_right _ hk)))
          (Sub.refl _)
          (s.wk (fun Z hZ => List.mem_append_right b hZ))))))



/-! ## Part 8: A-side prelude -/

/-- The positive under a list disjunction. -/
def orChain : List Neg → Pos
  | [] => .fls
  | x :: l => .or (.down x) (.down (nOrAll l))

theorem nOrAll_eq (L : List Neg) : nOrAll L = .up (orChain L) := by
  cases L <;> rfl

theorem p3_succ (m : Nat) : (3:Nat) ^ (m + 1) = 3 ^ m * 3 := Nat.pow_succ ..

/-- The station drop for the Dyckhoff pipeline, with generous slack. -/
theorem dec_dykC {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ (wNeg N' + 1 + wNeg N + 1) + sum3 rest +
      3 ^ (wPos Q' + wNeg N' + 1) + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N' + 1 + wNeg N + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wPos_pos Q'; omega)
  have h2 := p3_mono (a := wPos Q' + wNeg N' + 1)
    (b := wPos Q' + wNeg N' + 1 + wNeg N) (by have := wNeg_pos N; omega)
  have h3 : (3:Nat) ^ (wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1) =
      3 ^ (wPos Q' + wNeg N' + 1 + wNeg N) * 3 * 3 := by
    rw [show wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1 =
        wPos Q' + wNeg N' + 1 + wNeg N + 1 + 1 from by omega,
      p3_succ, p3_succ]
  have h5 := p3_mono (a := 1) (b := wPos Q' + wNeg N' + 1 + wNeg N)
    (by have := wPos_pos Q'; omega)
  omega

/-- The fire drop, with slack. -/
theorem dec_fireS {done rest : List Neg} {a : String} {N : Neg}
    (h : (Neg.imp (.atom a) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  rw [show 1 + wNeg N + 1 = wNeg N + 1 + 1 from by omega] at hs
  have h1 := p3_succ (wNeg N)
  have h2 := p3_succ (wNeg N + 1)
  have h3 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The Dyckhoff-fire drop, with slack. -/
theorem dec_dykS {done rest : List Neg} {Q' : Pos} {N' N : Neg}
    (h : (Neg.imp (Pos.down (Neg.imp Q' N')) N, rest) ∈ splits done) :
    2 * 3 ^ wNeg N + sum3 rest + 9 < sum3 done := by
  have hs := splits_sum h
  simp only [wNeg, wPos] at hs
  have h1 := p3_mono (a := wNeg N + 1 + 1)
    (b := wPos Q' + wNeg N' + 1 + 1 + wNeg N + 1)
    (by have := wPos_pos Q'; have := wNeg_pos N'; omega)
  have h2 := p3_succ (wNeg N)
  have h3 := p3_succ (wNeg N + 1)
  have h4 := p3_mono (a := 1) (b := wNeg N) (wNeg_pos N)
  omega

/-- The goal-inversion drop, with slack. -/
theorem dec_ainvS {Q : Pos} {b : List Neg} {N : Neg}
    (hb : b ∈ invertPos Q) :
    2 * sum3 b + 3 ^ wNeg N + 9 < 3 ^ (wPos Q + wNeg N + 1) := by
  have h1 := invertPos_le Q b hb
  have hD := p3_succ (wPos Q + wNeg N - 1)
  rw [show wPos Q + wNeg N - 1 + 1 = wPos Q + wNeg N from by
    have := wPos_pos Q; omega] at hD
  have hC := p3_succ (wPos Q + wNeg N)
  have hA := p3_mono (a := wPos Q) (b := wPos Q + wNeg N - 1)
    (by have := wNeg_pos N; omega)
  have hB := p3_mono (a := wNeg N) (b := wPos Q + wNeg N)
    (by have := wPos_pos Q; omega)
  have hDp := p3_mono (a := 1) (b := wPos Q + wNeg N - 1)
    (by have := wPos_pos Q; have := wNeg_pos N; omega)
  omega

variable {p : String}

/-- Fire the `q`-implication conjunct: the atom from `sa`, the recursively
interpolated body consumed through `δ`. -/
def qAssembleN {done rest K : List Neg} {a : String} {N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈ L)
    (hap : ¬ a = p)
    (sa : Stab (interp p [] done none :: K) (.atom a))
    (δ : Inv (interp p [N] rest none :: K) [] C) :
    Inv (interp p [] done none :: K) [] C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem (by
          simp only [pGuard]; rw [if_neg hap]
          exact LFoc.impL (sa.wk hs) lf)))
    (Sub.grow _) δ

/-- Fire the Dyckhoff conjunct: the antecedent interpolant from `sant`, the
recursively interpolated body consumed through `δ`. -/
def dykAssembleN {done rest K : List Neg} {Q' : Pos} {N' N : Neg} {C : Neg}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
             (interp p [N] rest none))
        (interp p [.imp (.down N') N] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) []
      (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
    (δ : Inv (interp p [N] rest none :: K) [] C) :
    Inv (interp p [] done none :: K) [] C :=
  simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ



/-! The `∀p` aggregates as equations, at each goal shape (stated outside any
mutual block so the elaborator reuses `interp`'s own compiled matchers). -/

theorem interpA_atom_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : ¬ atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) =
      nOrAll (atomHead p q ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.atom q)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.atom q))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_atomT_eq {p : String} {done : List Neg}
    (hsat : Saturated done) {q : String} (hq : atomMem q done = true) :
    interp p [] done (some (.up (.atom q))) = nTop := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · simp [hq]

theorem interpA_fls_eq {p : String} {done : List Neg}
    (hsat : Saturated done) :
    interp p [] done (some (.up .fls)) =
      nOrAll ((splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up .fls))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up .fls)))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_or_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (P₁ P₂ : Pos) :
    interp p [] done (some (.up (.or P₁ P₂))) =
      nOrAll ([interp p [] done (some (.up P₁)),
               interp p [] done (some (.up P₂))] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.or P₁ P₂)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.or P₁ P₂))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_down_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M : Neg) :
    interp p [] done (some (.up (.down M))) =
      nOrAll ([interp p [] done (some M)] ++ (splits done).attach.map (fun ⟨(X, rest), hXr⟩ =>
              match X, hXr with
              | .imp (.atom a) N, hXr =>
                  pGuard p a nBot
                    (nAnd (.up (.atom a)) (interp p [N] rest (some (.up (.down M)))))
              | .imp (.down (.imp Q' N')) N, hXr =>
                  nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
                       (interp p [N] rest (some (.up (.down M))))
              | _, _ => nBot)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_imp_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (Q : Pos) (N : Neg) :
    interp p [] done (some (.imp Q N)) =
      nAndAll ((invertPos Q).attach.map
        (fun ⟨b, hb⟩ =>
          .imp (.down (interp p b done none))
            (interp p b done (some N)))) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl

theorem interpA_and_eq {p : String} {done : List Neg}
    (hsat : Saturated done) (M N : Neg) :
    interp p [] done (some (.and M N)) =
      nAnd (interp p [] done (some M)) (interp p [] done (some N)) := by
  rw [interp]; split
  all_goals rename_i heq
  · rw [hsat] at heq; cases heq
  · rfl


variable {p : String}

set_option maxHeartbeats 8000000 in
mutual

/-- Minimality of `∃p`, with the saturated case discharged inline —
conditional only on the Dyckhoff antecedent dispatch `dyk`. -/
def eMinF : ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtx done →
    PFreeCtx p Δ → PFreeN p ψ →
    Inv ((todo ++ done) ++ Δ) [] ψ →
    Inv (interp p todo done none :: Δ) [] ψ
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ hψ
        (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _ => by
      rw [interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      refine nOrAllElim _ (List.mem_cons_self ..) ?_
      intro x hx Γ' hsub
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine ((eMinF (b ++ todo) done Δ ψ hP hΔ hψ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ ψ hP hΔ hψ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF (.imp P' N :: todo) done Δ ψ hP hΔ hψ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ ψ
        hP hΔ hψ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ hψ
        (d.wk subParkOut)
  | [], done, Δ, ψ, hP, hΔ, hψ, d => by
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          rw [interpFire_eq hf none]
          exact eMinF [N] rest Δ ψ
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact TInv done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ (fun _ h => absurd h (List.not_mem_nil)) hψ d
  termination_by todo done Δ ψ hP hΔ hψ d =>
    (2 * sum3 todo + sum3 done + 1, 0)
  decreasing_by ljf_dec_e


/-- Inversion-phase traversal. -/
def TInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {Ω : List Pos} {C : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeN p C →
      Inv Γ' Ω C → Inv (interp p [] done none :: K) Ω C
  | _, _, _, _, hm, hm2, hK, hΩ, hC, .impR d =>
      .impR (TInv done hsat hP hm hm2 hK (hΩ.cons hC.1) hC.2 d)
  | _, _, _, _, hm, hm2, hK, hΩ, hC, .andR d e =>
      .andR (TInv done hsat hP hm hm2 hK hΩ hC.1 d)
            (TInv done hsat hP hm hm2 hK hΩ hC.2 e)
  | _, _, _, _, hm, hm2, hK, _, hC, .stable s =>
      .stable (TStab done hsat hP hm hm2 hK hC s)
  | _, _, .or P₁ Q₁ :: _, _, hm, hm2, hK, hΩ, hC, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1) hC d₁)
           (TInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2) hC d₂)
  | _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, .down M₀ :: _, _, hm, hm2, hK, hΩ, hC, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, .atom a :: _, _, hm, hm2, hK, hΩ, hC, .atomL d =>
      .atomL (((TInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hΩ.tail hC d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K Ω C hm hm2 hK hΩ hC d => (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Stable-phase traversal: the dispatch point. -/
def TStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      Stab Γ' P → Stab (interp p [] done none :: K) P
  | _, _, _, hm, hm2, hK, hp, .rfoc r => TRF done hsat hP hm hm2 hK hp r
  | _, _, _, hm, hm2, hK, hp, @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom a), _, hd, .rel (.atomL (.stable s')) =>
            TStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hp s'
        | .imp (.atom a) N, _, hd, .impL s_a lf' =>
            if hap : a = p then
              TpElim done hsat hP hm hm2 hK hp hap hap hd lf' s_a
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hap
                (TStab done hsat hP hm hm2 hK hap s_a)
                (eMinF [N] rest _ _ (hP.sub (splits_sub hXr)) hK hp
                  (fireClean (splitHyp hm hXr)
                    (.stable (.lfoc (List.mem_cons_self ..)
                      (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
              (eMinF [N] rest _ _ (hP.sub (splits_sub hXr)) hK hp
                (fireClean (splitHyp hm hXr)
                  (.stable (.lfoc (List.mem_cons_self ..)
                    (lf'.wk (Sub.grow _)))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hp lf)
  termination_by Γ' K P hm hm2 hK hp s => (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Right-focus traversal. -/
def TRF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P : Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P →
      RFocus Γ' P → Stab (interp p [] done none :: K) P
  | _, _, .atom a, hm, _, hK, hp, .init h => by
      by_cases hd : Neg.up (.atom a) ∈ done
      · exact
          let w := splitAt done _ hd
          atomAssemble (interpE_eq hsat) (atomConjMem w.2) hp
      · exact .rfoc (.init (List.mem_cons_of_mem _
          ((hm _ h).resolve_left hd)))
  | _, _, _, hm, hm2, hK, hp, .or1 r =>
      stabOr1 (TRF done hsat hP hm hm2 hK hp.1 r)
  | _, _, _, hm, hm2, hK, hp, .or2 r =>
      stabOr2 (TRF done hsat hP hm hm2 hK hp.2 r)
  | _, _, _, hm, hm2, hK, hp, .rel d =>
      .rfoc (.rel (TInv done hsat hP hm hm2 hK
        (fun _ h => absurd h (List.not_mem_nil)) hp d))
  termination_by Γ' K P hm hm2 hK hp r => (2 * sum3 [] + sum3 done, sizeOf r)
  decreasing_by ljf_dec_e


/-- Left-focus traversal on a kept hypothesis. -/
def TLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {H : Neg} {P : Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P →
      LFoc Γ' H P → LFoc (interp p [] done none :: K) H P
  | _, _, _, _, hm, hm2, hK, hH, hp, .rel d =>
      .rel (TInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil) hp d)
  | _, _, _, _, hm, hm2, hK, hH, hp, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  | _, _, _, _, hm, hm2, hK, hH, hp, .and1 lf =>
      .and1 (TLF done hsat hP hm hm2 hK hH.1 hp lf)
  | _, _, _, _, hm, hm2, hK, hH, hp, .and2 lf =>
      .and2 (TLF done hsat hP hm hm2 hK hH.2 hp lf)
  termination_by Γ' K H P hm hm2 hK hH hp lf => (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- The `p`-fire eliminator: a main-line proof of the atom `p`, plus the
outer `p ⊃ M` package, yields the target directly — `init` on `↑p` is
impossible, kept chains rebuild, nested `p`-fires shortcut to their own
premise, and every other fire composes the package with the fire's body. -/
def TpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M P₀ →
      Stab Γ' (.atom b) → Stab (interp p [] done none :: K) P₀
  | _, _, _, _, _, _, hm, _, hK, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, a, b, hm, hm2, hK, hpT, ha, hb, hXpkg, lfP, @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            TpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hpT ha hb
              hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) N_b, _, hd, .impL s_b lf_b =>
            if hcp : c = p then
              TpElim done hsat hP hm hm2 hK hpT ha hcp hXpkg lfP s_b
            else
              let ⟨rest, hXr⟩ := splitAt done _ hd
              unStable (qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                (TStab done hsat hP hm hm2 hK hcp s_b)
                (eMinF [N_b] rest _ _ (hP.sub (splits_sub hXr)) hK hpT
                  (fireClean (splitHyp hm hXr) (.stable
                    (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                      (.impL
                        ((hb.trans ha.symm) ▸
                          Stab.lfoc (List.mem_cons_self ..)
                            (lf_b.wk (Sub.grow _)))
                        (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d =>
            let ⟨rest, hXr⟩ := splitAt done _ hd
            unStable (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
              (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
              (eMinF [N_d] rest _ _ (hP.sub (splits_sub hXr)) hK hpT
                (fireClean (splitHyp hm hXr) (.stable
                  (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                    (.impL
                      ((hb.trans ha.symm) ▸
                        Stab.lfoc (List.mem_cons_self ..)
                          (lf_d.wk (Sub.grow _)))
                      (lfP.wk (Sub.grow _))))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        .lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
          (TpLF done hsat hP hm hm2 hK
            (hK _ ((hm _ h).resolve_left hd)) hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ a b hm hm2 hK hpT ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done, sizeOf s)
  decreasing_by ljf_dec_e


/-- Left focus on a kept hypothesis, inside a `p`-proof. -/
def TpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {H : Neg} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeN p H → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M P₀ →
      LFoc Γ' H (.atom b) → LFoc (interp p [] done none :: K) H P₀
  | _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .rel d =>
      .rel (TpInv done hsat hP hm hm2 hK
        (PFreeΩ.cons hH PFreeΩ.nil)
        hpT ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and1 lf =>
      .and1 (TpLF done hsat hP hm hm2 hK hH.1 hpT ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, hm, hm2, hK, hH, hpT, ha, hb, hXpkg, lfP, .and2 lf =>
      .and2 (TpLF done hsat hP hm hm2 hK hH.2 hpT ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ H a b hm hm2 hK hH hpT ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done, sizeOf lf)
  decreasing_by ljf_dec_e


/-- Inversion inside a `p`-proof, with the goal re-targeted. -/
def TpInv (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {Ω : List Pos} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      PFreeΩ p Ω → PFreeP p P₀ → a = p → b = p →
      Neg.imp (.atom a) M ∈ done → LFoc Γ' M P₀ →
      Inv Γ' Ω (.up (.atom b)) → Inv (interp p [] done none :: K) Ω (.up P₀)
  | _, _, _, _, _, _, _, hm, hm2, hK, _, hpT, ha, hb, hXpkg, lfP, .stable s =>
      .stable (TpElim done hsat hP hm hm2 hK hpT ha hb hXpkg lfP s)
  | _, _, _, _, .or P₁ Q₁ :: _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .orL d₁ d₂ =>
      have hor : PFreeP p (.or P₁ Q₁) := hΩ.head
      .orL (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.1)
              hpT ha hb hXpkg lfP d₁)
           (TpInv done hsat hP hm hm2 hK (hΩ.tail.cons hor.2)
              hpT ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, .down M₀ :: _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .downL d =>
      have hM : PFreeN p M₀ := hΩ.head
      .downL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hM hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, .atom c :: _, _, _, hm, hm2, hK, hΩ, hpT, ha, hb, hXpkg, lfP, .atomL d =>
      .atomL (((TpInv done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK) hΩ.tail hpT ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk (fun Z hZ => by
        rcases List.mem_cons.mp hZ with rfl | hZ
        · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
        · rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ Ω a b hm hm2 hK hΩ hpT ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done, sizeOf d)
  decreasing_by ljf_dec_e


/-- Minimality of `∀p`, with the saturated case discharged inline. -/
def aMinF : ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtx done →
    PFreeCtx p Δ →
    Inv ((todo ++ done) ++ Δ) [] G →
    Inv (interp p todo done none :: Δ) [] (interp p todo done (some G))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF todo (.up (.atom a) :: done) Δ G
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, G, _, _, _ => by
      rw [interp, interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine .impR (.downL ?_)
      refine ((aMinF (b ++ todo) done Δ G hP hΔ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ G hP hΔ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF (.imp P' N :: todo) done Δ G hP hΔ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ G
        hP hΔ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMinF todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ
        (d.wk subParkOut)
  | [], done, Δ, G, hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          rw [interpFire_eq hf none, interpFire_eq hf (some G)]
          exact aMinF [N'] rest Δ G
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact UEntry done hf hP
            (fun Z hZ => List.mem_append.mp hZ)
            (fun Z hZ => List.mem_append_left _ hZ)
            hΔ G d
  termination_by todo done Δ G hP hΔ d =>
    (2 * sum3 todo + sum3 done + 3 ^ wNeg G + 4, 0)
  decreasing_by ljf_dec_a


/-- The `∀p` interpolant of any goal over a mixed saturated context. -/
def UEntry (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      ∀ (G : Neg), Inv Γ' [] G →
      Inv (interp p [] done none :: K) [] (interp p [] done (some G))
  | _, _, hm, hm2, hK, .imp Q N, .impR d₁ => by
      rw [interpA_imp_eq hsat Q N]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨w, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      have hb : w.1 ∈ invertPos Q := w.2
      refine .impR (.downL ?_)
      refine ((aMinF w.1 done _ N hP hK
        ((extract [] d₁ w.1 hb).wk (fun Z hZ => by
          rcases List.mem_append.mp hZ with hZ | hZ
          · exact List.mem_append_left _ (List.mem_append_left _ hZ)
          · rcases hm Z hZ with hd | hk
            · exact List.mem_append_left _ (List.mem_append_right _ hd)
            · exact List.mem_append_right _ hk))).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | _, _, hm, hm2, hK, .and M N, .andR d₁ d₂ => by
      rw [interpA_and_eq hsat M N]
      exact .andR (UEntry done hsat hP hm hm2 hK M d₁)
                  (UEntry done hsat hP hm hm2 hK N d₂)
  | _, _, hm, hm2, hK, .up (.atom q), .stable s => by
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · rw [interpA_atom_eq hsat hq]
        exact UStab done hsat hP hm hm2 hK (interpA_atom_eq hsat hq)
          (fun {c Nc rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          (fun {Q' N' N rest} hsp =>
            List.mem_append_right _
              (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
          s
  | _, _, hm, hm2, hK, .up .fls, .stable s => by
      rw [interpA_fls_eq hsat]
      exact UStab done hsat hP hm hm2 hK (interpA_fls_eq hsat)
        (fun {c Nc rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        (fun {Q' N' N rest} hsp =>
          List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩))
        s
  | _, _, hm, hm2, hK, .up (.or P₁ P₂), .stable s => by
      rw [interpA_or_eq hsat P₁ P₂]
      exact UStab done hsat hP hm hm2 hK (interpA_or_eq hsat P₁ P₂)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  | _, _, hm, hm2, hK, .up (.down M), .stable s => by
      rw [interpA_down_eq hsat M]
      exact UStab done hsat hP hm hm2 hK (interpA_down_eq hsat M)
        (fun {c Nc rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        (fun {Q' N' N rest} hsp =>
          List.mem_append_right _
            (List.mem_map_of_mem (List.mem_attach _ ⟨(_, _), hsp⟩)))
        s
  termination_by Γ' K hm hm2 hK G d =>
    (2 * sum3 [] + sum3 done + 3 ^ wNeg G + 3, 0)
  decreasing_by ljf_dec_a


/-- Stable-phase `∀p` traversal: attack emission. -/
def UStab (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {L : List Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      Stab Γ' P₀ → Inv (interp p [] done none :: K) [] (nOrAll L)
  | _, _, _, _, hm, hm2, hK, hV, qmem, dmem, .rfoc r =>
      hV ▸ URF done hsat hP hm hm2 hK r
  | _, _, _, _, hm, hm2, hK, hV, qmem, dmem, @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UStab done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hV qmem dmem s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf' =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem hcp hcp hd lf' s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact nOrAllIntro (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _)))))))
        | .imp (.down (.imp Q' N')) N, _, hd, .impL s_d lf' => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact nOrAllIntro (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr)
                      (.stable (.lfoc (List.mem_cons_self ..)
                        (lf'.wk (Sub.grow _))))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (nOrAll_eq _).symm ▸
          Inv.stable (.lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (ULF done hsat hP hm hm2 hK hV qmem dmem
              (hK _ ((hm _ h).resolve_left hd)) lf))
  termination_by Γ' K P₀ L hm hm2 hK hV qmem dmem s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by
    all_goals simp_wf
    all_goals try simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals
      first
        | exact Nat.lt_succ_self _
        | omega
        | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
        | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
        | (have h1 := dec_ainvS (N := N) (by assumption); omega)
        | (have h1 := dec_fireS (by assumption); omega)
        | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
        | (refine Prod.Lex.left _ _ ?_
           first
             | omega
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | exact Nat.lt_of_lt_of_le
                 (Nat.lt_of_le_of_lt
                   (Nat.add_le_add_left (show (5:Nat) ≤ 9 from by decide) _)
                   (dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr))
                 (Nat.le_trans (Nat.le_add_left _ _)
                   (Nat.le_trans (Nat.le_add_right _ _)
                     (Nat.le_add_right _ _)))
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykC (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N) hXr; omega)
             | (have h1 := dec_dykS (Q' := Q') (N' := N') (N := N_d) hXr
                omega)
             | (have h1 := dec_fireS (a := c) (N := Nc) hXr; omega)
             | (have h1 := dec_ainvS (N := N) (by assumption); omega)
             | (have h1 := dec_fireS (by assumption); omega)
             | (have h1 := dec_fireS (findFire_mem (by assumption)); omega)
             | (have h1 := dec_dykC (by assumption); omega))
        | decreasing_tactic


/-- Right-focus `∀p` traversal: the goal-driven disjuncts. -/
def URF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      RFocus Γ' P₀ →
      Inv (interp p [] done none :: K) [] (interp p [] done (some (.up P₀)))
  | _, _, .atom q, hm, hm2, hK, .init h => by
      by_cases hq : atomMem q done = true
      · rw [interpA_atomT_eq hsat hq]; exact nTopIntro
      · have hk : Neg.up (.atom q) ∈ _ :=
          (hm _ h).resolve_left (fun hd => hq (atomMem_of_mem hd))
        have hqp : ¬ q = p := fun e => (hK _ hk) e
        rw [interpA_atom_eq hsat hq]
        refine nOrAllIntro (List.mem_append_left _ ?_)
          (.stable (.rfoc (.init (List.mem_cons_of_mem _ hk))))
        rw [atomHead, if_neg hqp]
        exact List.mem_cons_self ..
  | _, _, .or P₁ P₂, hm, hm2, hK, .or1 r₁ => by
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (URF done hsat hP hm hm2 hK r₁)
  | _, _, .or P₁ P₂, hm, hm2, hK, .or2 r₂ => by
      rw [interpA_or_eq hsat P₁ P₂]
      exact nOrAllIntro (List.mem_append_left _
          (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
        (URF done hsat hP hm hm2 hK r₂)
  | _, _, .down M, hm, hm2, hK, .rel dI => by
      rw [interpA_down_eq hsat M]
      exact nOrAllIntro (List.mem_append_left _ (List.mem_cons_self ..))
        (UEntry done hsat hP hm hm2 hK M dI)
  termination_by Γ' K P₀ hm hm2 hK r =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf r)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, `∀p` mode. -/
def ULF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {L : List Neg} {H : Neg},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeN p H →
      LFoc Γ' H P₀ → LFoc (interp p [] done none :: K) H (orChain L)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .rel d =>
      .rel (UInvG done hsat hP hm hm2 hK hV qmem dmem
        (PFreeΩ.cons hH PFreeΩ.nil) d)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (ULF done hsat hP hm hm2 hK hV qmem dmem hH.2 lf)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .and1 lf =>
      .and1 (ULF done hsat hP hm hm2 hK hV qmem dmem hH.1 lf)
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, .and2 lf =>
      .and2 (ULF done hsat hP hm hm2 hK hV qmem dmem hH.2 lf)
  termination_by Γ' K P₀ L H hm hm2 hK hV qmem dmem hH lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion, `∀p` mode, goal re-targeted to the disjunction. -/
def UInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {P₀ : Pos} {L : List Neg} {Ω : List Pos},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeΩ p Ω →
      Inv Γ' Ω (.up P₀) →
      Inv (interp p [] done none :: K) Ω (.up (orChain L))
  | _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, _, .stable s =>
      nOrAll_eq _ ▸ UStab done hsat hP hm hm2 hK hV qmem dmem s
  | _, _, _, _, .or PA PB :: _, hm, hm2, hK, hV, qmem, dmem, hΩ, .orL d₁ d₂ =>
      .orL (UInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.1) d₁)
           (UInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.2) d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, .down M₀ :: _, hm, hm2, hK, hV, qmem, dmem, hΩ, .downL d =>
      .downL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, .atom a :: _, hm, hm2, hK, hV, qmem, dmem, hΩ, .atomL d =>
      .atomL (((UInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom a)) from hΩ.head) hK)
          hV qmem dmem hΩ.tail d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K P₀ L Ω hm hm2 hK hV qmem dmem hΩ d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The `p`-fire eliminator, `∀p` mode: same composition, attack emission. -/
def UpElim (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      a = p → b = p → Neg.imp (.atom a) M ∈ done → LFoc Γ' M P₀ →
      Stab Γ' (.atom b) →
      Inv (interp p [] done none :: K) [] (nOrAll L)
  | _, _, _, _, _, a, b, hm, _, hK, _, _, _, ha, hb, hXpkg, _, .rfoc (.init h) =>
      False.elim (by
        rcases hm _ h with hd | hk
        · have h1 := atomMem_of_mem hd
          have h2 := saturated_atom_absent hsat hXpkg
          rw [hb.trans ha.symm] at h1
          rw [h1] at h2; cases h2
        · exact (hK _ hk) hb)
  | _, _, _, _, _, a, b, hm, hm2, hK, hV, qmem, dmem, ha, hb, hXpkg, lfP,
      @Stab.lfoc _ _ N₀ h lf =>
      if hd : N₀ ∈ done then
        match N₀, hP _ hd, hd, lf with
        | .up (.atom c), _, hd, .rel (.atomL (.stable s')) =>
            UpElim done hsat hP (hmConsDone hd hm)
              (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ)) hK hV qmem dmem
              ha hb hXpkg (lfP.wk (Sub.grow _)) s'
        | .imp (.atom c) Nc, _, hd, .impL s_c lf_c =>
            if hcp : c = p then
              UpElim done hsat hP hm hm2 hK hV qmem dmem ha hcp hXpkg lfP s_c
            else by
              obtain ⟨rest, hXr⟩ := splitAt done _ hd
              exact nOrAllIntro (qmem hXr) (by
                simp only [pGuard]; rw [if_neg hcp]
                refine .andR
                  (.stable (TStab done hsat hP hm hm2 hK hcp s_c)) ?_
                exact qAssembleN (interpE_eq hsat) (qimpConjMem hXr) hcp
                  (TStab done hsat hP hm hm2 hK hcp s_c)
                  (aMinF [Nc] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_c.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _))))))))
        | .imp (.down (.imp Q' N')) N_d, _, hd, .impL s_d lf_d => by
            obtain ⟨rest, hXr⟩ := splitAt done _ hd
            exact nOrAllIntro (dmem hXr)
              (.andR
                (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                (dykAssembleN (interpE_eq hsat) (dykConjMem hXr)
                  (dykAntC done rest _ _ Q' N' N_d hsat hP hXr hm hm2 hK s_d)
                  (aMinF [N_d] rest _ (.up _)
                    (ParkedCtx.sub (splits_sub hXr) hP) hK
                    (fireClean (splitHyp hm hXr) (.stable
                      (.lfoc (List.mem_cons_of_mem _ (hm2 _ hXpkg))
                        (.impL
                          ((hb.trans ha.symm) ▸
                            Stab.lfoc (List.mem_cons_self ..)
                              (lf_d.wk (Sub.grow _)))
                          (lfP.wk (Sub.grow _)))))))))
        | .up .fls, hpk, _, _ => nomatch hpk
        | .up (.or _ _), hpk, _, _ => nomatch hpk
        | .up (.down _), hpk, _, _ => nomatch hpk
        | .imp .fls _, hpk, _, _ => nomatch hpk
        | .imp (.or _ _) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.up _)) _, hpk, _, _ => nomatch hpk
        | .imp (.down (.and _ _)) _, hpk, _, _ => nomatch hpk
        | .and _ _, hpk, _, _ => nomatch hpk
      else
        (nOrAll_eq _).symm ▸
          Inv.stable (.lfoc (List.mem_cons_of_mem _ ((hm _ h).resolve_left hd))
            (UpLF done hsat hP hm hm2 hK hV qmem dmem
              (hK _ ((hm _ h).resolve_left hd)) ha hb hXpkg lfP lf))
  termination_by Γ' K M P₀ L a b hm hm2 hK hV qmem dmem ha hb hXpkg lfP s =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf s)
  decreasing_by ljf_dec_a


/-- Left focus on a kept hypothesis, inside an `∀p`-mode `p`-proof. -/
def UpLF (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {H : Neg}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeN p H → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M P₀ →
      LFoc Γ' H (.atom b) → LFoc (interp p [] done none :: K) H (orChain L)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .rel d =>
      .rel (UpInvG done hsat hP hm hm2 hK hV qmem dmem
        (PFreeΩ.cons hH PFreeΩ.nil) ha hb hXpkg lfP d)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .impL s lf =>
      .impL (TStab done hsat hP hm hm2 hK hH.1 s)
            (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.2 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .and1 lf =>
      .and1 (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.1 ha hb hXpkg lfP lf)
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, hH, ha, hb, hXpkg,
      lfP, .and2 lf =>
      .and2 (UpLF done hsat hP hm hm2 hK hV qmem dmem hH.2 ha hb hXpkg lfP lf)
  termination_by Γ' K M P₀ L H a b hm hm2 hK hV qmem dmem hH ha hb hXpkg lfP lf =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf lf)
  decreasing_by ljf_dec_a


/-- Inversion inside an `∀p`-mode `p`-proof. -/
def UpInvG (done : List Neg) (hsat : Saturated done) (hP : ParkedCtx done) :
    ∀ {Γ' K : List Neg} {M : Neg} {P₀ : Pos} {L : List Neg} {Ω : List Pos}
      {a b : String},
      (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
      interp p [] done (some (.up P₀)) = nOrAll L →
      (∀ {c : String} {Nc : Neg} {rest : List Neg},
        (Neg.imp (.atom c) Nc, rest) ∈ splits done →
        pGuard p c nBot (nAnd (.up (.atom c))
          (interp p [Nc] rest (some (.up P₀)))) ∈ L) →
      (∀ {Q' : Pos} {N' N : Neg} {rest : List Neg},
        (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
        nAnd (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
             (interp p [N] rest (some (.up P₀))) ∈ L) →
      PFreeΩ p Ω → a = p → b = p → Neg.imp (.atom a) M ∈ done →
      LFoc Γ' M P₀ →
      Inv Γ' Ω (.up (.atom b)) →
      Inv (interp p [] done none :: K) Ω (.up (orChain L))
  | _, _, _, _, _, _, _, _, hm, hm2, hK, hV, qmem, dmem, _, ha, hb, hXpkg,
      lfP, .stable s =>
      nOrAll_eq _ ▸
        UpElim done hsat hP hm hm2 hK hV qmem dmem ha hb hXpkg lfP s
  | _, _, _, _, _, .or PA PB :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .orL d₁ d₂ =>
      .orL (UpInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.1) ha hb hXpkg lfP d₁)
           (UpInvG done hsat hP hm hm2 hK hV qmem dmem
              (hΩ.tail.cons hΩ.head.2) ha hb hXpkg lfP d₂)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, .flsL => .flsL
  | _, _, _, _, _, .down M₀ :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .downL d =>
      .downL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons hΩ.head hK) hV qmem dmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  | _, _, _, _, _, .atom c :: _, _, _, hm, hm2, hK, hV, qmem, dmem, hΩ, ha, hb, hXpkg,
      lfP, .atomL d =>
      .atomL (((UpInvG done hsat hP (hmConsK hm)
          (fun Z hZ => List.mem_cons_of_mem _ (hm2 Z hZ))
          (PFreeCtx.cons (show PFreeN p (.up (.atom c)) from hΩ.head) hK)
          hV qmem dmem hΩ.tail ha hb hXpkg
          (lfP.wk (Sub.grow _)) d)).wk
        (fun Z hZ => by
          rcases List.mem_cons.mp hZ with rfl | hZ
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · rcases List.mem_cons.mp hZ with rfl | hZ
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)))
  termination_by Γ' K M P₀ L Ω a b hm hm2 hK hV qmem dmem hΩ ha hb hXpkg lfP d =>
    (2 * sum3 [] + sum3 done + 3 ^ wPos P₀ + 2, sizeOf d)
  decreasing_by ljf_dec_a


/-- The Dyckhoff antecedent dispatch, discharged: commute, interpolate at
the residual station, project the E-res conjunct. -/
def dykAntC : ∀ (done rest K Γ' : List Neg) (Q' : Pos) (N' N : Neg),
    Saturated done → ParkedCtx done →
    (Neg.imp (.down (.imp Q' N')) N, rest) ∈ splits done →
    (∀ Z ∈ Γ', Z ∈ done ∨ Z ∈ K) → Sub done Γ' → PFreeCtx p K →
    Stab Γ' (.down (.imp Q' N')) →
    Inv (interp p [] done none :: K) []
        (interp p [.imp (.down N') N] rest (some (.imp Q' N')))
  | done, rest, K, Γ', Q', N', N, hsat, hP, hXr, hm, hm2, hK, s =>
      simHyp
        (fl := fun hs lf =>
          .lfoc (hs _ (List.mem_cons_self ..))
            ((interpE_eq hsat).symm ▸ lfocAndAll (dykConjMem hXr) (.and2 lf)))
        (Sub.grow _)
        (aMinF [.imp (.down N') N] rest K (.imp Q' N')
          (ParkedCtx.sub (splits_sub hXr) hP) hK
          (dykCommute (p := p) hXr hm s))
  termination_by done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    (2 * sum3 [Neg.imp (Pos.down N') N] + sum3 rest +
      3 ^ wNeg (Neg.imp Q' N') + 5, 0)
  decreasing_by ljf_dec_a


end

/-- **SatE2, unconditional.** -/
def satE2 : SatE2 p := fun done Δ ψ hsat hP hΔ hψ d =>
  TInv done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ
    (fun _ h => absurd h (List.not_mem_nil)) hψ d

/-- **SatA2, unconditional.** -/
def satA2 : SatA2 p := fun done Δ G hsat hP hΔ d =>
  UEntry done hsat hP (fun Z hZ => List.mem_append.mp hZ)
    (fun Z hZ => List.mem_append_left _ hZ) hΔ G d

/-- **The Dyckhoff antecedent dispatch, as originally isolated.** -/
def dykAnt : DykAnt p :=
  fun done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s =>
    dykAntC done rest K Γ' Q' N' N hsat hP hXr hm hm2 hK s

end LJF

/-! ### Axiom audit — measured and pinned on creation (2026-08-09). -/

/-- info: 'LJF.interp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.interp

/-- info: 'LJF.interp_pfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.interp_pfree

/-- info: 'LJF.eSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.eSound

/-- info: 'LJF.aSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.aSound

/-- info: 'LJF.satE2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.satE2

/-- info: 'LJF.satA2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.satA2

/-- info: 'LJF.dykAnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.dykAnt

/-- info: 'LJF.eMinF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.eMinF

/-- info: 'LJF.aMinF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LJF.aMinF
