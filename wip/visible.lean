import LaxLogic.PLLSequent
import LaxLogic.PLLLaxInfinite
import rnEmbed

/-!
# Visibility: join-prime elements of the closed lax fragment RN(◯,{})

For a Heyting algebra `H` the principal filter `↑a = {x | a ≤ x}` is a PRIME
filter exactly when `a` is JOIN-PRIME,

    a ≤ x ⊔ y  ⟹  a ≤ x  or  a ≤ y,

and the prime filters are the points of the Esakia dual.  In the Lindenbaum
algebra of the closed (variable-free) fragment of PLL, with `≤` given by
single-hypothesis derivability, this reads

    ∀ x y closed,  ⊢ a ⊃ (x ∨ y)  ⟹  ⊢ a ⊃ x  or  ⊢ a ⊃ y

— the DISJUNCTION PROPERTY RELATIVE TO `a`.  A proof of it, together with
`a ⊬ ⊥` (properness of `↑a`), is a proof that `a` names a point of the dual.
This file calls that predicate `Visible`.

## What is proved here

* `primeAll_top` / `visible_top` — the top element `⊤` is join-prime.  This is
  literally F&M Lemma 2.7(i), `PLLSequent.disjunction_property`: join-primality
  of `⊤` and the disjunction property ARE the same statement, and `↑⊤` is the
  least point of the dual, the root world forcing exactly the theorems.

* `harrop_sc` / `harrop_dp` — **the Harrop lemma for PLL**:

      every `φ ∈ Γ` Harrop  and  Γ ⊢ x ∨ y   ⟹   Γ ⊢ x  or  Γ ⊢ y

  proved by induction on the height of a cut-free `SCh` derivation
  (`PLLSequent.cutElimination` supplies the cut-free derivation, and the
  last-rule inspection follows `disjunction_property` as template).

* `primeAll_of_harrop` — a Harrop formula is join-prime; `PrimeAll.of_interd` —
  join-primality is invariant under interderivability, so it is a property of
  the Lindenbaum CLASS, and a Harrop REPRESENTATIVE suffices.

* Instantiation at the embedded Rieger–Nishimura ladder `t n := rnSub n`
  (`rnEmbed.lean`: `rn n` with `p := ◯⊥`):
  `visible_rnSub_one` (`t1 = ◯⊥`), `visible_rnSub_two` (`t2 = ¬◯⊥`),
  `visible_rnSub_four` (`t4 = (◯⊥ ∨ ¬◯⊥) ⊃ ◯⊥`), and — beyond the reach of
  Harrop applied to `t6` itself — `visible_rnSub_six`, via
  `rnSub_six_interd : t6 ≡ ¬¬◯⊥ ⊃ ◯⊥`, whose right-hand side IS Harrop.

* `not_joinPrime_rnSub_odd` — a REFUTATION: every odd rung `t (2k+3)` fails
  join-primality, since `t (2k+3) = t (2k+1) ∨ t (2k+2)` syntactically while
  neither disjunct is entailed (`rnSub_deriv_iff`).  So the odd rungs from `t3`
  on are proper joins, not points.

* `visible_gap_zero` / `harrop_gap_succ` — the gap family
  `g k = ◯ t (2k+1) ⊃ t (2k+1)`: `g 0` is visible but degenerate (`g 0 ⊣⊢ ⊤`),
  and from `k = 1` on the criterion does not apply.  Those gaps are OPEN.

* `joinPrime_of_exactRooted` — the semantic route, in general form: an EXACT
  ROOTED MODEL for `a` (a pointed model forcing `a` whose closed theory is
  exactly the closed consequences of `a`) makes `a` join-prime immediately, by
  locality of the Kripke `∨` clause.  `rnSub_even_prime_on_rungs` runs that
  route as far as the available exactness reaches: every EVEN rung is prime
  against RUNG-SHAPED disjunctions, because its ladder truth set is the
  principal upset `↑(k+1)`.  The obstruction to the full statement is recorded
  in the docstring of `rnSub_even_prime_on_rungs`.

## How `◯` is treated in the Harrop predicate

`Harrop (◯A) = true` for **arbitrary** `A` — not only for Harrop `A`.  This was
not assumed but read off the calculus.  The lax left rule of `PLLSequent.SCh` is

      Γ, A ⊢ ◯B
    -------------- ◯L        (principal `◯A ∈ Γ`, kept)
      Γ ⊢ ◯B

and it carries a SUCCEDENT RESTRICTION: its conclusion must be a `◯`-formula.
Along the whole induction of `harrop_sc` the succedent stays the disjunction
`x ∨ y`, so `◯L` is never applicable and a hypothesis `◯A` generates NO case at
all — `cases` on the derivation discards it by unification.  Hence `◯A` is inert
on the left for this argument whatever `A` is, and `◯(x ∨ y)` counts as Harrop
even though `x ∨ y` does not.  This is a point where PLL behaves BETTER than the
IPC analogy would suggest, and it is what makes `t1 = ◯⊥` and
`t4 = (◯⊥ ∨ ¬◯⊥) ⊃ ◯⊥` immediate.

The other clauses are the classical ones: `A ∧ B` Harrop when both are (`andL`
puts both components in the context), `C ⊃ B` Harrop when `B` is, with `C`
ARBITRARY (`impL` puts only `B` in the context of the minor premise, and the
major premise `Γ ⊢ C` is carried unexamined), and no disjunction is Harrop
(`orL` must be blocked outright).
-/

open PLLFormula

namespace PLLND
namespace Visibility

open SemUI RNEmbed
open LaxInfinite (atomFree)

/-! ## Join-primality and visibility -/

/-- **Join-primality, unrestricted**: `a ⊢ x ∨ y` implies `a ⊢ x` or `a ⊢ y`,
for arbitrary `x`, `y`. -/
def PrimeAll (a : PLLFormula) : Prop :=
  ∀ x y : PLLFormula, Deriv [a] (x.or y) → Deriv [a] x ∨ Deriv [a] y

/-- **Join-primality in the closed fragment**: the disjunction property
relative to `a`, over closed (atom-free) disjuncts.  This is exactly primeness
of the principal filter `↑a` in the Lindenbaum algebra RN(◯,{}). -/
def JoinPrime (a : PLLFormula) : Prop :=
  ∀ x y : PLLFormula, atomFree x = true → atomFree y = true →
    Deriv [a] (x.or y) → Deriv [a] x ∨ Deriv [a] y

theorem JoinPrime.of_primeAll {a : PLLFormula} (h : PrimeAll a) : JoinPrime a :=
  fun x y _ _ => h x y

/-- **`a` names a point of the Esakia dual of RN(◯,{})**: `a` is closed, the
principal filter `↑a` is proper (`a ⊬ ⊥`), and it is prime. -/
structure Visible (a : PLLFormula) : Prop where
  closed : atomFree a = true
  proper : ¬ Deriv [a] .falsePLL
  prime : JoinPrime a

/-- Join-primality is a property of the interderivability CLASS. -/
theorem PrimeAll.of_interd {a b : PLLFormula} (hab : Interd a b) (hb : PrimeAll b) :
    PrimeAll a := by
  intro x y h
  rcases hb x y (Deriv.cutHead hab.2 h) with h' | h'
  · exact .inl (Deriv.cutHead hab.1 h')
  · exact .inr (Deriv.cutHead hab.1 h')

/-! ## The top element: join-primality of `⊤` IS the disjunction property -/

theorem deriv_top : Deriv [] truePLL := ⟨.impIntro (.iden (.head _))⟩

/-- **`⊤` is join-prime.**  Restated: `⊢ x ∨ y` implies `⊢ x` or `⊢ y`, which is
F&M Lemma 2.7(i) (`disjunction_property`).  So `↑⊤`, the set of theorems, is a
point of the Esakia dual — the root world, forcing exactly the theorems. -/
theorem primeAll_top : PrimeAll truePLL := by
  intro x y h
  have h0 : Deriv [] (x.or y) := Deriv.cutHead deriv_top h
  have hw : ∀ {φ : PLLFormula}, Deriv [] φ → Deriv [truePLL] φ := by
    intro φ hd
    refine Deriv.rename ?_ hd
    intro χ hχ
    simp at hχ
  rcases disjunction_property h0 with h1 | h1
  · exact .inl (hw h1)
  · exact .inr (hw h1)

theorem proper_top : ¬ Deriv [truePLL] .falsePLL := by
  intro h
  exact LaxInfinite.not_entails_of_force (C := LaxInfinite.MC) (0 : Fin 7)
    (by decide) (by decide) h

theorem visible_top : Visible truePLL :=
  ⟨rfl, proper_top, JoinPrime.of_primeAll primeAll_top⟩

/-! ## The Harrop class and the Harrop lemma

`Harrop φ` says: no `∨` occurs in a strictly positive position of `φ`.  Atoms
and `⊥` are Harrop; `A ∧ B` is Harrop when both are; `C ⊃ B` is Harrop when `B`
is, with `C` ARBITRARY; and `◯A` is Harrop for `A` ARBITRARY — see the header
for why the calculus forces the last clause. -/

/-- The Harrop formulas of PLL. -/
def Harrop : PLLFormula → Bool
  | .prop _ => true
  | .falsePLL => true
  | .and A B => Harrop A && Harrop B
  | .or _ _ => false
  | .ifThen _ B => Harrop B
  | .somehow _ => true

/-- **The Harrop lemma, cut-free form.**  If every hypothesis is Harrop then a
cut-free derivation of a disjunction yields a derivation of a disjunct:

    (∀ φ ∈ Γ, Harrop φ)  →  SCh n Γ (x ∨ y)  →  SC Γ x  or  SC Γ y.

Induction on the height `n`.  The succedent stays `x ∨ y` throughout, so the
only rules that can end the derivation are `botL`, `andL`, `orL`, `impL`,
`orR1`, `orR2`; `orL` is impossible (no Harrop formula is a disjunction),
`andL`/`impL` reproduce the Harrop hypothesis on their minor premise, and
`orR1`/`orR2` deliver the disjunct.  `laxL` cannot fire at all: its conclusion
must be a `◯`-formula. -/
theorem harrop_sc : ∀ (n : Nat) {Γ : List PLLFormula} {x y : PLLFormula},
    (∀ φ ∈ Γ, Harrop φ = true) → SCh n Γ (x.or y) → SC Γ x ∨ SC Γ y := by
  intro n
  induction n with
  | zero =>
      intro Γ x y _ d
      cases d with
      | botL h => exact .inl (SC.botL h)
  | succ n ih =>
      intro Γ x y hΓ d
      cases d with
      | botL h => exact .inl (SC.botL h)
      | orR1 d' => exact .inl ⟨n, d'⟩
      | orR2 d' => exact .inr ⟨n, d'⟩
      | @orL _ _ A B _ h _ _ => exact absurd (hΓ _ h) (by simp [Harrop])
      | @andL _ _ A B _ h d' =>
          have hb := hΓ _ h
          simp only [Harrop, Bool.and_eq_true] at hb
          have hΓ' : ∀ φ ∈ A :: B :: Γ, Harrop φ = true := by
            intro φ hφ
            rcases List.mem_cons.mp hφ with rfl | hφ
            · exact hb.1
            · rcases List.mem_cons.mp hφ with rfl | hφ
              · exact hb.2
              · exact hΓ φ hφ
          rcases ih hΓ' d' with h' | h'
          · exact .inl (SC.andL h h')
          · exact .inr (SC.andL h h')
      | @impL _ _ A B _ h d₁ d₂ =>
          have hb := hΓ _ h
          simp only [Harrop] at hb
          have hΓ' : ∀ φ ∈ B :: Γ, Harrop φ = true := by
            intro φ hφ
            rcases List.mem_cons.mp hφ with rfl | hφ
            · exact hb
            · exact hΓ φ hφ
          rcases ih hΓ' d₂ with h' | h'
          · exact .inl (SC.impL h ⟨n, d₁⟩ h')
          · exact .inr (SC.impL h ⟨n, d₁⟩ h')

/-- **The Harrop lemma** (natural-deduction form):

    (∀ φ ∈ Γ, Harrop φ)  and  Γ ⊢ x ∨ y   ⟹   Γ ⊢ x  or  Γ ⊢ y. -/
theorem harrop_dp {Γ : List PLLFormula} {x y : PLLFormula}
    (hΓ : ∀ φ ∈ Γ, Harrop φ = true) (h : Deriv Γ (x.or y)) :
    Deriv Γ x ∨ Deriv Γ y := by
  obtain ⟨n, d⟩ := cutElimination.mp h
  rcases harrop_sc n hΓ d with h' | h'
  · exact .inl (cutElimination.mpr h')
  · exact .inr (cutElimination.mpr h')

/-- **A Harrop formula is join-prime**: `↑a` is a prime filter whenever `a` has
no `∨` in strictly positive position. -/
theorem primeAll_of_harrop {a : PLLFormula} (ha : Harrop a = true) : PrimeAll a := by
  intro x y h
  refine harrop_dp ?_ h
  intro φ hφ
  rw [List.mem_singleton] at hφ
  subst hφ
  exact ha

/-- Harrop-ness of any interderivable REPRESENTATIVE suffices. -/
theorem primeAll_of_harrop_rep {a b : PLLFormula} (hab : Interd a b)
    (hb : Harrop b = true) : PrimeAll a :=
  PrimeAll.of_interd hab (primeAll_of_harrop hb)

/-! ## Closedness and properness along the embedded ladder -/

/-- The substituted rung pairs are closed. -/
theorem atomFree_rnP_emb : ∀ k : Nat,
    atomFree (embed (rnP k).1) = true ∧ atomFree (embed (rnP k).2) = true := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show atomFree ((embed (rnP k).1).or (embed (rnP k).2)) = true
        simp only [LaxInfinite.atomFree, Bool.and_eq_true]
        exact ⟨h1, h2⟩
      · show atomFree (((embed (rnP k).1).or (embed (rnP k).2)).ifThen
            (embed (rnP k).1)) = true
        simp only [LaxInfinite.atomFree, Bool.and_eq_true]
        exact ⟨⟨h1, h2⟩, h1⟩

/-- Every substituted rung is a CLOSED formula. -/
theorem atomFree_rnSub (n : Nat) : atomFree (rnSub n) = true := by
  rcases parity3 n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rfl
  · show atomFree (embed (rn (2 * a + 1))) = true
    rw [rn_odd_eq]
    exact (atomFree_rnP_emb a).1
  · show atomFree (embed (rn (2 * a + 2))) = true
    rw [rn_even_eq]
    exact (atomFree_rnP_emb a).2

/-- Every rung above `⊥` is consistent, so `↑(t n)` is a PROPER filter.
(`t 0 = ⊥` is join-prime vacuously but `↑⊥` is the whole algebra, not a point.) -/
theorem proper_rnSub {i : Nat} (hi : i ≠ 0) : ¬ Deriv [rnSub i] .falsePLL := by
  intro h
  have h0 : Deriv [rnSub i] (rnSub 0) := h
  have hc := (rnSub_deriv_iff i 0).mp h0
  rcases parity3 i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact hi rfl
  · exact sat_rn_zero 0 (hc 0 ((sat_rn_odd a 0).mpr (Nat.zero_le a)))
  · exact sat_rn_zero (a + 1) (hc (a + 1) ((sat_rn_even a (a + 1)).mpr (Or.inr rfl)))

/-! ## The visible rungs -/

/-- `t1 = ◯⊥` is Harrop: `◯` is inert on the left for a disjunctive succedent. -/
theorem harrop_rnSub_one : Harrop (rnSub 1) = true := by
  rw [rnSub_one_eq]; rfl

/-- `t2 = ¬◯⊥` is Harrop (an implication into `⊥`). -/
theorem harrop_rnSub_two : Harrop (rnSub 2) = true := by
  rw [rnSub_two_eq]; rfl

/-- `t4 = (◯⊥ ∨ ¬◯⊥) ⊃ ◯⊥` is Harrop: the `∨` sits in the ANTECEDENT, a
negative position, and the consequent `◯⊥` is Harrop. -/
theorem harrop_rnSub_four : Harrop (rnSub 4) = true := by
  rw [rnSub_four_eq]; rfl

theorem visible_rnSub_one : Visible (rnSub 1) :=
  ⟨atomFree_rnSub 1, proper_rnSub (by decide),
   JoinPrime.of_primeAll (primeAll_of_harrop harrop_rnSub_one)⟩

theorem visible_rnSub_two : Visible (rnSub 2) :=
  ⟨atomFree_rnSub 2, proper_rnSub (by decide),
   JoinPrime.of_primeAll (primeAll_of_harrop harrop_rnSub_two)⟩

theorem visible_rnSub_four : Visible (rnSub 4) :=
  ⟨atomFree_rnSub 4, proper_rnSub (by decide),
   JoinPrime.of_primeAll (primeAll_of_harrop harrop_rnSub_four)⟩

/-! ### `t6`: Harrop does not apply to it, but does apply to its class

`t6 = t5 ⊃ t3` has the DISJUNCTION `t3 = ◯⊥ ∨ ¬◯⊥` as its consequent, hence
`Harrop (rnSub 6) = false` — the criterion does not apply.  Failure of a
sufficient criterion proves nothing either way; what settles `t6` is that
join-primality is invariant under interderivability and `t6` has a Harrop
REPRESENTATIVE, namely `¬¬◯⊥ ⊃ ◯⊥`.

The underlying intuitionistic law, for arbitrary `A`:

    ((A ∨ ¬A) ∨ ((A ∨ ¬A) ⊃ A)) ⊃ (A ∨ ¬A)   ⊣⊢   ¬¬A ⊃ A. -/

theorem harrop_rnSub_six : Harrop (rnSub 6) = false := rfl

theorem rnSub_six_eq :
    rnSub 6 =
      (((oBot.or (notPLL oBot)).or ((oBot.or (notPLL oBot)).ifThen oBot)).ifThen
        (oBot.or (notPLL oBot))) := rfl

/-- `((A ∨ ¬A) ∨ ((A ∨ ¬A) ⊃ A)) ⊃ (A ∨ ¬A)  ⊣⊢  ¬¬A ⊃ A` — hand `LaxND`
derivations (the `rn 6` rung is interderivable with a Harrop formula). -/
theorem interd_rn6_dneg (A : PLLFormula) :
    Interd (((A.or (notPLL A)).or ((A.or (notPLL A)).ifThen A)).ifThen (A.or (notPLL A)))
      ((notPLL (notPLL A)).ifThen A) := by
  constructor
  · -- [(D ∨ (D ⊃ A)) ⊃ D] ⊢ ¬¬A ⊃ A, where D = A ∨ ¬A
    refine Deriv.impIntro ?_
    have hE : Deriv [notPLL (notPLL A),
        ((A.or (notPLL A)).or ((A.or (notPLL A)).ifThen A)).ifThen (A.or (notPLL A))]
        ((A.or (notPLL A)).ifThen A) :=
      Deriv.impIntro
        (Deriv.orElim (Deriv.iden (.head _))
          (Deriv.iden (.head _))
          (Deriv.falsoElim A
            (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _))))
              (Deriv.iden (.head _)))))
    have hD : Deriv [notPLL (notPLL A),
        ((A.or (notPLL A)).or ((A.or (notPLL A)).ifThen A)).ifThen (A.or (notPLL A))]
        (A.or (notPLL A)) :=
      Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.orIntro2 hE)
    exact Deriv.orElim hD (Deriv.iden (.head _))
      (Deriv.falsoElim A
        (Deriv.impElim (Deriv.iden (.tail _ (.head _))) (Deriv.iden (.head _))))
  · -- [¬¬A ⊃ A] ⊢ (D ∨ (D ⊃ A)) ⊃ D
    refine Deriv.impIntro ?_
    refine Deriv.orElim (Deriv.iden (.head _)) (Deriv.iden (.head _)) ?_
    have hnn : Deriv [(A.or (notPLL A)).ifThen A,
        (A.or (notPLL A)).or ((A.or (notPLL A)).ifThen A),
        (notPLL (notPLL A)).ifThen A] (notPLL (notPLL A)) :=
      Deriv.impIntro
        (Deriv.impElim (Deriv.iden (.head _))
          (Deriv.impElim (Deriv.iden (.tail _ (.head _)))
            (Deriv.orIntro2 (Deriv.iden (.head _)))))
    exact Deriv.orIntro1
      (Deriv.impElim (Deriv.iden (.tail _ (.tail _ (.head _)))) hnn)

/-- `t6 ⊣⊢ ¬¬◯⊥ ⊃ ◯⊥`. -/
theorem rnSub_six_interd : Interd (rnSub 6) ((notPLL (notPLL oBot)).ifThen oBot) := by
  rw [rnSub_six_eq]
  exact interd_rn6_dneg oBot

theorem visible_rnSub_six : Visible (rnSub 6) :=
  ⟨atomFree_rnSub 6, proper_rnSub (by decide),
   JoinPrime.of_primeAll (primeAll_of_harrop_rep rnSub_six_interd rfl)⟩

/-! ## The odd rungs are NOT visible -/

/-- `t (2k+3) = t (2k+1) ∨ t (2k+2)` syntactically. -/
theorem rnSub_odd_split (k : Nat) :
    rnSub (2 * k + 3) = (rnSub (2 * k + 1)).or (rnSub (2 * k + 2)) := by
  show embed (rn (2 * k + 3)) = _
  rw [rn_odd_rec]
  rfl

/-- **REFUTED**: no odd rung from `t3 = ◯⊥ ∨ ¬◯⊥` on is join-prime.  Each is
literally the join of the two preceding rungs, and by `rnSub_deriv_iff` neither
is entailed, so `↑(t (2k+3))` is not a prime filter: these classes are proper
joins in RN(◯,{}), not points of the dual. -/
theorem not_joinPrime_rnSub_odd (k : Nat) : ¬ JoinPrime (rnSub (2 * k + 3)) := by
  intro hp
  have hd : Deriv [rnSub (2 * k + 3)] ((rnSub (2 * k + 1)).or (rnSub (2 * k + 2))) := by
    rw [← rnSub_odd_split]
    exact Deriv.iden (.head _)
  have hidx : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rcases hp _ _ (atomFree_rnSub _) (atomFree_rnSub _) hd with h | h
  · have hc := (rnSub_deriv_iff (2 * k + 3) (2 * k + 1)).mp h
    have hw : ladder.sat (rn (2 * k + 3)) (k + 1) := by
      rw [hidx]; exact (sat_rn_odd (k + 1) (k + 1)).mpr (Nat.le_refl _)
    have := (sat_rn_odd k (k + 1)).mp (hc (k + 1) hw)
    omega
  · have hc := (rnSub_deriv_iff (2 * k + 3) (2 * k + 2)).mp h
    have hw : ladder.sat (rn (2 * k + 3)) k := by
      rw [hidx]; exact (sat_rn_odd (k + 1) k).mpr (by omega)
    have := (sat_rn_even k k).mp (hc k hw)
    omega

/-! ## The gap family `g k = ◯ t (2k+1) ⊃ t (2k+1)`

`Harrop (g k) = Harrop (t (2k+1))`, so the criterion applies exactly at `k = 0`,
where `t 1 = ◯⊥` is Harrop.  But `g 0 = ◯◯⊥ ⊃ ◯⊥` is a THEOREM (`◯` is
idempotent), so `↑(g 0) = ↑⊤` and `visible_gap_zero` says nothing new: it is
`visible_top` in disguise.  For `k ≥ 1` the consequent `t (2k+1)` is a
disjunction (`harrop_rnSub_odd`), so `Harrop (g (k+1)) = false` and the
criterion does not apply.  That is NOT a refutation — `g (k+1)` may or may not
be join-prime; it is OPEN here. -/

/-- The gap formulas `g k = ◯ t (2k+1) ⊃ t (2k+1)`. -/
def gap (k : Nat) : PLLFormula :=
  (rnSub (2 * k + 1)).somehow.ifThen (rnSub (2 * k + 1))

theorem atomFree_gap (k : Nat) : atomFree (gap k) = true := by
  show atomFree ((rnSub (2 * k + 1)).somehow.ifThen (rnSub (2 * k + 1))) = true
  simp only [LaxInfinite.atomFree, Bool.and_eq_true]
  exact ⟨atomFree_rnSub _, atomFree_rnSub _⟩

/-- No odd rung from `t3` on is Harrop: each is literally a disjunction.  (At
those rungs the criterion is not merely inapplicable — `not_joinPrime_rnSub_odd`
refutes primality outright.) -/
theorem harrop_rnSub_odd (k : Nat) : Harrop (rnSub (2 * k + 3)) = false := by
  rw [rnSub_odd_split]; rfl

theorem harrop_gap_zero : Harrop (gap 0) = true := rfl

theorem harrop_gap_succ (k : Nat) : Harrop (gap (k + 1)) = false := by
  show Harrop (rnSub (2 * (k + 1) + 1)) = false
  rw [show 2 * (k + 1) + 1 = 2 * k + 3 from by omega]
  exact harrop_rnSub_odd k

/-- `g 0 = ◯◯⊥ ⊃ ◯⊥ ⊣⊢ ⊤`: idempotency of `◯` collapses the bottom gap. -/
theorem interd_gap_zero_top : Interd (gap 0) truePLL :=
  ⟨⟨.impIntro (.iden (.head _))⟩,
   ⟨.impIntro (.laxElim (.iden (.head _)) (.iden (.head _)))⟩⟩

theorem proper_gap_zero : ¬ Deriv [gap 0] .falsePLL :=
  fun h => proper_top (Deriv.cutHead interd_gap_zero_top.2 h)

theorem visible_gap_zero : Visible (gap 0) :=
  ⟨atomFree_gap 0, proper_gap_zero,
   JoinPrime.of_primeAll (primeAll_of_harrop harrop_gap_zero)⟩

/-! ## The semantic route

An **exact rooted model** for `a` is a pointed model `(M, w)` with

    M, w ⊩ a      and      ∀ closed φ,  M, w ⊩ φ  →  a ⊢ φ.

Join-primality is then immediate from the locality of the Kripke `∨` clause:
soundness sends `a ⊢ x ∨ y` to `M, w ⊩ x ∨ y`, the clause splits it, and
exactness sends the surviving disjunct back. -/

/-- A pointed model whose closed theory is exactly the closed consequences
of `a`. -/
structure ExactRooted (a : PLLFormula) where
  M : ConstraintModel
  w : M.W
  forces : M.force w a
  closedComplete : ∀ φ : PLLFormula, atomFree φ = true → M.force w φ → Deriv [a] φ

/-- **Exactness gives visibility.**  The whole content is the locality of the
`∨` clause: `M, w ⊩ x ∨ y` is `M, w ⊩ x` or `M, w ⊩ y`, with no quantification
over successors. -/
theorem joinPrime_of_exactRooted {a : PLLFormula} (E : ExactRooted a) : JoinPrime a := by
  intro x y hx hy h
  obtain ⟨d⟩ := h
  have hxy : E.M.force E.w (x.or y) := by
    refine soundness d E.M E.w ?_
    intro ψ hψ
    rw [List.mem_singleton] at hψ
    subst hψ
    exact E.forces
  have hxy' : E.M.force E.w x ∨ E.M.force E.w y := hxy
  rcases hxy' with h' | h'
  · exact .inl (E.closedComplete x hx h')
  · exact .inr (E.closedComplete y hy h')

/-- The ladder truth set of an even rung is the PRINCIPAL upset `↑(k+1)`: any
rung true at `k+1` is true everywhere `t (2k+2)` is. -/
theorem even_upset {k m : Nat} (h : ladder.sat (rn m) (k + 1)) :
    ∀ w : Nat, ladder.sat (rn (2 * k + 2)) w → ladder.sat (rn m) w := by
  rcases parity3 m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · exact absurd h (sat_rn_zero _)
  · rw [sat_rn_odd] at h
    intro w hw
    rw [sat_rn_even] at hw
    rw [sat_rn_odd]
    omega
  · rw [sat_rn_even] at h
    intro w hw
    rw [sat_rn_even] at hw
    rw [sat_rn_even]
    omega

/-- **The semantic route, as far as available exactness reaches.**  Every EVEN
rung is join-prime against RUNG-SHAPED disjunctions:

    t (2k+2) ⊢ t i ∨ t j   ⟹   t (2k+2) ⊢ t i   or   t (2k+2) ⊢ t j.

Proof: soundness through `Skel.transfer` turns the hypothesis into truth-set
containment on the ladder; at the world `k+1`, which forces `t (2k+2)`, one
disjunct must hold; and since the truth set of `t (2k+2)` is the principal
upset `↑(k+1)`, that disjunct is forced wherever `t (2k+2)` is, so
`rnSub_deriv_iff` returns a derivation.

This is NOT full join-primality: the quantifier in `JoinPrime` ranges over ALL
closed `x`, `y`, and `Skel.transfer` controls only formulas in the image of
`embed` on `◯`-free formulas, i.e. the sublattice of RN(◯,{}) generated by
`◯⊥`.  The missing statement is exactly the `closedComplete` field of
`ExactRooted` for the ladder point:

    ∀ φ, atomFree φ = true → ladder.cm.force (some (k+1)) φ → Deriv [rnSub (2k+2)] φ,

i.e. that the ladder model is EXACT for the whole closed fragment.  That is a
completeness theorem about RN(◯,{}), not about the embedded ladder: closed
formulas outside the `◯⊥`-generated sublattice (`◯(¬◯⊥)` is one, by
`LaxInfinite.closed_lax_ge_eight`) are not controlled by `Skel.transfer`.  It
is OPEN here. -/
theorem rnSub_even_prime_on_rungs (k i j : Nat)
    (h : Deriv [rnSub (2 * k + 2)] ((rnSub i).or (rnSub j))) :
    Deriv [rnSub (2 * k + 2)] (rnSub i) ∨ Deriv [rnSub (2 * k + 2)] (rnSub j) := by
  obtain ⟨d⟩ := h
  have key : ∀ w : Nat, ladder.sat (rn (2 * k + 2)) w →
      (ladder.sat (rn i) w ∨ ladder.sat (rn j) w) := by
    intro w hw
    have hor : ladder.cm.force (some w) ((rnSub i).or (rnSub j)) := by
      refine soundness d ladder.cm (some w) ?_
      intro ψ hψ
      rw [List.mem_singleton] at hψ
      subst hψ
      exact (ladder.transfer (rn_boxFree (2 * k + 2)) w).mpr hw
    have hor' : ladder.cm.force (some w) (rnSub i) ∨
        ladder.cm.force (some w) (rnSub j) := hor
    rcases hor' with h1 | h1
    · exact .inl ((ladder.transfer (rn_boxFree i) w).mp h1)
    · exact .inr ((ladder.transfer (rn_boxFree j) w).mp h1)
  rcases key (k + 1) ((sat_rn_even k (k + 1)).mpr (Or.inr rfl)) with h1 | h1
  · exact .inl ((rnSub_deriv_iff _ _).mpr (even_upset h1))
  · exact .inr ((rnSub_deriv_iff _ _).mpr (even_upset h1))

/-! ## Axiom audits -/

/--
info: 'PLLND.Visibility.JoinPrime.of_primeAll' does not depend on any axioms
-/
#guard_msgs in
#print axioms JoinPrime.of_primeAll

/--
info: 'PLLND.Visibility.PrimeAll.of_interd' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms PrimeAll.of_interd

/--
info: 'PLLND.Visibility.deriv_top' does not depend on any axioms
-/
#guard_msgs in
#print axioms deriv_top

/--
info: 'PLLND.Visibility.primeAll_top' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms primeAll_top

/--
info: 'PLLND.Visibility.proper_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proper_top

/--
info: 'PLLND.Visibility.visible_top' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_top

/--
info: 'PLLND.Visibility.harrop_sc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms harrop_sc

/--
info: 'PLLND.Visibility.harrop_dp' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms harrop_dp

/--
info: 'PLLND.Visibility.primeAll_of_harrop' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms primeAll_of_harrop

/--
info: 'PLLND.Visibility.primeAll_of_harrop_rep' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms primeAll_of_harrop_rep

/--
info: 'PLLND.Visibility.atomFree_rnP_emb' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms atomFree_rnP_emb

/--
info: 'PLLND.Visibility.atomFree_rnSub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms atomFree_rnSub

/--
info: 'PLLND.Visibility.proper_rnSub' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proper_rnSub

/--
info: 'PLLND.Visibility.harrop_rnSub_one' does not depend on any axioms
-/
#guard_msgs in
#print axioms harrop_rnSub_one

/--
info: 'PLLND.Visibility.harrop_rnSub_two' does not depend on any axioms
-/
#guard_msgs in
#print axioms harrop_rnSub_two

/--
info: 'PLLND.Visibility.harrop_rnSub_four' does not depend on any axioms
-/
#guard_msgs in
#print axioms harrop_rnSub_four

/--
info: 'PLLND.Visibility.visible_rnSub_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_rnSub_one

/--
info: 'PLLND.Visibility.visible_rnSub_two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_rnSub_two

/--
info: 'PLLND.Visibility.visible_rnSub_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_rnSub_four

/--
info: 'PLLND.Visibility.harrop_rnSub_six' does not depend on any axioms
-/
#guard_msgs in
#print axioms harrop_rnSub_six

/--
info: 'PLLND.Visibility.rnSub_six_eq' does not depend on any axioms
-/
#guard_msgs in
#print axioms rnSub_six_eq

/--
info: 'PLLND.Visibility.interd_rn6_dneg' does not depend on any axioms
-/
#guard_msgs in
#print axioms interd_rn6_dneg

/--
info: 'PLLND.Visibility.rnSub_six_interd' does not depend on any axioms
-/
#guard_msgs in
#print axioms rnSub_six_interd

/--
info: 'PLLND.Visibility.visible_rnSub_six' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_rnSub_six

/--
info: 'PLLND.Visibility.rnSub_odd_split' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms rnSub_odd_split

/--
info: 'PLLND.Visibility.not_joinPrime_rnSub_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms not_joinPrime_rnSub_odd

/--
info: 'PLLND.Visibility.gap' does not depend on any axioms
-/
#guard_msgs in
#print axioms gap

/--
info: 'PLLND.Visibility.atomFree_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms atomFree_gap

/--
info: 'PLLND.Visibility.harrop_rnSub_odd' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms harrop_rnSub_odd

/--
info: 'PLLND.Visibility.harrop_gap_zero' does not depend on any axioms
-/
#guard_msgs in
#print axioms harrop_gap_zero

/--
info: 'PLLND.Visibility.harrop_gap_succ' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms harrop_gap_succ

/--
info: 'PLLND.Visibility.interd_gap_zero_top' does not depend on any axioms
-/
#guard_msgs in
#print axioms interd_gap_zero_top

/--
info: 'PLLND.Visibility.proper_gap_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms proper_gap_zero

/--
info: 'PLLND.Visibility.visible_gap_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms visible_gap_zero

/--
info: 'PLLND.Visibility.joinPrime_of_exactRooted' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms joinPrime_of_exactRooted

/--
info: 'PLLND.Visibility.even_upset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms even_upset

/--
info: 'PLLND.Visibility.rnSub_even_prime_on_rungs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnSub_even_prime_on_rungs

end Visibility
end PLLND
