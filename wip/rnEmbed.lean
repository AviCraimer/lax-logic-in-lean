import LaxLogic.PLLSemUIFrag
import LaxLogic.PLLSemUIOFree
import LaxLogic.PLLSemUICtx
import LaxLogic.PLLConfluentComplete

/-!
# The Rieger–Nishimura ladder embeds in the variable-free fragments
# of PLL and PCLL under `p ↦ ◯⊥`

This file proves that the substitution `p ↦ ◯⊥` carries the
one-variable Rieger–Nishimura rungs to PAIRWISE NON-INTERDERIVABLE
variable-free formulas, in PLL (`LaxND`) and in PCLL (= PLL +
`◯(A∨B) ⊃ (◯A∨◯B)`, the system `DerivU` of
`PLLConfluentComplete.lean`) — for EVERY pair of rungs, not merely a
finite initial segment.  Consequently both variable-free fragments
RN(PLL,◯,{}) and RN(PCLL,◯,{}) are infinite up to interderivability
(`varfree_no_finite_cover_pll` / `_pcll`), and for every crank bound
`r` some rung escapes the crank-≤`r` classes (`rank_escape_pll` /
`_pcll`, via `frag_reps_exist'`).

## The transfer mechanism (T1)

`Skel` is a bare one-variable IPC skeleton: a preorder `(W, le)` with
an upward-closed set `U` (the extension of the variable `p`).
`Skel.sat` is ordinary IPC Kripke forcing over it (`p` reads `U`, all
other atoms are false; the `◯`-clause is junk and never used).

`Skel.cm` adjoins ONE fresh fallible point `f` (encoded `none`):

* `Rᵢ`: the skeleton order, with `f` an `Rᵢ`-top above EVERYTHING
  (`v Rᵢ f` for all `v`, `f Rᵢ f` only);
* `Rₘ`: the identity on the skeleton, plus `v Rₘ f` exactly for
  `v ∈ U`, plus `f Rₘ f`;
* `F = {f}`; every atom true exactly at `f` (p-pure).

Deviation from the commissioning sketch: `Rᵢ` puts `f` above ALL of
`W`, not only above `U` — with `f` reachable only from `U`,
`Rᵢ`-transitivity fails (`u ≤ v ∈ U` needs `u Rᵢ f` but upward
closure runs the wrong way).  With `f` on top of everything all frame
laws hold, the model is MUTUALLY CONFLUENT (`Skel.cm_confluent`, the
`Rₘ`-to-`f` square closing via upward closure of `U`), and:

* `Skel.force_oBot`: the truth set of `◯⊥` restricted to `W` is
  exactly `U`;
* `Skel.transfer`: for ◯-free `A`, the constraint model forces
  `A[p := ◯⊥]` at `w ∈ W` iff the skeleton IPC-forces `A` at `w`
  (the fallible top forces everything, so it never constrains an
  implication — the `topExt` conservativity pattern of
  `PLLSemUIOFree.lean`).

## The separation payload (T2)

An IPC separation on any skeleton (`A` forced, `B` refuted at some
world) yields underivability of the substituted formulas — in PCLL,
hence in PLL: `not_derivU_of_sep`, `rn_transfer_pcll`,
`rn_transfer_pll`.  Soundness instruments: `soundness` (PLL),
`derivU_sound` + `Skel.cm_confluent` (PCLL).

## The ladder instantiation (T3)

Rungs (`rn`), one standard presentation, pinned by `rn_zero/one/two`
and the recursions `rn_odd_rec`/`rn_even_rec`:

    rn 0 = ⊥,  rn 1 = p,  rn 2 = ¬p,
    rn (2k+3) = rn (2k+1) ∨ rn (2k+2),
    rn (2k+4) = rn (2k+3) ⊃ rn (2k+1).

(So rn 3 = p ∨ ¬p, rn 4 ≡ ¬¬p, rn 5 ≡ ¬p ∨ ¬¬p, … — Nishimura's
ladder, in the ∨/⊃ recursion form.)

The separating skeleton is the INFINITE Rieger–Nishimura frame
`ladder`: worlds `ℕ`, `le w v ↔ v = w ∨ v + 2 ≤ w` (each world sees
itself and everything at least two earlier; consecutive worlds are
incomparable), `U = {0}`.  The rung truth sets have a closed form
(`sat_rnP`, proved by ONE arithmetic induction, no `decide`):

    sat (rn (2k+1)) w ↔ w ≤ k
    sat (rn (2k+2)) w ↔ w + 1 ≤ k ∨ w = k + 1

whence every pair of distinct rungs separates (`ladder_sep`) and the
headline theorems follow for ALL indices:

    rn_pairwise_pcll : i ≠ j → ¬ InterdU (rnSub i) (rnSub j)
    rn_pairwise_pll  : i ≠ j → ¬ Interd  (rnSub i) (rnSub j)

## Structure notes (T4)

* `deriv_substP` / `interd_substP`: substitution respects
  derivability and interderivability (so `A ↦ A[p := ◯⊥]` is
  well-defined and monotone on interderivability classes; it respects
  the connectives SYNTACTICALLY — `substP` commutes with them by
  definition).
* `interdU_of_interd`: the identity map RN(PLL,◯,{}) →
  RN(PCLL,◯,{}) is well-defined (more axioms, coarser quotient).
* Syntactic base of the dictionary correspondence: `rnSub 0 = ⊥`,
  `rnSub 1 = ◯⊥` (q2), `rnSub 2 = ¬◯⊥` (q3), `rnSub 3 = ◯⊥ ∨ ¬◯⊥`
  (q4) — all `rfl` — and `rnSub_four_interd`: `rnSub 4 ≡ ¬¬◯⊥` (q6),
  by hand `LaxND` derivations of the general IPC fact
  `(A ∨ ¬A ⊃ A) ≡ ¬¬A` (`interd_peirce_dneg`).
* `crank_rnP_emb`: the substituted rungs have crank `k+2` / `k+3` at
  pair-level `k` — the ladder supplies two fresh classes per crank,
  all the way up.

## The image order (beyond the commission)

`rnSub_deriv_iff` / `rnSub_derivU_iff`: rung-to-rung derivability of
the substituted rungs — in PLL AND in PCLL — is EXACTLY truth-set
containment on the ladder (positive halves from three one-line
derivation schemas chained along the ladder; negative halves from
soundness through the transfer).  Hence `rnSub_derivU_iff_deriv`:
PCLL is CONSERVATIVE over PLL for rung-to-rung derivability — the
embedding is an order-isomorphism onto its image in both quotients,
with the same image order; distribution's collapses do not touch the
embedded ladder's arrows.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI ConfluentU

/-- The distinguished propositional variable. -/
def pv : String := "p"

/-- `◯⊥`. -/
def oBot : PLLFormula := .somehow .falsePLL

/-- The embedding map on formulas: substitute `◯⊥` for `p`. -/
def embed (A : PLLFormula) : PLLFormula := substP pv oBot A

/-! ## One-variable IPC skeletons -/

/-- A one-variable IPC Kripke skeleton: a preorder with an
upward-closed extension `U` for the variable `p`. -/
structure Skel where
  W : Type
  le : W → W → Prop
  refl : ∀ w, le w w
  trans : ∀ {w v u}, le w v → le v u → le w u
  U : Set W
  upU : ∀ {w v}, le w v → w ∈ U → v ∈ U

/-- IPC forcing over a skeleton: `p` reads `U`, every other atom is
false everywhere, `⊥` is absurd, the connectives are the standard
intuitionistic clauses.  The `◯`-clause is JUNK (`False`); it is never
consumed — every use is guarded by `boxFree`. -/
def Skel.sat (S : Skel) : PLLFormula → S.W → Prop
  | .prop a, w => a = pv ∧ w ∈ S.U
  | .falsePLL, _ => False
  | .and A B, w => S.sat A w ∧ S.sat B w
  | .or A B, w => S.sat A w ∨ S.sat B w
  | .ifThen A B, w => ∀ v, S.le w v → S.sat A v → S.sat B v
  | .somehow _, _ => False

/-! ## The lifted constraint model: one fresh fallible top -/

/-- `Rᵢ` of the lift: the skeleton order, with the fallible point
(`none`) on top of EVERYTHING. -/
def riL (S : Skel) : Option S.W → Option S.W → Prop
  | some v, some w => S.le v w
  | some _, none   => True
  | none,   none   => True
  | none,   some _ => False

/-- `Rₘ` of the lift: identity on the skeleton, with the fallible
point `Rₘ`-reachable exactly from `U` (and from itself). -/
def rmL (S : Skel) : Option S.W → Option S.W → Prop
  | some v, some w => v = w
  | some v, none   => v ∈ S.U
  | none,   none   => True
  | none,   some _ => False

/-- The constraint model over `W ⊕ {f}`: `F = {f}`, valuation p-pure
(every atom true exactly at `f`, as `full_F` requires).  Reducible so
that concrete instances expose the worlds and relations, as with the
finite models of `PLLFrames.lean`. -/
@[reducible] def Skel.cm (S : Skel) : ConstraintModel where
  W := Option S.W
  Ri := riL S
  Rm := rmL S
  F := {x | x = none}
  V _ := {x | x = none}
  refl_i x := by
    cases x with
    | none => exact trivial
    | some a => exact S.refl a
  trans_i {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
        | some b =>
            cases z with
            | none => exact trivial
            | some c => exact S.trans h1 h2
  refl_m x := by
    cases x with
    | none => exact trivial
    | some a => exact rfl
  trans_m {x y z} h1 h2 := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h1 : False).elim
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact trivial
    | some a =>
        cases y with
        | none =>
            cases z with
            | some c => exact (h2 : False).elim
            | none => exact h1
        | some b =>
            cases z with
            | none => exact ((h1 : a = b).symm ▸ h2 : a ∈ S.U)
            | some c => exact (h1 : a = b).trans (h2 : b = c)
  sub_mi {x y} h := by
    cases x with
    | none =>
        cases y with
        | some b => exact (h : False).elim
        | none => exact trivial
    | some a =>
        cases y with
        | none => exact trivial
        | some b => obtain rfl := (h : a = b); exact S.refl a
  hered_F {x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  hered_V {a x y} h hx := by
    obtain rfl := (hx : x = none)
    cases y with
    | some b => exact (h : False).elim
    | none => exact rfl
  full_F {a x} hx := hx

/-- **The lift is mutually confluent** — the key frame condition for
PCLL.  The only nontrivial square (`x Rₘ f`, `x Rᵢ v`) closes through
`f` because `U` is upward closed. -/
theorem Skel.cm_confluent (S : Skel) : MutuallyConfluent S.cm := by
  intro x w v hm hi
  cases x with
  | none =>
      cases w with
      | some b => exact (hm : False).elim
      | none =>
          cases v with
          | some c => exact (hi : False).elim
          | none => exact ⟨none, trivial, trivial⟩
  | some a =>
      cases w with
      | none =>
          cases v with
          | none => exact ⟨none, trivial, trivial⟩
          | some c => exact ⟨none, trivial, S.upU hi hm⟩
      | some b =>
          obtain rfl := (hm : a = b)
          cases v with
          | none => exact ⟨none, trivial, trivial⟩
          | some c => exact ⟨some c, hi, rfl⟩

/-- **T1(a): the truth set of `◯⊥`, restricted to the skeleton, is
exactly `U`.**  A skeleton world sees a fallible row-member through
every intuitionistic successor iff it lies in `U`. -/
theorem Skel.force_oBot (S : Skel) (x : S.W) :
    S.cm.force (some x) oBot ↔ x ∈ S.U := by
  constructor
  · intro h
    obtain ⟨u, hmu, hu⟩ := h (some x) (S.refl x)
    obtain rfl := (hu : u = none)
    exact hmu
  · intro hx v hv
    refine ⟨none, ?_, rfl⟩
    cases v with
    | none => exact trivial
    | some y => exact S.upU hv hx

/-- **T1(b), the transfer lemma**: for ◯-free `A`, the lifted
constraint model forces `A[p := ◯⊥]` at a skeleton world iff the
skeleton IPC-forces `A` there.  The atom case is `force_oBot`; in the
implication case the fallible top forces everything
(`force_of_fallible`) and so never refutes an implication. -/
theorem Skel.transfer (S : Skel) :
    ∀ {A : PLLFormula}, boxFree A = true →
      ∀ w : S.W, (S.cm.force (some w) (substP pv oBot A) ↔ S.sat A w) := by
  intro A
  induction A with
  | prop a =>
      intro _ w
      by_cases ha : a = pv
      · subst ha
        show S.cm.force (some w) oBot ↔ S.sat (.prop pv) w
        rw [S.force_oBot w]
        exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
      · have he : substP pv oBot (.prop a) = .prop a := by
          show (if a = pv then oBot else .prop a) = .prop a
          exact if_neg ha
        rw [he]
        constructor
        · intro h
          have h' : (some w : Option S.W) = none := h
          exact absurd h' (Option.some_ne_none w)
        · intro h
          exact absurd h.1 ha
  | falsePLL =>
      intro _ w
      show ((some w : Option S.W) = none) ↔ False
      exact iff_false_intro (Option.some_ne_none w)
  | and A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (S.cm.force (some w) (substP pv oBot A) ∧
            S.cm.force (some w) (substP pv oBot B)) ↔
          (S.sat A w ∧ S.sat B w)
      exact and_congr (ihA h.1 w) (ihB h.2 w)
  | or A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (S.cm.force (some w) (substP pv oBot A) ∨
            S.cm.force (some w) (substP pv oBot B)) ↔
          (S.sat A w ∨ S.sat B w)
      exact or_congr (ihA h.1 w) (ihB h.2 w)
  | ifThen A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (∀ v, S.cm.Ri (some w) v →
            S.cm.force v (substP pv oBot A) → S.cm.force v (substP pv oBot B)) ↔
          (∀ y, S.le w y → S.sat A y → S.sat B y)
      constructor
      · intro hf y hle hsy
        exact (ihB h.2 y).mp (hf (some y) hle ((ihA h.1 y).mpr hsy))
      · intro hs v hv hvA
        cases v with
        | none => exact S.cm.force_of_fallible rfl
        | some y => exact (ihB h.2 y).mpr (hs y hv ((ihA h.1 y).mp hvA))
  | somehow A ih =>
      intro h w
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-! ## PCLL interderivability, and the T2 separation payload -/

/-- Interderivability in PCLL (= PLL + distribution, `DerivU`). -/
def InterdU (φ ψ : PLLFormula) : Prop :=
  DerivU [φ] ψ ∧ DerivU [ψ] φ

/-- Cut for single-hypothesis PCLL derivability. -/
theorem DerivU.cutHead {φ ψ χ : PLLFormula}
    (h1 : DerivU [φ] ψ) (h2 : DerivU [ψ] χ) : DerivU [φ] χ :=
  DerivU.mp (h2.deduction.rename (by simp)) h1

theorem InterdU.refl (φ : PLLFormula) : InterdU φ φ :=
  ⟨.hyp (by simp), .hyp (by simp)⟩

theorem InterdU.symm {φ ψ : PLLFormula} (h : InterdU φ ψ) : InterdU ψ φ :=
  ⟨h.2, h.1⟩

theorem InterdU.trans {φ ψ χ : PLLFormula}
    (h1 : InterdU φ ψ) (h2 : InterdU ψ χ) : InterdU φ χ :=
  ⟨DerivU.cutHead h1.1 h2.1, DerivU.cutHead h2.2 h1.2⟩

/-- **T4: the identity is a well-defined map of quotients
RN(PLL,◯,{}) → RN(PCLL,◯,{})** — PCLL has more axioms, so its
quotient is coarser.  (It is a lattice homomorphism: meets and joins
in both quotients are induced by the same connectives `∧`, `∨`.) -/
theorem interdU_of_interd {φ ψ : PLLFormula} (h : Interd φ ψ) :
    InterdU φ ψ :=
  ⟨h.1.elim fun d => .of_nd d, h.2.elim fun d => .of_nd d⟩

/-- **T2, PCLL form**: an IPC separation on a skeleton refutes PCLL
derivability of the substituted formulas (via `derivU_sound` and
mutual confluence of the lift). -/
theorem not_derivU_of_sep (S : Skel) {A B : PLLFormula}
    (hA : boxFree A = true) (hB : boxFree B = true) {w : S.W}
    (hfA : S.sat A w) (hfB : ¬ S.sat B w) :
    ¬ DerivU [embed A] (embed B) := by
  intro hd
  apply hfB
  refine (S.transfer hB w).mp ?_
  refine derivU_sound hd S.cm_confluent (some w) ?_
  intro ψ hψ
  rw [List.mem_singleton] at hψ
  subst hψ
  exact (S.transfer hA w).mpr hfA

/-- **T2, PLL form** (weaker premise refuted: plain `LaxND`). -/
theorem not_deriv_of_sep (S : Skel) {A B : PLLFormula}
    (hA : boxFree A = true) (hB : boxFree B = true) {w : S.W}
    (hfA : S.sat A w) (hfB : ¬ S.sat B w) :
    ¬ Deriv [embed A] (embed B) :=
  fun h => not_derivU_of_sep S hA hB hfA hfB (h.elim fun d => .of_nd d)

/-- **The reusable transfer theorem, PCLL**: explicit Kripke
separation data refutes interderivability of the `p ↦ ◯⊥`
substitution instances in PCLL. -/
theorem rn_transfer_pcll (S : Skel) {A B : PLLFormula}
    (hA : boxFree A = true) (hB : boxFree B = true) {w : S.W}
    (hfA : S.sat A w) (hfB : ¬ S.sat B w) :
    ¬ InterdU (embed A) (embed B) :=
  fun hI => not_derivU_of_sep S hA hB hfA hfB hI.1

/-- **The reusable transfer theorem, PLL.** -/
theorem rn_transfer_pll (S : Skel) {A B : PLLFormula}
    (hA : boxFree A = true) (hB : boxFree B = true) {w : S.W}
    (hfA : S.sat A w) (hfB : ¬ S.sat B w) :
    ¬ Interd (embed A) (embed B) :=
  fun hI => rn_transfer_pcll S hA hB hfA hfB (interdU_of_interd hI)

/-! ## The Rieger–Nishimura rungs -/

/-- The odd/even rung pairs: `rnP k = (rn (2k+1), rn (2k+2))`. -/
def rnP : Nat → PLLFormula × PLLFormula
  | 0 => (.prop pv, .ifThen (.prop pv) .falsePLL)
  | k + 1 =>
      ((rnP k).1.or (rnP k).2, ((rnP k).1.or (rnP k).2).ifThen (rnP k).1)

/-- The Rieger–Nishimura rungs. -/
def rn : Nat → PLLFormula
  | 0 => .falsePLL
  | n + 1 => if n % 2 = 0 then (rnP (n / 2)).1 else (rnP (n / 2)).2

/-- The substituted rungs: `rn n [p := ◯⊥]`, variable-free. -/
def rnSub (n : Nat) : PLLFormula := embed (rn n)

theorem rn_odd_eq (k : Nat) : rn (2 * k + 1) = (rnP k).1 := by
  have h1 : 2 * k % 2 = 0 := by omega
  have h2 : 2 * k / 2 = k := by omega
  show (if 2 * k % 2 = 0 then (rnP (2 * k / 2)).1 else (rnP (2 * k / 2)).2)
      = (rnP k).1
  rw [if_pos h1, h2]

theorem rn_even_eq (k : Nat) : rn (2 * k + 2) = (rnP k).2 := by
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  show (if (2 * k + 1) % 2 = 0 then (rnP ((2 * k + 1) / 2)).1
      else (rnP ((2 * k + 1) / 2)).2) = (rnP k).2
  rw [if_neg h1, h2]

/-! The standard recursion, pinned (this DOCUMENTS the presentation):
`rn 0 = ⊥`, `rn 1 = p`, `rn 2 = ¬p`,
`rn (2k+3) = rn (2k+1) ∨ rn (2k+2)`,
`rn (2k+4) = rn (2k+3) ⊃ rn (2k+1)`. -/

theorem rn_zero : rn 0 = .falsePLL := rfl
theorem rn_one : rn 1 = .prop pv := rfl
theorem rn_two : rn 2 = notPLL (.prop pv) := rfl

theorem rn_odd_rec (k : Nat) :
    rn (2 * k + 3) = (rn (2 * k + 1)).or (rn (2 * k + 2)) := by
  have e : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [e, rn_odd_eq (k + 1), rn_odd_eq k, rn_even_eq k]
  rfl

theorem rn_even_rec (k : Nat) :
    rn (2 * k + 4) = (rn (2 * k + 3)).ifThen (rn (2 * k + 1)) := by
  have e1 : 2 * k + 4 = 2 * (k + 1) + 2 := by omega
  have e2 : 2 * k + 3 = 2 * (k + 1) + 1 := by omega
  rw [e1, e2, rn_even_eq (k + 1), rn_odd_eq (k + 1), rn_odd_eq k]
  rfl

/-- The rungs are ◯-free. -/
theorem rnP_boxFree :
    ∀ k, boxFree (rnP k).1 = true ∧ boxFree (rnP k).2 = true := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show boxFree ((rnP k).1.or (rnP k).2) = true
        show (boxFree (rnP k).1 && boxFree (rnP k).2) = true
        rw [h1, h2]
        rfl
      · show boxFree (((rnP k).1.or (rnP k).2).ifThen (rnP k).1) = true
        show ((boxFree (rnP k).1 && boxFree (rnP k).2) && boxFree (rnP k).1)
            = true
        rw [h1, h2]
        rfl

theorem rn_boxFree (n : Nat) : boxFree (rn n) = true := by
  match n with
  | 0 => rfl
  | m + 1 =>
      show boxFree (if m % 2 = 0 then (rnP (m / 2)).1 else (rnP (m / 2)).2)
          = true
      split
      · exact (rnP_boxFree _).1
      · exact (rnP_boxFree _).2

/-- The rungs' only atom is `p`. -/
theorem rnP_atoms :
    ∀ k, (∀ a ∈ (rnP k).1.atoms, a = pv) ∧ (∀ a ∈ (rnP k).2.atoms, a = pv) := by
  intro k
  induction k with
  | zero =>
      constructor
      · intro a ha
        have ha' : a ∈ (PLLFormula.prop pv).atoms := ha
        simpa using ha'
      · intro a ha
        have ha' : a ∈ ((PLLFormula.prop pv).ifThen .falsePLL).atoms := ha
        rcases mem_atoms_ifThen.mp ha' with h | h
        · simpa using h
        · simp at h
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · intro a ha
        have ha' : a ∈ ((rnP k).1.or (rnP k).2).atoms := ha
        rcases mem_atoms_or.mp ha' with h | h
        exacts [h1 a h, h2 a h]
      · intro a ha
        have ha' : a ∈ (((rnP k).1.or (rnP k).2).ifThen (rnP k).1).atoms := ha
        rcases mem_atoms_ifThen.mp ha' with h | h
        · rcases mem_atoms_or.mp h with h' | h'
          exacts [h1 a h', h2 a h']
        · exact h1 a h

theorem rn_atoms (n : Nat) : ∀ a ∈ (rn n).atoms, a = pv := by
  match n with
  | 0 =>
      intro a ha
      have ha' : a ∈ (PLLFormula.falsePLL).atoms := ha
      simp at ha'
  | m + 1 =>
      show ∀ a ∈ (if m % 2 = 0 then (rnP (m / 2)).1 else (rnP (m / 2)).2).atoms,
        a = pv
      split
      · exact (rnP_atoms _).1
      · exact (rnP_atoms _).2

/-- Substituting `◯⊥` for `p` in a `p`-only formula kills all atoms. -/
theorem embed_atoms {A : PLLFormula} (hA : ∀ a ∈ A.atoms, a = pv) :
    (embed A).atoms = ∅ := by
  induction A with
  | prop b =>
      have hb : b = pv := hA b (by simp)
      subst hb
      exact rfl
  | falsePLL => exact rfl
  | and A B ihA ihB =>
      show ((embed A).and (embed B)).atoms = ∅
      rw [atoms_and,
        ihA fun a ha => hA a (mem_atoms_and.mpr (.inl ha)),
        ihB fun a ha => hA a (mem_atoms_and.mpr (.inr ha))]
      simp
  | or A B ihA ihB =>
      show ((embed A).or (embed B)).atoms = ∅
      rw [atoms_or,
        ihA fun a ha => hA a (mem_atoms_or.mpr (.inl ha)),
        ihB fun a ha => hA a (mem_atoms_or.mpr (.inr ha))]
      simp
  | ifThen A B ihA ihB =>
      show ((embed A).ifThen (embed B)).atoms = ∅
      rw [atoms_ifThen,
        ihA fun a ha => hA a (mem_atoms_ifThen.mpr (.inl ha)),
        ihB fun a ha => hA a (mem_atoms_ifThen.mpr (.inr ha))]
      simp
  | somehow A ihA =>
      show ((embed A).somehow).atoms = ∅
      rw [atoms_somehow]
      exact ihA fun a ha => hA a ha

/-- **The substituted rungs are variable-free**: they live in
RN(◯,{}). -/
theorem rnSub_atoms (n : Nat) : (rnSub n).atoms = ∅ :=
  embed_atoms (rn_atoms n)

/-! ## The infinite Rieger–Nishimura skeleton -/

/-- The RN ladder frame: worlds `ℕ`; `w` sees itself and every world
at least two earlier (so consecutive worlds are incomparable); `p`
true exactly at `0`. -/
@[reducible] def ladder : Skel where
  W := Nat
  le w v := v = w ∨ v + 2 ≤ w
  refl w := Or.inl rfl
  trans := by
    intro w v u h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega
  U := {w | w = 0}
  upU := by
    intro w v h hw
    have hw' : w = 0 := hw
    have h' : v = w ∨ v + 2 ≤ w := h
    show v = 0
    omega

theorem ladder_le {w v : Nat} : ladder.le w v ↔ (v = w ∨ v + 2 ≤ w) :=
  Iff.rfl

theorem ladder_U {w : Nat} : w ∈ ladder.U ↔ w = 0 := Iff.rfl

/-- **The ladder truth lemma** (closed form for the rung truth sets),
by one arithmetic induction:
`sat (rn (2k+1)) w ↔ w ≤ k` and
`sat (rn (2k+2)) w ↔ (w + 1 ≤ k ∨ w = k + 1)`. -/
theorem sat_rnP (k : Nat) :
    (∀ w : Nat, ladder.sat (rnP k).1 w ↔ w ≤ k) ∧
    (∀ w : Nat, ladder.sat (rnP k).2 w ↔ (w + 1 ≤ k ∨ w = k + 1)) := by
  induction k with
  | zero =>
      constructor
      · intro w
        show (pv = pv ∧ w ∈ ladder.U) ↔ w ≤ 0
        rw [ladder_U]
        constructor
        · rintro ⟨-, h⟩; omega
        · intro h; exact ⟨rfl, by omega⟩
      · intro w
        show (∀ v : Nat, ladder.le w v → (pv = pv ∧ v ∈ ladder.U) → False) ↔ _
        constructor
        · intro h
          by_contra hc
          have h0 : ladder.le w 0 := by rw [ladder_le]; omega
          exact h 0 h0 ⟨rfl, by rw [ladder_U]⟩
        · intro hw v hv hvp
          have hv0 : v = 0 := ladder_U.mp hvp.2
          rw [ladder_le] at hv
          omega
  | succ k ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hC : ∀ w : Nat,
          ladder.sat ((rnP k).1.or (rnP k).2) w ↔ w ≤ k + 1 := by
        intro w
        show (ladder.sat (rnP k).1 w ∨ ladder.sat (rnP k).2 w) ↔ _
        rw [ih1 w, ih2 w]
        omega
      constructor
      · intro w
        show ladder.sat ((rnP k).1.or (rnP k).2) w ↔ _
        exact hC w
      · intro w
        show (∀ v : Nat, ladder.le w v →
            ladder.sat ((rnP k).1.or (rnP k).2) v →
            ladder.sat (rnP k).1 v) ↔ _
        constructor
        · intro h
          by_contra hc
          have hle : ladder.le w (k + 1) := by rw [ladder_le]; omega
          have hsatC : ladder.sat ((rnP k).1.or (rnP k).2) (k + 1) :=
            (hC (k + 1)).mpr (by omega)
          have := (ih1 (k + 1)).mp (h (k + 1) hle hsatC)
          omega
        · intro hw v hv hvC
          rw [ladder_le] at hv
          have h1 : v ≤ k + 1 := (hC v).mp hvC
          exact (ih1 v).mpr (by omega)

theorem sat_rn_odd (k w : Nat) :
    ladder.sat (rn (2 * k + 1)) w ↔ w ≤ k := by
  rw [rn_odd_eq]; exact (sat_rnP k).1 w

theorem sat_rn_even (k w : Nat) :
    ladder.sat (rn (2 * k + 2)) w ↔ (w + 1 ≤ k ∨ w = k + 1) := by
  rw [rn_even_eq]; exact (sat_rnP k).2 w

theorem sat_rn_zero (w : Nat) : ¬ ladder.sat (rn 0) w := fun h => h

/-- Every index is `0`, odd, or even-positive. -/
theorem parity3 (n : Nat) :
    n = 0 ∨ (∃ a, n = 2 * a + 1) ∨ (∃ a, n = 2 * a + 2) := by
  rcases n with _ | m
  · exact Or.inl rfl
  · rcases Nat.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inr (Or.inl ⟨a, by omega⟩)
    · exact Or.inr (Or.inr ⟨a, by omega⟩)

/-- **Every pair of distinct rungs separates on the ladder**: for
`i < j` some world forces `rn j` and refutes `rn i`. -/
theorem ladder_sep {i j : Nat} (hij : i < j) :
    ∃ w : Nat, ladder.sat (rn j) w ∧ ¬ ladder.sat (rn i) w := by
  rcases parity3 j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · omega
  · -- j = 2b+1: witness depends on i
    rcases parity3 i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨0, (sat_rn_odd b 0).mpr (by omega), sat_rn_zero 0⟩
    · refine ⟨b, (sat_rn_odd b b).mpr (by omega), ?_⟩
      rw [sat_rn_odd]; omega
    · refine ⟨a, (sat_rn_odd b a).mpr (by omega), ?_⟩
      rw [sat_rn_even]; omega
  · -- j = 2b+2: witness b+1
    rcases parity3 i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨b + 1, (sat_rn_even b (b + 1)).mpr (by omega), sat_rn_zero _⟩
    · refine ⟨b + 1, (sat_rn_even b (b + 1)).mpr (by omega), ?_⟩
      rw [sat_rn_odd]; omega
    · refine ⟨b + 1, (sat_rn_even b (b + 1)).mpr (by omega), ?_⟩
      rw [sat_rn_even]; omega

/-! ## The headline theorems (T3): injectivity at every depth -/

/-- **The RN ladder embeds injectively into RN(PCLL,◯,{})**: distinct
rungs have non-interderivable `p ↦ ◯⊥` instances in PCLL — for ALL
indices, not merely an initial segment. -/
theorem rn_pairwise_pcll {i j : Nat} (h : i ≠ j) :
    ¬ InterdU (rnSub i) (rnSub j) := by
  rcases (by omega : i < j ∨ j < i) with hij | hji
  · obtain ⟨w, hj, hi⟩ := ladder_sep hij
    exact fun hI =>
      not_derivU_of_sep ladder (rn_boxFree j) (rn_boxFree i) hj hi hI.2
  · obtain ⟨w, hi, hj⟩ := ladder_sep hji
    exact fun hI =>
      not_derivU_of_sep ladder (rn_boxFree i) (rn_boxFree j) hi hj hI.1

/-- **The RN ladder embeds injectively into RN(PLL,◯,{}).** -/
theorem rn_pairwise_pll {i j : Nat} (h : i ≠ j) :
    ¬ Interd (rnSub i) (rnSub j) :=
  fun hI => rn_pairwise_pcll h (interdU_of_interd hI)

/-! ## Infinitude of the variable-free fragments -/

/-- No finite list of formulas covers the substituted rungs up to
PCLL-interderivability (pigeonhole over any putative list). -/
theorem no_finite_cover (L : List PLLFormula)
    (hL : ∀ n : Fin (L.length + 1), ∃ D ∈ L, InterdU (rnSub n.1) D) :
    False := by
  classical
  choose f hf hI using hL
  have hcard : L.toFinset.card
      < (Finset.univ : Finset (Fin (L.length + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Nat.lt_succ_of_le L.toFinset_card_le
  obtain ⟨x, -, y, -, hxy, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (fun n _ => List.mem_toFinset.mpr (hf n))
  have hIx : InterdU (rnSub x.1) (f y) := hfeq ▸ hI x
  exact rn_pairwise_pcll (fun hv => hxy (Fin.val_injective hv))
    (hIx.trans (hI y).symm)

/-- **RN(PCLL,◯,{}) is infinite**: no finite list represents the
variable-free formulas of PCLL up to interderivability. -/
theorem varfree_no_finite_cover_pcll :
    ¬ ∃ L : List PLLFormula,
        ∀ φ : PLLFormula, φ.atoms = ∅ → ∃ D ∈ L, InterdU φ D := by
  rintro ⟨L, hL⟩
  exact no_finite_cover L fun n => hL _ (rnSub_atoms n.1)

/-- **RN(PLL,◯,{}) is infinite**: no finite list represents the
variable-free formulas of PLL up to interderivability. -/
theorem varfree_no_finite_cover_pll :
    ¬ ∃ L : List PLLFormula,
        ∀ φ : PLLFormula, φ.atoms = ∅ → ∃ D ∈ L, Interd φ D := by
  rintro ⟨L, hL⟩
  refine varfree_no_finite_cover_pcll ⟨L, fun φ hφ => ?_⟩
  obtain ⟨D, hD, hI⟩ := hL φ hφ
  exact ⟨D, hD, interdU_of_interd hI⟩

/-- **Rank escape, PCLL**: for every crank bound `r` some substituted
rung is interderivable with NO variable-free formula of crank ≤ `r`
(via the per-rank finiteness `frag_reps_exist'`). -/
theorem rank_escape_pcll (r : Nat) :
    ∃ n : Nat, ∀ ψ : PLLFormula,
      ψ.atoms = ∅ → crank ψ ≤ r → ¬ InterdU (rnSub n) ψ := by
  by_contra hc
  push Not at hc
  obtain ⟨L, -, hL2⟩ := frag_reps_exist' ∅ r
  apply no_finite_cover L
  intro n
  obtain ⟨ψ, hψa, hψc, hψI⟩ := hc n.1
  obtain ⟨D, hD, d1, d2⟩ := hL2 ψ hψc (by simp [hψa])
  exact ⟨D, hD, hψI.trans (interdU_of_interd ⟨d1, d2⟩)⟩

/-- **Rank escape, PLL.** -/
theorem rank_escape_pll (r : Nat) :
    ∃ n : Nat, ∀ ψ : PLLFormula,
      ψ.atoms = ∅ → crank ψ ≤ r → ¬ Interd (rnSub n) ψ := by
  obtain ⟨n, hn⟩ := rank_escape_pcll r
  exact ⟨n, fun ψ h1 h2 hI => hn ψ h1 h2 (interdU_of_interd hI)⟩

/-! ## T4: substitution respects the connectives and the quotients -/

/-- Substitution respects derivability (via `substND`). -/
theorem deriv_substP {p : String} {χ A B : PLLFormula}
    (h : Deriv [A] B) : Deriv [substP p χ A] (substP p χ B) :=
  h.elim fun d => ⟨substND p χ d⟩

/-- **Substitution congruence**: the map `A ↦ A[p := χ]` is
well-defined on interderivability classes (and commutes with all
connectives syntactically, by definition of `substP`). -/
theorem interd_substP {p : String} {χ A B : PLLFormula}
    (h : Interd A B) : Interd (substP p χ A) (substP p χ B) :=
  ⟨h.1.elim fun d => ⟨substND p χ d⟩, h.2.elim fun d => ⟨substND p χ d⟩⟩

/-! ### The dictionary correspondence at the base of the ladder

The first four substituted rungs are SYNTACTICALLY the dictionary
representatives `q0 = ⊥`, `q2 = ◯⊥`, `q3 = ¬◯⊥`, `q4 = ◯⊥ ∨ ¬◯⊥`;
the fifth is interderivable with `q6 = ¬¬◯⊥` by the general IPC law
`((A ∨ ¬A) ⊃ A) ≡ ¬¬A`. -/

theorem rnSub_zero_eq : rnSub 0 = .falsePLL := rfl
theorem rnSub_one_eq : rnSub 1 = oBot := rfl
theorem rnSub_two_eq : rnSub 2 = notPLL oBot := rfl
theorem rnSub_three_eq : rnSub 3 = oBot.or (notPLL oBot) := rfl
theorem rnSub_four_eq : rnSub 4 = (oBot.or (notPLL oBot)).ifThen oBot := rfl

/-- `((A ∨ ¬A) ⊃ A) ≡ ¬¬A` in intuitionistic (hence lax) logic — hand
`LaxND` derivations. -/
theorem interd_peirce_dneg (A : PLLFormula) :
    Interd ((A.or (notPLL A)).ifThen A) (notPLL (notPLL A)) := by
  constructor
  · -- [(A ∨ ¬A) ⊃ A] ⊢ ¬¬A
    exact ⟨.impIntro (.impElim (.iden (.head _))
      (.impElim (.iden (.tail _ (.head _)))
        (.orIntro2 (.iden (.head _)))))⟩
  · -- [¬¬A] ⊢ (A ∨ ¬A) ⊃ A
    exact ⟨.impIntro (.orElim (.iden (.head _))
      (.iden (.head _))
      (.falsoElim A (.impElim (.iden (.tail _ (.tail _ (.head _))))
        (.iden (.head _)))))⟩

/-- `rnSub 4 ≡ ¬¬◯⊥` (the dictionary class `q6`). -/
theorem rnSub_four_interd : Interd (rnSub 4) (notPLL (notPLL oBot)) := by
  rw [rnSub_four_eq]
  exact interd_peirce_dneg oBot

/-! ### Crank growth along the substituted ladder -/

/-- The substituted rungs cost crank `k+2` (odd) and `k+3` (even) at
pair-level `k`: the ladder supplies two fresh classes per crank. -/
theorem crank_rnP_emb :
    ∀ k, crank (embed (rnP k).1) = k + 2 ∧ crank (embed (rnP k).2) = k + 3 := by
  intro k
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      constructor
      · show crank ((embed (rnP k).1).or (embed (rnP k).2)) = k + 3
        show max (crank (embed (rnP k).1)) (crank (embed (rnP k).2)) = k + 3
        rw [h1, h2]
        omega
      · show crank (((embed (rnP k).1).or (embed (rnP k).2)).ifThen
            (embed (rnP k).1)) = k + 4
        show max (max (crank (embed (rnP k).1)) (crank (embed (rnP k).2)))
            (crank (embed (rnP k).1)) + 1 = k + 4
        rw [h1, h2]
        omega

/-! ## The ladder ORDER: rung-to-rung derivability characterised

Beyond injectivity: derivability between substituted rungs — in BOTH
logics — is EXACTLY truth-set containment on the ladder
(`rnSub_deriv_iff`, `rnSub_derivU_iff`).  The positive direction is
generated by three one-line derivation schemas (`∨`-introductions and
a constant implication) chained along the ladder; the negative
direction is soundness through the transfer lemma.  Corollary
(`rnSub_derivU_iff_deriv`): PCLL is CONSERVATIVE over PLL for
rung-to-rung derivability — distribution adds no new arrows inside
the embedded ladder, so the embedding is an order-isomorphism onto
its image in both quotients, with the same image order. -/

/-- `rn (2k+1) ⊢ rn (2k+3)` (left `∨`-introduction). -/
theorem deriv_rnP_or1 (k : Nat) : Deriv [(rnP k).1] ((rnP (k + 1)).1) := by
  show Deriv [(rnP k).1] ((rnP k).1.or (rnP k).2)
  exact Deriv.orIntro1 (Deriv.iden (.head _))

/-- `rn (2k+2) ⊢ rn (2k+3)` (right `∨`-introduction). -/
theorem deriv_rnP_or2 (k : Nat) : Deriv [(rnP k).2] ((rnP (k + 1)).1) := by
  show Deriv [(rnP k).2] ((rnP k).1.or (rnP k).2)
  exact Deriv.orIntro2 (Deriv.iden (.head _))

/-- `rn (2k+1) ⊢ rn (2k+4)` (a constant implication). -/
theorem deriv_rnP_imp (k : Nat) : Deriv [(rnP k).1] ((rnP (k + 1)).2) := by
  show Deriv [(rnP k).1] (((rnP k).1.or (rnP k).2).ifThen (rnP k).1)
  exact Deriv.impIntro (Deriv.iden (.tail _ (.head _)))

theorem deriv_odd_mono {a b : Nat} (h : a ≤ b) :
    Deriv [(rnP a).1] ((rnP b).1) := by
  induction b with
  | zero =>
      obtain rfl : a = 0 := by omega
      exact Deriv.iden (.head _)
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le h with rfl | hlt
      · exact Deriv.iden (.head _)
      · exact (ih (by omega)).cutHead (deriv_rnP_or1 b)

theorem deriv_even_to_odd {a b : Nat} (h : a < b) :
    Deriv [(rnP a).2] ((rnP b).1) :=
  (deriv_rnP_or2 a).cutHead (deriv_odd_mono (by omega))

theorem deriv_odd_to_even {a b : Nat} (h : a < b) :
    Deriv [(rnP a).1] ((rnP b).2) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact (deriv_odd_mono (by omega : a ≤ c)).cutHead (deriv_rnP_imp c)

theorem deriv_even_to_even {a b : Nat} (h : a = b ∨ a + 2 ≤ b) :
    Deriv [(rnP a).2] ((rnP b).2) := by
  rcases h with rfl | h
  · exact Deriv.iden (.head _)
  · exact (deriv_rnP_or2 a).cutHead (deriv_odd_to_even (by omega : a + 1 < b))

/-- **Completeness of the generator chains**: ladder containment
yields derivability between the (unsubstituted) rungs. -/
theorem deriv_rn_of_sat_le {i j : Nat}
    (h : ∀ w, ladder.sat (rn i) w → ladder.sat (rn j) w) :
    Deriv [rn i] (rn j) := by
  rcases parity3 i with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · -- i = 0: ex falso
    exact Deriv.falsoElim _ (Deriv.iden (.head _))
  · -- i = 2a+1
    rcases parity3 j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact absurd (h a ((sat_rn_odd a a).mpr (by omega))) (sat_rn_zero a)
    · have hab : a ≤ b :=
        (sat_rn_odd b a).mp (h a ((sat_rn_odd a a).mpr (by omega)))
      rw [rn_odd_eq a, rn_odd_eq b]
      exact deriv_odd_mono hab
    · have h1 := (sat_rn_even b a).mp (h a ((sat_rn_odd a a).mpr (by omega)))
      have hb : a < b := by
        rcases h1 with h1 | h1
        · omega
        · exfalso
          have h2 :=
            (sat_rn_even b b).mp (h b ((sat_rn_odd a b).mpr (by omega)))
          omega
      rw [rn_odd_eq a, rn_even_eq b]
      exact deriv_odd_to_even hb
  · -- i = 2a+2
    rcases parity3 j with rfl | ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact absurd (h (a + 1) ((sat_rn_even a (a + 1)).mpr (by omega)))
        (sat_rn_zero _)
    · have hab : a + 1 ≤ b :=
        (sat_rn_odd b (a + 1)).mp
          (h (a + 1) ((sat_rn_even a (a + 1)).mpr (by omega)))
      rw [rn_even_eq a, rn_odd_eq b]
      exact deriv_even_to_odd (by omega)
    · have h1 := (sat_rn_even b (a + 1)).mp
        (h (a + 1) ((sat_rn_even a (a + 1)).mpr (by omega)))
      rw [rn_even_eq a, rn_even_eq b]
      exact deriv_even_to_even (by omega)

/-- **The image order in PLL is exactly ladder containment.** -/
theorem rnSub_deriv_iff (i j : Nat) :
    Deriv [rnSub i] (rnSub j) ↔
      (∀ w, ladder.sat (rn i) w → ladder.sat (rn j) w) := by
  constructor
  · rintro ⟨d⟩ w hw
    refine (ladder.transfer (rn_boxFree j) w).mp ?_
    refine soundness d ladder.cm (some w) ?_
    intro ψ hψ
    rw [List.mem_singleton] at hψ
    subst hψ
    exact (ladder.transfer (rn_boxFree i) w).mpr hw
  · intro h
    exact deriv_substP (deriv_rn_of_sat_le h)

/-- **The image order in PCLL is exactly ladder containment** — the
same order. -/
theorem rnSub_derivU_iff (i j : Nat) :
    DerivU [rnSub i] (rnSub j) ↔
      (∀ w, ladder.sat (rn i) w → ladder.sat (rn j) w) := by
  constructor
  · intro d w hw
    refine (ladder.transfer (rn_boxFree j) w).mp ?_
    refine derivU_sound d ladder.cm_confluent (some w) ?_
    intro ψ hψ
    rw [List.mem_singleton] at hψ
    subst hψ
    exact (ladder.transfer (rn_boxFree i) w).mpr hw
  · intro h
    exact ((rnSub_deriv_iff i j).mpr h).elim fun d => .of_nd d

/-- **Conservativity on the embedded ladder**: distribution adds no
new rung-to-rung derivability — the coarsening map is an
order-ISOMORPHISM from the PLL ladder image onto the PCLL ladder
image. -/
theorem rnSub_derivU_iff_deriv (i j : Nat) :
    DerivU [rnSub i] (rnSub j) ↔ Deriv [rnSub i] (rnSub j) :=
  (rnSub_derivU_iff i j).trans (rnSub_deriv_iff i j).symm

/-! ## Axiom audits -/

/-- info: 'PLLND.RNEmbed.Skel.transfer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Skel.transfer

/-- info: 'PLLND.RNEmbed.Skel.cm_confluent' does not depend on any axioms -/
#guard_msgs in
#print axioms Skel.cm_confluent

/-- info: 'PLLND.RNEmbed.rn_transfer_pcll' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rn_transfer_pcll

/-- info: 'PLLND.RNEmbed.rn_transfer_pll' depends on axioms: [propext] -/
#guard_msgs in
#print axioms rn_transfer_pll

/--
info: 'PLLND.RNEmbed.rn_pairwise_pcll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rn_pairwise_pcll

/--
info: 'PLLND.RNEmbed.rn_pairwise_pll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rn_pairwise_pll

/--
info: 'PLLND.RNEmbed.varfree_no_finite_cover_pcll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms varfree_no_finite_cover_pcll

/--
info: 'PLLND.RNEmbed.varfree_no_finite_cover_pll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms varfree_no_finite_cover_pll

/--
info: 'PLLND.RNEmbed.rank_escape_pcll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rank_escape_pcll

/--
info: 'PLLND.RNEmbed.rank_escape_pll' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rank_escape_pll

/-- info: 'PLLND.RNEmbed.rnSub_four_interd' does not depend on any axioms -/
#guard_msgs in
#print axioms rnSub_four_interd

/-- info: 'PLLND.RNEmbed.interd_substP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms interd_substP

/--
info: 'PLLND.RNEmbed.rnSub_deriv_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnSub_deriv_iff

/--
info: 'PLLND.RNEmbed.rnSub_derivU_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnSub_derivU_iff

/--
info: 'PLLND.RNEmbed.rnSub_derivU_iff_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rnSub_derivU_iff_deriv

end RNEmbed
end PLLND
