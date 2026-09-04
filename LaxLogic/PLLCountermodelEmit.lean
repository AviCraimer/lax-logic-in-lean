import LaxLogic.PLLG4Term
import LaxLogic.PLLKripke

/-!
# Executable countermodels: a verified checker and an emitter

`PLLCountermodel.lean` proves the *specification*: a formula is unprovable
iff some finite constraint model refutes it.  This file makes the witness
side of that biconditional executable, in the same trust discipline as
`PLLG4Term.lean` (untrusted search, kernel-checked artefact):

* `FinCM` — a finite constraint model as printable data (worlds `0..n-1`,
  relations as pair lists, valuation as `(world, atom)` pairs);
* `FinCM.forceB` — forcing as a computable `Bool`, by structural recursion
  on the formula with the world quantifiers as finite folds;
* `FinCM.WellFormed` — the frame conditions of `ConstraintModel`
  (transitivity, `Rₘ ⊆ Rᵢ`, heredity), as a *decidable* proposition
  (reflexivity of both relations and fullness of the valuation on fallible
  worlds are built into the derived relations, so they need no check);
* `FinCM.toModel` — a well-formed `FinCM` is a genuine `ConstraintModel`;
* `FinCM.force_iff` — the reflection lemma: `forceB` computes `force`;
* `not_provable_of_check` — **the certificate theorem**: if the computable
  check passes (well-formed, all of `Γ` forced at `w`, `C` not forced at
  `w`), then `Γ ⊢ C` is underivable, by soundness.

The *emitter* (second half of the file) is untrusted `partial` code that
proposes a candidate countermodel from the failed search: worlds are pairs
`(T, P)` of a prime `G4c`-closed theory `T` over the subformula closure
and a coherent *refutation promise* set `P` (subformulas pledged false at
every `Rₘ`-successor — the syntactic mirror of the second filtration
component `Fmset`, `PLLFiniteModel.lean`), with `Rᵢ` = inclusion on `T`
and `Rₘ` = inclusion on both components.  Every candidate is run through
the verified checker before being returned, so a wrong guess can only
produce `none`, never a wrong certificate.
-/

open PLLFormula

namespace PLLND

/-- A finite constraint model as printable, decidable data.  Worlds are
`0, …, n-1`; `ri`/`rm` list the non-reflexive relation pairs; `fall` lists
the fallible worlds; `val` lists the true `(world, atom)` pairs. -/
structure FinCM where
  n : Nat
  ri : List (Nat × Nat)
  rm : List (Nat × Nat)
  fall : List Nat
  val : List (Nat × String)
  deriving Repr, DecidableEq, Inhabited

namespace FinCM

/-- `Rᵢ` test, reflexive closure built in. -/
def riB (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.ri) || decide (w = v)

/-- `Rₘ` test, reflexive closure built in. -/
def rmB (M : FinCM) (w v : Nat) : Bool := decide ((w, v) ∈ M.rm) || decide (w = v)

/-- Fallibility test. -/
def fallB (M : FinCM) (w : Nat) : Bool := decide (w ∈ M.fall)

/-- Valuation test; fallible worlds validate every atom by construction. -/
def valB (M : FinCM) (w : Nat) (a : String) : Bool :=
  decide ((w, a) ∈ M.val) || M.fallB w

/-- **Computable forcing**: structural recursion on the formula, world
quantifiers as folds over `List.range n`. -/
def forceB (M : FinCM) : Nat → PLLFormula → Bool
  | w, .prop a => M.valB w a
  | w, .falsePLL => M.fallB w
  | w, .and φ ψ => M.forceB w φ && M.forceB w ψ
  | w, .or φ ψ => M.forceB w φ || M.forceB w ψ
  | w, .ifThen φ ψ =>
      (List.range M.n).all fun v =>
        !(M.riB w v) || !(M.forceB v φ) || M.forceB v ψ
  | w, .somehow φ =>
      (List.range M.n).all fun v =>
        !(M.riB w v) ||
        (List.range M.n).any fun u => M.rmB v u && M.forceB u φ

/-- The frame conditions of `ConstraintModel`, decidably.  (Reflexivity and
`full_F` hold by construction of `riB`/`rmB`/`valB`.) -/
def WellFormed (M : FinCM) : Prop :=
  (∀ w, w < M.n → ∀ v, v < M.n → ∀ u, u < M.n →
    M.riB w v = true → M.riB v u = true → M.riB w u = true) ∧
  (∀ w, w < M.n → ∀ v, v < M.n → ∀ u, u < M.n →
    M.rmB w v = true → M.rmB v u = true → M.rmB w u = true) ∧
  (∀ w, w < M.n → ∀ v, v < M.n → M.rmB w v = true → M.riB w v = true) ∧
  (∀ w, w < M.n → ∀ v, v < M.n → M.riB w v = true →
    M.fallB w = true → M.fallB v = true) ∧
  (∀ p ∈ M.val, ∀ v, v < M.n → M.riB p.1 v = true → M.valB v p.2 = true)

/-- The frame conditions as a computable check. -/
def wellB (M : FinCM) : Bool :=
  ((List.range M.n).all fun w => (List.range M.n).all fun v =>
    (List.range M.n).all fun u =>
      !(M.riB w v) || !(M.riB v u) || M.riB w u) &&
  ((List.range M.n).all fun w => (List.range M.n).all fun v =>
    (List.range M.n).all fun u =>
      !(M.rmB w v) || !(M.rmB v u) || M.rmB w u) &&
  ((List.range M.n).all fun w => (List.range M.n).all fun v =>
    !(M.rmB w v) || M.riB w v) &&
  ((List.range M.n).all fun w => (List.range M.n).all fun v =>
    !(M.riB w v) || !(M.fallB w) || M.fallB v) &&
  (M.val.all fun p => (List.range M.n).all fun v =>
    !(M.riB p.1 v) || M.valB v p.2)

theorem wellFormed_of_wellB {M : FinCM} (h : M.wellB = true) :
    M.WellFormed := by
  simp only [wellB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv u hu a b
    simpa [a, b] using h₁ w hw v hv u hu
  · intro w hw v hv u hu a b
    simpa [a, b] using h₂ w hw v hv u hu
  · intro w hw v hv a
    simpa [a] using h₃ w hw v hv
  · intro w hw v hv a b
    simpa [a, b] using h₄ w hw v hv
  · intro p hp v hv a
    simpa [a] using h₅ p hp v hv

/-- A well-formed `FinCM` is a genuine Fairtlough–Mendler constraint model
on `Fin n`.  (Reducible so that concrete instances expose `W = Fin n` and the
relation/valuation fields to `simp` and `decide`.) -/
@[reducible] def toModel (M : FinCM) (h : M.WellFormed) : ConstraintModel where
  W := Fin M.n
  Ri w v := M.riB w.1 v.1 = true
  Rm w v := M.rmB w.1 v.1 = true
  F := {w | M.fallB w.1 = true}
  V a := {w | M.valB w.1 a = true}
  refl_i w := by simp [riB]
  trans_i {w v u} h₁ h₂ := h.1 _ w.2 _ v.2 _ u.2 h₁ h₂
  refl_m w := by simp [rmB]
  trans_m {w v u} h₁ h₂ := h.2.1 _ w.2 _ v.2 _ u.2 h₁ h₂
  sub_mi {w v} h₁ := h.2.2.1 _ w.2 _ v.2 h₁
  hered_F {w v} h₁ hw := h.2.2.2.1 _ w.2 _ v.2 h₁ hw
  hered_V {a w v} h₁ hw := by
    rcases Bool.or_eq_true .. |>.mp hw with hmem | hf
    · exact h.2.2.2.2 (w.1, a) (of_decide_eq_true hmem) _ v.2 h₁
    · have hv := h.2.2.2.1 _ w.2 _ v.2 h₁ hf
      simp [valB, hv]
  full_F {a w} hw := by simp [valB, Set.mem_setOf_eq.mp hw]

/-- **Reflection**: the computable `forceB` decides genuine forcing in the
induced model. -/
theorem force_iff (M : FinCM) (h : M.WellFormed) :
    ∀ (φ : PLLFormula) (w : Fin M.n),
      (M.toModel h).force w φ ↔ M.forceB w.1 φ = true := by
  intro φ
  induction φ with
  | prop a => intro w; exact Iff.rfl
  | falsePLL => intro w; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro w
      simp only [ConstraintModel.force, forceB, Bool.and_eq_true]
      exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ =>
      intro w
      simp only [ConstraintModel.force, forceB, Bool.or_eq_true]
      exact or_congr (ihφ w) (ihψ w)
  | ifThen φ ψ ihφ ihψ =>
      intro w
      simp only [ConstraintModel.force, forceB, List.all_eq_true,
        List.mem_range]
      constructor
      · intro H v hv
        by_cases hri : M.riB w.1 v = true
        · by_cases hφ : M.forceB v φ = true
          · have := (ihψ ⟨v, hv⟩).mp (H ⟨v, hv⟩ hri ((ihφ ⟨v, hv⟩).mpr hφ))
            simp [this]
          · simp [hφ]
        · simp [hri]
      · intro H v hri hφ
        have := H v.1 v.2
        rw [hri, (ihφ v).mp hφ] at this
        simp only [Bool.not_true, Bool.false_or] at this
        exact (ihψ v).mpr this
  | somehow φ ih =>
      intro w
      simp only [ConstraintModel.force, forceB, List.all_eq_true,
        List.mem_range]
      constructor
      · intro H v hv
        by_cases hri : M.riB w.1 v = true
        · obtain ⟨u, hmu, hu⟩ := H ⟨v, hv⟩ hri
          have hmu' : M.rmB v u.1 = true := hmu
          have : (List.range M.n).any
              (fun u => M.rmB v u && M.forceB u φ) = true := by
            refine List.any_eq_true.mpr ⟨u.1, List.mem_range.mpr u.2, ?_⟩
            simp [hmu', (ih u).mp hu]
          simp [this]
        · simp [hri]
      · intro H v hri
        have := H v.1 v.2
        rw [hri] at this
        simp only [Bool.not_true, Bool.false_or, List.any_eq_true,
          List.mem_range] at this
        obtain ⟨u, hu, hb⟩ := this
        rw [Bool.and_eq_true] at hb
        exact ⟨⟨u, hu⟩, hb.1, (ih ⟨u, hu⟩).mpr hb.2⟩

theorem wellB_of_wellFormed {M : FinCM} (h : M.WellFormed) :
    M.wellB = true := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  simp only [wellB, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro w hw v hv u hu
    by_cases ha : M.riB w v = true
    · by_cases hb : M.riB v u = true
      · simp [h₁ _ hw _ hv _ hu ha hb]
      · simp [hb]
    · simp [ha]
  · intro w hw v hv u hu
    by_cases ha : M.rmB w v = true
    · by_cases hb : M.rmB v u = true
      · simp [h₂ _ hw _ hv _ hu ha hb]
      · simp [hb]
    · simp [ha]
  · intro w hw v hv
    by_cases ha : M.rmB w v = true
    · simp [h₃ _ hw _ hv ha]
    · simp [ha]
  · intro w hw v hv
    by_cases ha : M.riB w v = true
    · by_cases hb : M.fallB w = true
      · simp [h₄ _ hw _ hv ha hb]
      · simp [hb]
    · simp [ha]
  · intro p hp v hv
    by_cases ha : M.riB p.1 v = true
    · simp [h₅ p hp _ hv ha]
    · simp [ha]

/-- The computable countermodel check: well-formed, the world is in range,
all hypotheses forced there, the conclusion not. -/
def checkB (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula) :
    Bool :=
  M.wellB && decide (w < M.n) && Γ.all (M.forceB w) && !(M.forceB w C)

/-- Introduction rule for the check: a genuine refutation in the induced
model certifies. -/
theorem checkB_intro {M : FinCM} (h : M.WellFormed) {w : Nat} (hlt : w < M.n)
    {Γ : List PLLFormula} {C : PLLFormula}
    (hΓ : ∀ ψ ∈ Γ, (M.toModel h).force ⟨w, hlt⟩ ψ)
    (hC : ¬ (M.toModel h).force ⟨w, hlt⟩ C) :
    checkB M w Γ C = true := by
  simp only [checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨wellB_of_wellFormed h, hlt⟩,
    fun ψ hψ => (M.force_iff h ψ ⟨w, hlt⟩).mp (hΓ ψ hψ)⟩, ?_⟩
  by_cases hb : M.forceB w C = true
  · exact absurd ((M.force_iff h C ⟨w, hlt⟩).mpr hb) hC
  · exact Bool.not_eq_true _ |>.mp hb

/-- **The certificate theorem**: a checked finite countermodel refutes
derivability, by soundness.  Everything upstream of `soundness` here is
computation, so concrete instances discharge by `decide`. -/
theorem not_provable_of_check {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {C : PLLFormula}
    (h : checkB M w Γ C = true) : ¬ Nonempty (LaxND Γ C) := by
  simp only [checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := h
  have hwf := wellFormed_of_wellB hwb
  rintro ⟨p⟩
  have hval := soundness p (M.toModel hwf) ⟨w, hlt⟩
    (fun ψ hψ => (M.force_iff hwf ψ ⟨w, hlt⟩).mpr (hΓ ψ hψ))
  rw [M.force_iff hwf C ⟨w, hlt⟩, hC] at hval
  exact Bool.false_ne_true hval

end FinCM

/-! ## The emitter (untrusted; every candidate passes through `checkB`)

Worlds are pairs `(T, P)`: `T` a prime, `G4c`-deductively-closed subset of the
subformula closure (the *beliefs held*), `P` a coherent set of *refutation
promises* (subformulas pledged false at every `Rₘ`-successor — the syntactic
mirror of `Fmset` in the filtration).  `Rᵢ` is inclusion on `T`; `Rₘ` is
inclusion on both components, so a promise once made binds all constraint
successors — this is what stops the fallible world from trivialising `◯`. -/

namespace CounterEmit

/-- Subformulas (with the formula itself). -/
def subs : PLLFormula → List PLLFormula
  | .prop a => [.prop a]
  | .falsePLL => [.falsePLL]
  | .and A B => .and A B :: (subs A ++ subs B)
  | .or A B => .or A B :: (subs A ++ subs B)
  | .ifThen A B => .ifThen A B :: (subs A ++ subs B)
  | .somehow A => .somehow A :: subs A

/-- Subformula closure of the sequent, `⊥` always included. -/
def closureOf (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  canon (.falsePLL :: (C :: Γ).flatMap subs)

/-- `S` is deductively closed within the closure (oracle: `G4cTm.find`). -/
partial def closedB (cl S : List PLLFormula) : Bool :=
  cl.all fun φ => !(G4cTm.find S φ).isSome || decide (φ ∈ S)

/-- `S` has the disjunction property. -/
def primeB (S : List PLLFormula) : Bool :=
  S.all fun φ => match φ with
    | .or A B => decide (A ∈ S) || decide (B ∈ S)
    | _ => true

/-- Candidate belief states: prime closed subsets of the closure. -/
partial def statesOf (cl : List PLLFormula) : List (List PLLFormula) :=
  cl.sublists.filter fun S => closedB cl S && primeB S

/-- One step of the promise closure: if both disjuncts (a conjunct, the body
of a `◯`) are refuted at every constraint successor, so is the disjunction
(conjunction, `◯`-formula); and a refuted `◯A` refutes `A`. -/
def closeFStep (cl P : List PLLFormula) : List PLLFormula :=
  canon (P ++ cl.filter fun φ =>
    (match φ with
      | .or A B => decide (A ∈ P) && decide (B ∈ P)
      | .and A B => decide (A ∈ P) || decide (B ∈ P)
      | .somehow A => decide (A ∈ P)
      | _ => false)
    || decide (PLLFormula.somehow φ ∈ P))

/-- Promise closure (iterated to a fixpoint within the closure). -/
def closeF (cl P : List PLLFormula) : List PLLFormula :=
  (List.range cl.length).foldl (fun acc _ => closeFStep cl acc) P

/-- Coherence of promises `P` with beliefs `T`: nothing both believed and
promised-refuted; no implication promises (not needed, not sound to guess);
no `◯`-belief whose body is promised away. -/
def cohB (T P : List PLLFormula) : Bool :=
  P.all (fun φ => !(decide (φ ∈ T))) &&
  P.all (fun φ => match φ with | .ifThen _ _ => false | _ => true) &&
  T.all (fun φ => match φ with
    | .somehow A => !(decide (A ∈ P))
    | _ => true)

/-- Promise candidates for a state: closures of atom sets, kept if coherent. -/
def promisesOf (cl T : List PLLFormula) : List (List PLLFormula) :=
  (((cl.filter fun φ => match φ with
      | .prop _ => true | _ => false).sublists).map
    (closeF cl)).filter (cohB T)

/-- List inclusion, executably. -/
def subB (S T : List PLLFormula) : Bool := S.all (decide <| · ∈ T)

/-- Assemble the finite model from the `(T, P)` worlds. -/
partial def build (Γ : List PLLFormula) (C : PLLFormula) :
    FinCM × List (List PLLFormula × List PLLFormula) :=
  let cl := closureOf Γ C
  let ws := (statesOf cl).flatMap fun T =>
    (promisesOf cl T).map fun P => (T, P)
  let idx := List.range ws.length
  let get : Nat → List PLLFormula × List PLLFormula := fun i => ws[i]!
  ({ n := ws.length
     ri := idx.flatMap fun i => idx.filterMap fun j =>
       if subB (get i).1 (get j).1 then some (i, j) else none
     rm := idx.flatMap fun i => idx.filterMap fun j =>
       if subB (get i).1 (get j).1 && subB (get i).2 (get j).2 then
         some (i, j) else none
     fall := idx.filter fun i => decide (PLLFormula.falsePLL ∈ (get i).1)
     val := idx.flatMap fun i => (get i).1.filterMap fun φ =>
       match φ with | .prop a => some (i, a) | _ => none }, ws)

/-- **The countermodel emitter.**  Returns a finite model and a refuting
world for underivable sequents — every candidate is validated by the
*verified* `checkB` before being returned, so a wrong guess can only yield
`none`, never a wrong certificate.

The first thing it does is *run proof search*: `build` is exponential in
the closure, so it is worth a search to avoid building the model of a
provable sequent.  Two parameters control that search, and both exist to
stop this stage from being the unbounded one.

* `budget` caps it at that many visited sequents.  A **cutoff** returns
  `none`: the sequent might be provable, and building the model of a
  sequent that might be provable is exactly the work the budget was set to
  avoid.  So under a budget this emitter answers only about sequents whose
  search space it could exhaust — which is what `Search.Config.findBudget`
  promises everywhere else.
* `precheck := false` skips the search altogether.  Pass it when the
  caller has *already* run a search to exhaustion and found nothing, as
  `Search.settleWhy` has by the time it reaches this stage; the saving is
  one whole search on the expensive case. -/
partial def emit (Γ : List PLLFormula) (C : PLLFormula)
    (budget : Option Nat := none) (precheck : Bool := true) :
    Option (FinCM × Nat) :=
  let stop :=
    if !precheck then false
    else match budget with
      | none   => (G4cTm.find Γ C).isSome
      | some b => match G4cTm.findBounded b Γ C with
        | (some _, _) => true   -- provable: no countermodel exists
        | (none, 0)   => true   -- cut off: refuse to pay for `build`
        | (none, _)   => false  -- space exhausted, nothing found
  if stop then none
  else
    let (M, _) := build Γ C
    (List.range M.n).findSome? fun w =>
      if FinCM.checkB M w Γ C then some (M, w) else none

/-- Restrict a model to the listed worlds (renumbered in list order).
Every frame condition is universally quantified over the worlds present,
so any restriction of a well-formed model is well-formed; forcing, of
course, changes — which is why every use below is checker-gated. -/
def restrict (M : FinCM) (keep : List Nat) : FinCM :=
  let f := fun i => keep.idxOf i
  { n := keep.length
    ri := M.ri.filterMap fun p =>
      if p.1 ∈ keep ∧ p.2 ∈ keep then some (f p.1, f p.2) else none
    rm := M.rm.filterMap fun p =>
      if p.1 ∈ keep ∧ p.2 ∈ keep then some (f p.1, f p.2) else none
    fall := M.fall.filterMap fun i =>
      if i ∈ keep then some (f i) else none
    val := M.val.filterMap fun p =>
      if p.1 ∈ keep then some (f p.1, p.2) else none }

/-- **Greedy countermodel minimisation**: repeatedly remove any single
world whose removal leaves the checker satisfied, until none can go.
Untrusted, checker-gated at every step — the result is certified by the
same `checkB` as the input.

`accept` is an extra property the intermediate models must keep, the same
untrusted pre-filter as `Search.Config.accept`.  It matters when the
property is *not* inherited by submodels: mutual confluence (`RNC.confB`)
is the case in hand — deleting a world can destroy it — so a PCLL search
must pass `confB` here, or minimisation would hand back a model that no
longer refutes PCLL.  The default keeps every model. -/
partial def minimise (M : FinCM) (w : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) (accept : FinCM → Bool := fun _ => true) : FinCM × Nat :=
  let step := (List.range M.n).filter (· ≠ w) |>.findSome? fun j =>
    let keep := (List.range M.n).filter (· ≠ j)
    let M' := restrict M keep
    let w' := keep.idxOf w
    if accept M' && FinCM.checkB M' w' Γ C then some (M', w') else none
  match step with
  | some (M', w') => minimise M' w' Γ C accept
  | none => (M, w)

/-- One sweep of checker-gated attribute deletions: each fallible flag,
then each valuation pair, then each non-reflexive `ri`/`rm` pair is
removed if `checkB` still certifies the sequent afterwards.  Deleting a
relation pair can break transitivity or `Rₘ ⊆ Rᵢ`; the `wellB` conjunct
of `checkB` rejects exactly those edits, so gating on the full check
suffices. -/
def cleanStep (M : FinCM) (w : Nat) (Γ : List PLLFormula) (C : PLLFormula)
    (accept : FinCM → Bool := fun _ => true) : FinCM :=
  let ok : FinCM → Bool := fun M' => accept M' && FinCM.checkB M' w Γ C
  let M₁ := M.fall.foldl (init := M) fun acc i =>
    let cand := { acc with fall := acc.fall.erase i }
    if ok cand then cand else acc
  let M₂ := M₁.val.foldl (init := M₁) fun acc p =>
    let cand := { acc with val := acc.val.erase p }
    if ok cand then cand else acc
  let M₃ := M₂.ri.foldl (init := M₂) fun acc p =>
    if p.1 = p.2 then acc
    else
      let cand := { acc with ri := acc.ri.erase p }
      if ok cand then cand else acc
  M₃.rm.foldl (init := M₃) fun acc p =>
    if p.1 = p.2 then acc
    else
      let cand := { acc with rm := acc.rm.erase p }
      if ok cand then cand else acc

/-- **Checker-gated attribute cleaning**: `minimise` deletes worlds but
never edits the survivors' attributes, so a minimised model can carry
vestigial data — a fallible flag no longer doing any work, a valuation
pair or relation pair the refutation never uses.  `clean` sweeps the
attributes with `cleanStep` and iterates to a fixpoint.  Worlds are never
deleted or renumbered, so the refuting world `w` passes through
unchanged.  Untrusted and greedy, like `minimise`: every step is gated by
the verified `checkB`, so a wrong edit can only be rejected, never
mis-certify. -/
partial def clean (M : FinCM) (w : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) (accept : FinCM → Bool := fun _ => true) : FinCM × Nat :=
  let M' := cleanStep M w Γ C accept
  if M' = M then (M, w) else clean M' w Γ C accept

/-- **The countermodel simplifier**: `minimise` and `clean` run
alternately to a joint fixpoint.

Neither pass subsumes the other, and each can re-enable the other:
deleting a world can leave a relation pair with nothing to do, and
deleting a relation pair can leave a world unreachable, so a single
`minimise`-then-`clean` is not in general a fixpoint of either.  The loop
terminates because every round that changes anything deletes at least one
world, pair or flag.

`accept` is threaded through both passes; see `minimise`.  Untrusted and
greedy like its two components: every intermediate model is gated by the
verified `FinCM.checkB`, so the result is certified exactly as the input
was, and a wrong edit can only be rejected. -/
partial def simplify (M : FinCM) (w : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) (accept : FinCM → Bool := fun _ => true) : FinCM × Nat :=
  let (M₁, w₁) := minimise M w Γ C accept
  let (M₂, w₂) := clean M₁ w₁ Γ C accept
  if M₂ = M && w₂ = w then (M₂, w₂) else simplify M₂ w₂ Γ C accept

/-- Semantic profile of a world: which of the given formulas it forces —
for reading minimised models, whose belief-set provenance is gone. -/
def profile (M : FinCM) (φs : List PLLFormula) (w : Nat) :
    List PLLFormula :=
  φs.filter fun φ => M.forceB w φ

/-- Emit and then minimise: the systematic countermodel, cut down to a
presentable one by checker-gated deletion. -/
partial def emitMin (Γ : List PLLFormula) (C : PLLFormula) :
    Option (FinCM × Nat) :=
  (emit Γ C).map fun (M, w) => minimise M w Γ C

/-- Emit, minimise, then clean: the systematic countermodel cut down by
checker-gated world deletion, then stripped of vestigial attributes by
checker-gated edits.  The result is certified by the same `checkB` as
every intermediate model.

One pass of each, in that order — `simplify` is the version that alternates
the two to a fixpoint, and is what `Search.Config.simplify` runs.  The two
agree on every model in this file; they can differ when a cleaned edge
leaves a world with nothing to do. -/
partial def emitMinClean (Γ : List PLLFormula) (C : PLLFormula) :
    Option (FinCM × Nat) :=
  (emit Γ C).map fun (M, w) =>
    let (M', w') := minimise M w Γ C
    clean M' w' Γ C

/-- Human-readable formula rendering. -/
def fmt : PLLFormula → String
  | .prop a => a
  | .falsePLL => "⊥"
  | .and A B => s!"({fmt A} ∧ {fmt B})"
  | .or A B => s!"({fmt A} ∨ {fmt B})"
  | .ifThen A B => s!"({fmt A} → {fmt B})"
  | .somehow A => s!"◯{fmt A}"

/-- Human-readable countermodel report: the refuting world and, for each
world, its believed formulas and standing refutation promises. -/
partial def describe (Γ : List PLLFormula) (C : PLLFormula) : String :=
  match emit Γ C with
  | none => "no countermodel (sequent is provable, or emission failed)"
  | some (M, w) =>
    let (_, ws) := build Γ C
    let lines := (List.range ws.length).map fun i =>
      let (T, P) := ws[i]!
      s!"  w{i}: believes {(T.map fmt)}" ++
        (if P.isEmpty then "" else s!", promises-false {(P.map fmt)}")
    s!"refuting world: w{w}  ({M.n} worlds)\n" ++
      String.intercalate "\n" lines

end CounterEmit

/-! ## Smoke tests -/

section Tests
open CounterEmit

-- ⊬ p : refutable (expect a small model).
/-- info: some (4, 0) -/
#guard_msgs in
#eval (emit [] (prop "p")).map fun (M, w) => (M.n, w)

-- ◯p ⊬ p : the modality admits no escape.
/-- info: some (5, 2) -/
#guard_msgs in
#eval (emit [(prop "p").somehow] (prop "p")).map fun (M, w) => (M.n, w)

-- ⊬ ¬◯⊥ : inconsistency under ◯ is quarantined, not refutable.
/-- info: some (4, 0) -/
#guard_msgs in
#eval (emit [] ((falsePLL.somehow).ifThen falsePLL)).map fun (M, w) => (M.n, w)

-- ◯(p∨q) ⊬ ◯p ∨ ◯q : the ∨-distribution countermodel (the split model).
/-- info: some (20, 4) -/
#guard_msgs in
#eval (emit [((prop "p").or (prop "q")).somehow]
  (((prop "p").somehow).or ((prop "q").somehow))).map fun (M, w) => (M.n, w)

-- …and minimisation recovers the three-world split model of F&M Fig. 3.
/-- info: some { n := 3,
  ri := [(0, 0), (0, 1), (0, 2), (1, 1), (2, 2)],
  rm := [(0, 0), (0, 1), (0, 2), (1, 1), (2, 2)],
  fall := [],
  val := [(1, "p"), (2, "q")] } -/
#guard_msgs in
#eval (emitMin [((prop "p").or (prop "q")).somehow]
  (((prop "p").somehow).or ((prop "q").somehow))).map (·.1)

-- Cleaning strips a vestigial modal pair even from the split model: the
-- constraint arrow 0 → 1 does no work (`◯(p∨q)` at 0 is witnessed through
-- 0 → 2, and world 1 answers for itself by reflexivity), so the checker
-- confirms its removal.  Everything else survives as pinned above.
/-- info: some { n := 3,
  ri := [(0, 0), (0, 1), (0, 2), (1, 1), (2, 2)],
  rm := [(0, 0), (0, 2), (1, 1), (2, 2)],
  fall := [],
  val := [(1, "p"), (2, "q")] } -/
#guard_msgs in
#eval (emitMinClean [((prop "p").or (prop "q")).somehow]
  (((prop "p").somehow).or ((prop "q").somehow))).map (·.1)

-- ◯p ⊬ p, cleaned: minimisation leaves the top world flagged fallible (a
-- leftover of the fallible ceiling of the emitted model), but the
-- valuation pair `(1, p)` already witnesses `◯p` at the root, so cleaning
-- deletes the flag — two worlds, `p` at the top, no fallible world at all.
/-- info: some { n := 2, ri := [(0, 0), (0, 1), (1, 1)], rm := [(0, 0), (0, 1), (1, 1)], fall := [], val := [(1, "p")] } -/
#guard_msgs in
#eval (emitMinClean [(prop "p").somehow] (prop "p")).map (·.1)

-- p ⊢ ◯p is provable: the emitter must return none.
/-- info: none -/
#guard_msgs in
#eval (emit [prop "p"] (prop "p").somehow).map fun (M, w) => (M.n, w)

-- The readable report for the ∨-distribution refutation.
#eval IO.println (describe [((prop "p").or (prop "q")).somehow]
  (((prop "p").somehow).or ((prop "q").somehow)))

end Tests

/-! ## A pinned certificate: the emitted model as a kernel-checked theorem

The model below is the emitter's output for `◯p ⊢ p` (worlds: `w0` = no
beliefs, `w1` = no beliefs with the standing promise to refute `p`, `w2` =
believes exactly `◯p` (the refuting world), `w3` = believes `◯p, p`, `w4` =
the fallible ceiling).  `decide` re-runs the verified checker inside the
kernel, so the theorem is kernel-honest — no `native_decide`. -/

/-- The emitted countermodel for `◯p ⊢ p`, pinned as data. -/
def demoM : FinCM :=
  { n := 5
    ri := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),
           (2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
    rm := [(0,0),(0,1),(0,2),(0,3),(0,4),(1,1),(2,2),(2,3),(2,4),(3,3),
           (3,4),(4,4)]
    fall := [4]
    val := [(3, "p"), (4, "p")] }

/-- **`◯p ⊬ p`, by an executable countermodel**: the verified checker
validates `demoM` in the kernel. -/
theorem somehow_p_not_p :
    ¬ Nonempty (LaxND [(prop "p").somehow] (prop "p")) :=
  FinCM.not_provable_of_check (M := demoM) (w := 2) (by decide)

#print axioms FinCM.not_provable_of_check
#print axioms somehow_p_not_p

end PLLND
