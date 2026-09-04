import LaxLogic.PLLG4UIStab

/-!
# Uniform interpolation, phase 4: the truncated quantifiers (v3)

The v2 quantifiers (`PLLG4UI.lean`) are adequate at every fuel above
the consumer's height (`PLLG4UIAdq.lean`), but the fuel cannot be
eliminated by a stabilization argument: the A-side hits an off-by-one
cascade at same-set positions (`docs/ui-endgame.md`).  This file
rebuilds the definition so that no fuel is needed — uniformity holds
*by construction*:

* **omission** — context clauses whose mirrored premise is the
  conclusion's own sequent (all inserted pieces already present, same
  goal) are dropped; the adequacy proof already skips those steps
  (retention absorbs them), and the dropped clause is provably
  redundant *as a formula* (it is set-congruent to the whole);
* **jump budget** — v2's clause shapes are kept verbatim, including
  every `◯(E ⇢ A)`-guard, but each *same-context* recursive
  reference (the `impLLax` head/γ clauses, the `impLImp` side premise
  at a present piece, the `A13` guard at a present antecedent, and
  the `E`-components of the ◯-goal disjuncts) recurses at budget
  `b − 1`; context growth pays into the space defect instead.
  Premise-1 chains keep the context identical, so minimal consumers
  never need more budget than the space's jump-goal count; the
  absorption lemma makes budgets above that threshold provably
  interchangeable — a congruence, usable in any position;
* **N-truncation** — the self-referential ◯-goal disjunct is replaced
  by `◯(E ⇢ ⋁ other disjuncts)`; its consumption opens with `laxL`
  and modus ponens, its landing closes by identity after cutting in
  the induction hypothesis (the monad-multiplication move of
  `lax_fixpoint`).

Design lesson recorded from the first attempt (2026-07-11): an
*ambient-relative* equivalence such as the bare law
`◯(E ⇢ Z) ⊣⊢ ◯Z given E` (proved below as `box_guard_collapse` /
`box_guard_intro`, still useful at consumption sites) is NOT a
congruence, so it may not be folded into negatively-occurring
subterms of the definition — the γ-clause antecedents have no
ambient `E` to redeem them.  (The probe divergence that prompted
this repair later resolved as a comparison artifact — v2 had not
converged at low fuel on the gap-theorem context, while v3 was
already budget-stable at the limit — but the guarded shapes are
kept: they are what the adequacy case-map's induction hypotheses
deliver, and budget-annotation is the congruence-grade device.)

This file: the G4c-level proof engines, the measure layer, and the
definition.  The re-proved tower follows.
-/

open PLLFormula

namespace PLLND

/-! ### Guard absorption (the bare law)

`◯(E ⇢ Z)` and `◯Z` are interchangeable in any context that holds
`E`: collapse is retained modus ponens under the box, introduction is
monotonicity.  This is what lets the same-context clauses of the
truncated quantifiers drop the self-referential `E`-guards that v2
carried (and that made its recursion non-well-founded). -/

/-- Collapse: `E, ◯(E ⇢ Z) ⊢ ◯Z`. -/
theorem box_guard_collapse (E Z : PLLFormula) :
    G4c [E, (E.ifThen Z).somehow] Z.somehow := by
  refine G4c.laxL (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
    (Or.inl rfl)))) ?_
  -- E ⇢ Z, E, ◯(E ⇢ Z) ⊢ ◯Z: reorder and fire the context MP
  exact (G4c.laxR (G4c.mp E Z [(E.ifThen Z).somehow])).perm
    (List.Perm.swap _ _ _)

/-- Introduction: `◯Z ⊢ ◯(E ⇢ Z)`. -/
theorem box_guard_intro (E Z : PLLFormula) :
    G4c [Z.somehow] ((E.ifThen Z).somehow) :=
  box_mono (G4c.impR (G4c.identity_mem (List.mem_cons.mpr
    (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))

/-! ### laxL lifting

Consumption of the truncated ◯-goal disjunct: a boxed hypothesis may
be opened against a ◯-shaped goal (retention keeps the box). -/

/-- `X, Γ ⊢ ◯C  ⟹  ◯X, Γ ⊢ ◯C`. -/
theorem laxL_lift {X C : PLLFormula} {Γ : List PLLFormula}
    (d : G4c (X :: Γ) C.somehow) : G4c (X.somehow :: Γ) C.somehow :=
  G4c.laxL (List.mem_cons.mpr (Or.inl rfl))
    (((d.weaken X.somehow).perm (List.Perm.swap _ _ _)))

/-! ### The truncated quantifiers

`itpE p S fuel b Γ` / `itpA p S fuel b Γ C`.  Recursion structure:

* **space guards** — context-growing clauses driven by a `Γ`-formula
  fire only when their new pieces lie in the space `S` (a
  piece-closed finset fixed at instantiation); real runs always
  satisfy this, and it makes the growth pay strictly into
  `defect := (S \ Γ.toFinset).card`.  Goal-driven growth (`A13` at a
  fresh antecedent) needs no space guard: the goal-weight slot pays.
* **budget `b`** — every same-context recursive reference (`impLLax`
  head/γ, `impLImp` side premise at a present piece, `A13` at a
  present antecedent, the `E`-components of the ◯-goal disjuncts)
  recurses at `b − 1`; at `b = 0` those clauses are dropped (values
  below the jump-goal threshold are never consumed).
* **fuel** — a shadow parameter: every recursive call strictly
  decreases `mu := (defect + b)·(W₀+1) + goalweight` (`W₀` bounds the
  space's weights and the initial goal's), so above `mu` the fuel is
  syntactically irrelevant; the indifference lemma turns this into
  unfold equations for the packaged, fuel-free quantifiers.
-/

/-- Distance of the context set from the space: how many space
formulas the context has not yet absorbed.  Every space-guarded
context growth strictly decreases it. -/
def defect (S : Finset PLLFormula) (Γ : List PLLFormula) : Nat :=
  (S \ Γ.toFinset).card

theorem defect_cons_le (S : Finset PLLFormula) (x : PLLFormula)
    (Γ : List PLLFormula) : defect S (x :: Γ) ≤ defect S Γ := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_sdiff] at hy ⊢
  refine ⟨hy.1, fun hmem => hy.2 ?_⟩
  simp only [List.toFinset_cons, Finset.mem_insert]
  exact Or.inr hmem

theorem defect_cons_lt {S : Finset PLLFormula} {x : PLLFormula}
    {Γ : List PLLFormula} (hS : x ∈ S) (hΓ : x ∉ Γ) :
    defect S (x :: Γ) < defect S Γ := by
  have h1 : S \ (x :: Γ).toFinset = (S \ Γ.toFinset).erase x := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
      Finset.mem_insert, not_or]
    tauto
  rw [defect, h1]
  exact Finset.card_erase_lt_of_mem
    (Finset.mem_sdiff.mpr ⟨hS, fun h => hΓ (List.mem_toFinset.mp h)⟩)

theorem defect_cons_eq {S : Finset PLLFormula} {x : PLLFormula}
    {Γ : List PLLFormula} (hΓ : x ∈ Γ) :
    defect S (x :: Γ) = defect S Γ := by
  unfold defect
  congr 1
  ext y
  simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert]
  constructor
  · rintro ⟨hyS, hy⟩; exact ⟨hyS, fun h => hy (Or.inr h)⟩
  · rintro ⟨hyS, hy⟩
    refine ⟨hyS, fun h => hy ?_⟩
    rcases h with rfl | h
    · exact List.mem_toFinset.mpr hΓ
    · exact h

theorem defect_le_of_subset {S : Finset PLLFormula}
    {Γ₁ Γ₂ : List PLLFormula} (h : Γ₁.toFinset ⊆ Γ₂.toFinset) :
    defect S Γ₂ ≤ defect S Γ₁ := by
  apply Finset.card_le_card
  intro y hy
  rw [Finset.mem_sdiff] at hy ⊢
  exact ⟨hy.1, fun hmem => hy.2 (h hmem)⟩

/-- The recursion measure shadowed by the fuel parameter: `slot` is
`0` for `itpE` and the goal weight for `itpA`; `W0` bounds every goal
weight in play (the space's sup and the initial goal). -/
def mu (S : Finset PLLFormula) (W0 b slot : Nat)
    (Γ : List PLLFormula) : Nat :=
  (defect S Γ + b) * (W0 + 1) + slot

theorem mu_slot_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ : List PLLFormula} (h : slot' < slot) :
    mu S W0 b slot' Γ < mu S W0 b slot Γ :=
  Nat.add_lt_add_left h _

theorem mu_jump_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ : List PLLFormula} (h : slot' ≤ W0) :
    mu S W0 b slot' Γ < mu S W0 (b + 1) slot Γ := by
  unfold mu
  have h1 : (defect S Γ + b) * (W0 + 1) + slot' <
      (defect S Γ + (b + 1)) * (W0 + 1) := by
    have : (defect S Γ + (b + 1)) * (W0 + 1)
        = (defect S Γ + b) * (W0 + 1) + (W0 + 1) := by ring
    omega
  omega

theorem mu_growth_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {Γ Γ' : List PLLFormula} (hd : defect S Γ' < defect S Γ)
    (h : slot' ≤ W0) : mu S W0 b slot' Γ' < mu S W0 b slot Γ := by
  unfold mu
  have h1 : (defect S Γ' + b) * (W0 + 1) + slot' <
      (defect S Γ + b) * (W0 + 1) := by
    have h2 : (defect S Γ' + b) + 1 ≤ defect S Γ + b := by omega
    have h3 : ((defect S Γ' + b) + 1) * (W0 + 1) ≤
        (defect S Γ + b) * (W0 + 1) := Nat.mul_le_mul_right _ h2
    have : ((defect S Γ' + b) + 1) * (W0 + 1)
        = (defect S Γ' + b) * (W0 + 1) + (W0 + 1) := by ring
    omega
  omega

theorem mu_same_set_lt {S : Finset PLLFormula} {W0 b slot slot' : Nat}
    {x : PLLFormula} {Γ : List PLLFormula} (hx : x ∈ Γ)
    (h : slot' < slot) : mu S W0 b slot' (x :: Γ) < mu S W0 b slot Γ := by
  unfold mu
  rw [defect_cons_eq hx]
  omega

/-- Weight bounds for jump goals extracted from a space formula. -/
theorem weight_le_of_mem_left {S : Finset PLLFormula} {W0 : Nat}
    (hW : S.sup PLLFormula.weight ≤ W0) {F : PLLFormula} (hF : F ∈ S) :
    F.weight ≤ W0 :=
  le_trans (Finset.le_sup hF) hW

mutual

/-- ∃-quantifier, truncated form (v3). -/
def itpE (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → PLLFormula
  | 0, _, _ => truePLL
  | fuel + 1, b, Γ =>
      andAll (
        (if falsePLL ∈ Γ then [falsePLL] else [])
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
        ++ Γ.flatMap (fun F => match F with
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then []
                else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
                  [itpE p S fuel b (A :: B :: Γ)]
                else []
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else if A ∈ S ∧ B ∈ S then
                  [(itpE p S fuel b (A :: Γ)).or (itpE p S fuel b (B :: Γ))]
                else []
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  if PLLFormula.prop q ∈ Γ then [itpE p S fuel b (B :: Γ)]
                  else if q = p then []
                  else [(prop q).ifThen (itpE p S fuel b (B :: Γ))]
                else []
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else if A.ifThen (B.ifThen D) ∈ S then
                  [itpE p S fuel b (A.ifThen (B.ifThen D) :: Γ)]
                else []
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                    (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
                  [itpE p S fuel b (A.ifThen D :: B.ifThen D :: Γ)]
                else []
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if D ∈ S then
                  if B.ifThen D ∈ Γ then
                    if (A.ifThen B).ifThen D ∈ S then
                      match b with
                      | 0 => []
                      | b' + 1 =>
                          [((itpE p S fuel b' Γ).ifThen
                              (itpA p S fuel b' Γ (A.ifThen B))).ifThen
                            (itpE p S fuel b (D :: Γ))]
                    else []
                  else if B.ifThen D ∈ S then
                    [((itpE p S fuel b (B.ifThen D :: Γ)).ifThen
                        (itpA p S fuel b (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                      (itpE p S fuel b (D :: Γ))]
                  else []
                else []
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  (if A.somehow.ifThen B ∈ S then
                    match b with
                    | 0 => []
                    | b' + 1 =>
                        [(itpA p S fuel b' Γ A).ifThen
                           (itpE p S fuel b (B :: Γ)),
                         (((itpE p S fuel b' Γ).ifThen
                             (itpA p S fuel b' Γ A.somehow)).somehow).ifThen
                           (itpE p S fuel b (B :: Γ))]
                  else [])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ ∨ x ∉ S then none
                          else some ((((itpE p S fuel b (x :: Γ)).ifThen
                              (itpA p S fuel b (x :: Γ) A.somehow)).somehow).ifThen
                            (itpE p S fuel b (B :: Γ)))
                      | _ => none)
                else []
            | .somehow χ =>
                if χ ∈ Γ ∨ χ ∉ S then []
                else [(itpE p S fuel b (χ :: Γ)).somehow]
            | _ => []))

/-- ∀-quantifier, truncated form (v3). -/
def itpA (p : String) (S : Finset PLLFormula) :
    Nat → Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _, _ => falsePLL
  | fuel + 1, b, Γ, C =>
      let env : List PLLFormula := Γ.flatMap (fun F => match F with
            | .prop q =>
                if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
            | .and A B =>
                if A ∈ Γ ∧ B ∈ Γ then []
                else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
                  [itpA p S fuel b (A :: B :: Γ) C]
                else []
            | .or A B =>
                if A ∈ Γ ∨ B ∈ Γ then []
                else if A ∈ S ∧ B ∈ S then
                  [((itpE p S fuel b (A :: Γ)).ifThen
                      (itpA p S fuel b (A :: Γ) C)).and
                   ((itpE p S fuel b (B :: Γ)).ifThen
                      (itpA p S fuel b (B :: Γ) C))]
                else []
            | .ifThen (.prop q) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  if PLLFormula.prop q ∈ Γ then [itpA p S fuel b (B :: Γ) C]
                  else if q = p then []
                  else [(prop q).and (itpA p S fuel b (B :: Γ) C)]
                else []
            | .ifThen (.and A B) D =>
                if A.ifThen (B.ifThen D) ∈ Γ then []
                else if A.ifThen (B.ifThen D) ∈ S then
                  [itpA p S fuel b (A.ifThen (B.ifThen D) :: Γ) C]
                else []
            | .ifThen (.or A B) D =>
                if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
                else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
                    (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
                  [itpA p S fuel b (A.ifThen D :: B.ifThen D :: Γ) C]
                else []
            | .ifThen (.ifThen A B) D =>
                if D ∈ Γ then []
                else if D ∈ S then
                  if B.ifThen D ∈ Γ then
                    if (A.ifThen B).ifThen D ∈ S then
                      match b with
                      | 0 => []
                      | b' + 1 =>
                          [((itpE p S fuel b' Γ).ifThen
                              (itpA p S fuel b' Γ (A.ifThen B))).and
                            (itpA p S fuel b (D :: Γ) C)]
                    else []
                  else if B.ifThen D ∈ S then
                    [(((itpE p S fuel b (B.ifThen D :: Γ)).ifThen
                        (itpA p S fuel b (B.ifThen D :: Γ) (A.ifThen B)))).and
                      (itpA p S fuel b (D :: Γ) C)]
                  else []
                else []
            | .ifThen (.somehow A) B =>
                if B ∈ Γ then []
                else if B ∈ S then
                  (if A.somehow.ifThen B ∈ S then
                    match b with
                    | 0 => []
                    | b' + 1 =>
                        [(itpA p S fuel b' Γ A).and
                           (itpA p S fuel b (B :: Γ) C),
                         (((itpE p S fuel b' Γ).ifThen
                             (itpA p S fuel b' Γ A.somehow)).somehow).and
                           (itpA p S fuel b (B :: Γ) C)]
                  else [])
                  ++ Γ.filterMap (fun X => match X with
                      | .somehow x =>
                          if x ∈ Γ ∨ x ∉ S then none
                          else some (((((itpE p S fuel b (x :: Γ)).ifThen
                              (itpA p S fuel b (x :: Γ) A.somehow)).somehow)).and
                            (itpA p S fuel b (B :: Γ) C))
                      | _ => none)
                else []
            | .somehow χ => (match C with
                  | .somehow _ =>
                      if χ ∈ Γ ∨ χ ∉ S then []
                      else
                        [((itpE p S fuel b (χ :: Γ)).ifThen
                            (itpA p S fuel b (χ :: Γ) C)).somehow]
                  | _ => [])
            | _ => [])
      let goal : List PLLFormula := (match C with
            | .prop q => if q = p then [] else [prop q]
            | .falsePLL => []
            | .and C₁ C₂ =>
                [(itpA p S fuel b Γ C₁).and (itpA p S fuel b Γ C₂)]
            | .or C₁ C₂ => [itpA p S fuel b Γ C₁, itpA p S fuel b Γ C₂]
            | .ifThen C₁ C₂ =>
                if C₁ ∈ Γ then
                  match b with
                  | 0 => []
                  | b' + 1 =>
                      [(itpE p S fuel b' (C₁ :: Γ)).ifThen
                        (itpA p S fuel b (C₁ :: Γ) C₂)]
                else
                  [(itpE p S fuel b (C₁ :: Γ)).ifThen
                    (itpA p S fuel b (C₁ :: Γ) C₂)]
            | .somehow D =>
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S fuel b' Γ).ifThen
                        (itpA p S fuel b Γ D)).somehow])
      let others := goal ++ env
      orAll (match C with
        | .somehow _ =>
            others ++
              (if others.isEmpty then []
               else match b with
                 | 0 => []
                 | b' + 1 =>
                     [((itpE p S fuel b' Γ).ifThen (orAll others)).somehow])
        | _ => others)

end

/-! ### Monotonicity infrastructure: packaged clause tables

One-level unfoldings of `itpE`/`itpA` at successor fuel, with every
recursive reference kept *folded*.  Both monotonicity proofs work over
these symbols, so the (large) clause tables are transcribed once; the
unfold lemmas are definitional. -/

/-- The conjunct table of `itpE p S (f+1) b Γ`, references folded. -/
def itpEcls (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) : List PLLFormula :=
  (if falsePLL ∈ Γ then [falsePLL] else [])
  ++ Γ.filterMap (fun F => match F with
      | .prop q => if q = p then none else some (prop q)
      | _ => none)
  ++ Γ.flatMap (fun F => match F with
      | .and A B =>
          if A ∈ Γ ∧ B ∈ Γ then []
          else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
            [itpE p S f b (A :: B :: Γ)]
          else []
      | .or A B =>
          if A ∈ Γ ∨ B ∈ Γ then []
          else if A ∈ S ∧ B ∈ S then
            [(itpE p S f b (A :: Γ)).or (itpE p S f b (B :: Γ))]
          else []
      | .ifThen (.prop q) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            if PLLFormula.prop q ∈ Γ then [itpE p S f b (B :: Γ)]
            else if q = p then []
            else [(prop q).ifThen (itpE p S f b (B :: Γ))]
          else []
      | .ifThen (.and A B) D =>
          if A.ifThen (B.ifThen D) ∈ Γ then []
          else if A.ifThen (B.ifThen D) ∈ S then
            [itpE p S f b (A.ifThen (B.ifThen D) :: Γ)]
          else []
      | .ifThen (.or A B) D =>
          if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
          else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
              (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
            [itpE p S f b (A.ifThen D :: B.ifThen D :: Γ)]
          else []
      | .ifThen (.ifThen A B) D =>
          if D ∈ Γ then []
          else if D ∈ S then
            if B.ifThen D ∈ Γ then
              if (A.ifThen B).ifThen D ∈ S then
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S f b' Γ).ifThen
                        (itpA p S f b' Γ (A.ifThen B))).ifThen
                      (itpE p S f b (D :: Γ))]
              else []
            else if B.ifThen D ∈ S then
              [((itpE p S f b (B.ifThen D :: Γ)).ifThen
                  (itpA p S f b (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                (itpE p S f b (D :: Γ))]
            else []
          else []
      | .ifThen (.somehow A) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            (if A.somehow.ifThen B ∈ S then
              match b with
              | 0 => []
              | b' + 1 =>
                  [(itpA p S f b' Γ A).ifThen
                     (itpE p S f b (B :: Γ)),
                   (((itpE p S f b' Γ).ifThen
                       (itpA p S f b' Γ A.somehow)).somehow).ifThen
                     (itpE p S f b (B :: Γ))]
            else [])
            ++ Γ.filterMap (fun X => match X with
                | .somehow x =>
                    if x ∈ Γ ∨ x ∉ S then none
                    else some ((((itpE p S f b (x :: Γ)).ifThen
                        (itpA p S f b (x :: Γ) A.somehow)).somehow).ifThen
                      (itpE p S f b (B :: Γ)))
                | _ => none)
          else []
      | .somehow χ =>
          if χ ∈ Γ ∨ χ ∉ S then []
          else [(itpE p S f b (χ :: Γ)).somehow]
      | _ => [])

/-- One-level unfolding of `itpE` at successor fuel. -/
theorem itpE_succ (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) :
    itpE p S (f + 1) b Γ = andAll (itpEcls p S f b Γ) := rfl

/-- The goal-directed disjunct table of `itpA p S (f+1) b Γ C`. -/
def itpAgoal (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .prop q => if q = p then [] else [prop q]
  | .falsePLL => []
  | .and C₁ C₂ =>
      [(itpA p S f b Γ C₁).and (itpA p S f b Γ C₂)]
  | .or C₁ C₂ => [itpA p S f b Γ C₁, itpA p S f b Γ C₂]
  | .ifThen C₁ C₂ =>
      if C₁ ∈ Γ then
        match b with
        | 0 => []
        | b' + 1 =>
            [(itpE p S f b' (C₁ :: Γ)).ifThen
              (itpA p S f b (C₁ :: Γ) C₂)]
      else
        [(itpE p S f b (C₁ :: Γ)).ifThen
          (itpA p S f b (C₁ :: Γ) C₂)]
  | .somehow D =>
      match b with
      | 0 => []
      | b' + 1 =>
          [((itpE p S f b' Γ).ifThen
              (itpA p S f b Γ D)).somehow]

/-- The context-directed disjunct table of `itpA p S (f+1) b Γ C`. -/
def itpAenv (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  Γ.flatMap (fun F => match F with
      | .prop q =>
          if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
      | .and A B =>
          if A ∈ Γ ∧ B ∈ Γ then []
          else if (A ∈ Γ ∨ A ∈ S) ∧ (B ∈ Γ ∨ B ∈ S) then
            [itpA p S f b (A :: B :: Γ) C]
          else []
      | .or A B =>
          if A ∈ Γ ∨ B ∈ Γ then []
          else if A ∈ S ∧ B ∈ S then
            [((itpE p S f b (A :: Γ)).ifThen
                (itpA p S f b (A :: Γ) C)).and
             ((itpE p S f b (B :: Γ)).ifThen
                (itpA p S f b (B :: Γ) C))]
          else []
      | .ifThen (.prop q) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            if PLLFormula.prop q ∈ Γ then [itpA p S f b (B :: Γ) C]
            else if q = p then []
            else [(prop q).and (itpA p S f b (B :: Γ) C)]
          else []
      | .ifThen (.and A B) D =>
          if A.ifThen (B.ifThen D) ∈ Γ then []
          else if A.ifThen (B.ifThen D) ∈ S then
            [itpA p S f b (A.ifThen (B.ifThen D) :: Γ) C]
          else []
      | .ifThen (.or A B) D =>
          if A.ifThen D ∈ Γ ∧ B.ifThen D ∈ Γ then []
          else if (A.ifThen D ∈ Γ ∨ A.ifThen D ∈ S) ∧
              (B.ifThen D ∈ Γ ∨ B.ifThen D ∈ S) then
            [itpA p S f b (A.ifThen D :: B.ifThen D :: Γ) C]
          else []
      | .ifThen (.ifThen A B) D =>
          if D ∈ Γ then []
          else if D ∈ S then
            if B.ifThen D ∈ Γ then
              if (A.ifThen B).ifThen D ∈ S then
                match b with
                | 0 => []
                | b' + 1 =>
                    [((itpE p S f b' Γ).ifThen
                        (itpA p S f b' Γ (A.ifThen B))).and
                      (itpA p S f b (D :: Γ) C)]
              else []
            else if B.ifThen D ∈ S then
              [(((itpE p S f b (B.ifThen D :: Γ)).ifThen
                  (itpA p S f b (B.ifThen D :: Γ) (A.ifThen B)))).and
                (itpA p S f b (D :: Γ) C)]
            else []
          else []
      | .ifThen (.somehow A) B =>
          if B ∈ Γ then []
          else if B ∈ S then
            (if A.somehow.ifThen B ∈ S then
              match b with
              | 0 => []
              | b' + 1 =>
                  [(itpA p S f b' Γ A).and
                     (itpA p S f b (B :: Γ) C),
                   (((itpE p S f b' Γ).ifThen
                       (itpA p S f b' Γ A.somehow)).somehow).and
                     (itpA p S f b (B :: Γ) C)]
            else [])
            ++ Γ.filterMap (fun X => match X with
                | .somehow x =>
                    if x ∈ Γ ∨ x ∉ S then none
                    else some (((((itpE p S f b (x :: Γ)).ifThen
                        (itpA p S f b (x :: Γ) A.somehow)).somehow)).and
                      (itpA p S f b (B :: Γ) C))
                | _ => none)
          else []
      | .somehow χ => (match C with
            | .somehow _ =>
                if χ ∈ Γ ∨ χ ∉ S then []
                else
                  [((itpE p S f b (χ :: Γ)).ifThen
                      (itpA p S f b (χ :: Γ) C)).somehow]
            | _ => [])
      | _ => [])

/-- The undecorated disjunct table (`others`) of `itpA p S (f+1) b Γ C`. -/
def itpAoth (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  itpAgoal p S f b Γ C ++ itpAenv p S f b Γ C

/-- The full disjunct table of `itpA p S (f+1) b Γ C`, including the
truncation disjunct for ◯-goals. -/
def itpAfull (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) : List PLLFormula :=
  match C with
  | .somehow _ =>
      itpAoth p S f b Γ C ++
        (if (itpAoth p S f b Γ C).isEmpty then []
         else match b with
           | 0 => []
           | b' + 1 =>
               [((itpE p S f b' Γ).ifThen
                   (orAll (itpAoth p S f b Γ C))).somehow])
  | _ => itpAoth p S f b Γ C

/-- One-level unfolding of `itpA` at successor fuel. -/
theorem itpA_succ (p : String) (S : Finset PLLFormula) (f b : Nat)
    (Γ : List PLLFormula) (C : PLLFormula) :
    itpA p S (f + 1) b Γ C = orAll (itpAfull p S f b Γ C) := rfl

/-! ### Member-wise mapping helpers -/

/-- Conjunction-table monotonicity from a member-wise mapping. -/
theorem andAll_map {l L : List PLLFormula}
    (hmap : ∀ φ ∈ l, ∃ ψ ∈ L, G4c [ψ] φ) : G4c [andAll L] (andAll l) := by
  refine G4c.andAll_intro ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hd⟩ := hmap φ hφ
  exact G4c.andAll_elim hψ hd

/-- Disjunction-table monotonicity from a member-wise mapping. -/
theorem orAll_map {l L : List PLLFormula}
    (hmap : ∀ φ ∈ l, ∃ ψ ∈ L, G4c [φ] ψ) : G4c [orAll l] (orAll L) := by
  refine G4c.orAll_elim ?_
  intro φ hφ
  obtain ⟨ψ, hψ, hd⟩ := hmap φ hφ
  exact G4c.orAll_intro hψ hd

/-- Append two member-wise mappings. -/
theorem map_append {l₁ l₂ L₁ L₂ : List PLLFormula}
    (h₁ : ∀ φ ∈ l₁, ∃ ψ ∈ L₁, G4c [φ] ψ)
    (h₂ : ∀ φ ∈ l₂, ∃ ψ ∈ L₂, G4c [φ] ψ) :
    ∀ φ ∈ l₁ ++ l₂, ∃ ψ ∈ L₁ ++ L₂, G4c [φ] ψ := by
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · obtain ⟨ψ, hψ, hd⟩ := h₁ φ hφ
    exact ⟨ψ, List.mem_append.mpr (Or.inl hψ), hd⟩
  · obtain ⟨ψ, hψ, hd⟩ := h₂ φ hφ
    exact ⟨ψ, List.mem_append.mpr (Or.inr hψ), hd⟩

/-- The ◯-goal disjunction with its truncation disjunct: a member-wise
mapping on the `others` plus a contravariant feed for the truncation
guard whenever the low-side truncation is live. -/
theorem itpAfull_box_map {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ : List PLLFormula} {D : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ (D.somehow),
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ (D.somehow), G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ] (itpE p S f₁ b₁' Γ)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ (D.somehow))]
        (orAll (itpAfull p S f₂ b₂ Γ (D.somehow))) := by
  simp only [itpAfull]
  refine G4c.orAll_elim ?_
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
    exact G4c.orAll_intro (List.mem_append.mpr (Or.inl hψ)) hd
  · by_cases h1 : (itpAoth p S f₁ b₁ Γ (D.somehow)).isEmpty = true
    · rw [if_pos h1] at hφ; cases hφ
    · rw [if_neg h1] at hφ
      cases b₁ with
      | zero => cases hφ
      | succ b₁' =>
          rcases List.mem_singleton.mp hφ with rfl
          obtain ⟨b₂', rfl, hE⟩ := htr b₁' rfl
          have h2 : ¬ (itpAoth p S f₂ (b₂' + 1) Γ (D.somehow)).isEmpty = true := by
            intro h2
            have h2' : itpAoth p S f₂ (b₂' + 1) Γ (D.somehow) = [] := by
              simpa using h2
            cases hl : itpAoth p S f₁ (b₁' + 1) Γ (D.somehow) with
            | nil => rw [hl] at h1; simp at h1
            | cons a t =>
                obtain ⟨ψ, hψ, -⟩ := hoth a (by rw [hl]; exact .head _)
                rw [h2'] at hψ; cases hψ
          refine G4c.orAll_intro ?_ (box_mono (imp_mono hE (orAll_map hoth)))
          refine List.mem_append.mpr (Or.inr ?_)
          rw [if_neg h2]
          exact .head _

/-- Full-table monotonicity: dispatch on the goal shape (the
truncation disjunct exists only for ◯-goals). -/
theorem itpAfull_map {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ C,
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ C, G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ] (itpE p S f₁ b₁' Γ)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ C)]
        (orAll (itpAfull p S f₂ b₂ Γ C)) := by
  cases C with
  | somehow D => exact itpAfull_box_map hoth htr
  | prop q => simp only [itpAfull]; exact orAll_map hoth
  | falsePLL => simp only [itpAfull]; exact orAll_map hoth
  | and C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | or C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | ifThen C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth

/-! ### Fuel monotonicity

More fuel means a *stronger* ∃-quantifier and a *weaker* ∀-quantifier,
exactly as for the v2 quantifiers (`inter_fuel_mono`): the two halves
are proved simultaneously because the `(E ⇢ A)`-guards flip variance.
The space guards and omission guards mention neither fuel nor budget,
so the two sides always take the same branch; the budget-gated clauses
pair up at the same budget. -/

set_option maxHeartbeats 4000000 in
theorem itp_fuel_mono (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat),
    (∀ b Γ, G4c [itpE p S (fuel + 1) b Γ] (itpE p S fuel b Γ)) ∧
    (∀ b Γ C, G4c [itpA p S fuel b Γ C] (itpA p S (fuel + 1) b Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro b Γ
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro b Γ C
        simp only [itpA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- [itpE p S (fuel+2) b Γ] ⊢ itpE p S (fuel+1) b Γ
        intro b Γ
        rw [itpE_succ p S (fuel + 1) b Γ, itpE_succ p S fuel b Γ]
        refine andAll_map ?_
        intro φ hφ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause: identical at both fuels
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨falsePLL, ?_, G4c.botL (.head _)⟩
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hφ
          · -- the atom clauses: identical at both fuels
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine ⟨prop q, ?_, G4c.init (.head _)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihE b (A :: B :: Γ)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.and B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, or_mono (ihE b (A :: Γ)) (ihE b (B :: Γ))⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨_, ?_, box_mono (ihE b (χ :: Γ))⟩
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hFΓ, ?_⟩))
                simp only
                rw [if_neg hg]
                exact .head _
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihE b (B :: Γ)⟩
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_,
                            imp_mono (G4c.init (.head _)) (ihE b (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE b (A₁.ifThen (B₁.ifThen B) :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE b (A₁.ifThen B :: B₁.ifThen B :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, imp_mono
                                (imp_mono (ihE b' Γ) (ihA b' Γ (A₁.ifThen B₁)))
                                (ihE (b' + 1) (B :: Γ))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono
                            (imp_mono (ihE b (B₁.ifThen B :: Γ))
                              (ihA b (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihE b (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, imp_mono (ihA b' Γ A₁)
                                  (ihE (b' + 1) (B :: Γ))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, imp_mono
                                  (box_mono (imp_mono (ihE b' Γ)
                                    (ihA b' Γ A₁.somehow)))
                                  (ihE (b' + 1) (B :: Γ))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, imp_mono
                                (box_mono (imp_mono (ihE b (x :: Γ))
                                  (ihA b (x :: Γ) A₁.somehow)))
                                (ihE b (B :: Γ))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- [itpA p S (fuel+1) b Γ C] ⊢ itpA p S (fuel+2) b Γ C
        intro b Γ C
        rw [itpA_succ p S fuel b Γ C, itpA_succ p S (fuel + 1) b Γ C]
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel b Γ C,
            ∃ ψ ∈ itpAgoal p S (fuel + 1) b Γ C, G4c [φ] ψ := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨prop q, ?_, G4c.init (.head _)⟩
                rw [if_neg hq]
                exact .head _
          | falsePLL =>
              simp only [itpAgoal] at hφ
              cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              exact ⟨_, .head _, and_mono (ihA b Γ C₁) (ihA b Γ C₂)⟩
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact ⟨_, .head _, ihA b Γ C₁⟩
              · rcases List.mem_singleton.mp hφ' with rfl
                exact ⟨_, .tail _ (.head _), ihA b Γ C₂⟩
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next hpres =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    refine ⟨_, ?_, imp_mono (ihE b' (C₁ :: Γ))
                      (ihA (b' + 1) (C₁ :: Γ) C₂)⟩
                    rw [if_pos hpres]
                    exact .head _
              next hpres =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨_, ?_, imp_mono (ihE b (C₁ :: Γ))
                  (ihA b (C₁ :: Γ) C₂)⟩
                rw [if_neg hpres]
                exact .head _
          | somehow D =>
              simp only [itpAgoal] at hφ ⊢
              cases b with
              | zero => cases hφ
              | succ b' =>
                  rcases List.mem_singleton.mp hφ with rfl
                  exact ⟨_, .head _,
                    box_mono (imp_mono (ihE b' Γ) (ihA (b' + 1) Γ D))⟩
        have hENV : ∀ φ ∈ itpAenv p S fuel b Γ C,
            ∃ ψ ∈ itpAenv p S (fuel + 1) b Γ C, G4c [φ] ψ := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨truePLL, ?_, G4c.truePLL_intro _⟩
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hFΓ, ?_⟩
                simp only
                rw [if_pos hg]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihA b (A :: B :: Γ) C⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.and B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, and_mono
                    (imp_mono (ihE b (A :: Γ)) (ihA b (A :: Γ) C))
                    (imp_mono (ihE b (B :: Γ)) (ihA b (B :: Γ) C))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.or B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              · split at hin
                next => cases hin
                next hg =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, box_mono
                    (imp_mono (ihE b (χ :: Γ)) (ihA b (χ :: Γ) _))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩
                  simp only
                  rw [if_neg hg]
                  exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihA b (B :: Γ) C⟩
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono (G4c.init (.head _))
                            (ihA b (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihA b (A₁.ifThen (B₁.ifThen B) :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_,
                        ihA b (A₁.ifThen B :: B₁.ifThen B :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, and_mono
                                (imp_mono (ihE b' Γ) (ihA b' Γ (A₁.ifThen B₁)))
                                (ihA (b' + 1) (B :: Γ) C)⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono
                            (imp_mono (ihE b (B₁.ifThen B :: Γ))
                              (ihA b (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihA b (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, and_mono (ihA b' Γ A₁)
                                  (ihA (b' + 1) (B :: Γ) C)⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, and_mono
                                  (box_mono (imp_mono (ihE b' Γ)
                                    (ihA b' Γ A₁.somehow)))
                                  (ihA (b' + 1) (B :: Γ) C)⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, and_mono
                                (box_mono (imp_mono (ihE b (x :: Γ))
                                  (ihA b (x :: Γ) A₁.somehow)))
                                (ihA b (B :: Γ) C)⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        exact itpAfull_map (map_append hGOAL hENV)
          (fun b' hb => ⟨b', hb, ihE b' Γ⟩)

/-! ### Budget monotonicity

A larger jump budget means a *stronger* ∃-quantifier and a *weaker*
∀-quantifier, at every fixed fuel: the budget-gated clauses vanish at
`b = 0` (a subset of the conjunct/disjunct table, so nothing to prove
resp. nothing to map), and at successor budgets the components pair up
with budgets `(b', b)` against `(b, b+1)` — the ∀-quantified induction
hypotheses cover every pairing.  The induction is on fuel; the budget
is handled by the same local splits as in `itp_fuel_mono`. -/

set_option maxHeartbeats 4000000 in
theorem itp_budget_mono (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat),
    (∀ b Γ, G4c [itpE p S fuel (b + 1) Γ] (itpE p S fuel b Γ)) ∧
    (∀ b Γ C, G4c [itpA p S fuel b Γ C] (itpA p S fuel (b + 1) Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro b Γ
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro b Γ C
        simp only [itpA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- [itpE p S (fuel+1) (b+1) Γ] ⊢ itpE p S (fuel+1) b Γ
        intro b Γ
        rw [itpE_succ p S fuel (b + 1) Γ, itpE_succ p S fuel b Γ]
        refine andAll_map ?_
        intro φ hφ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause: identical at both budgets
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨falsePLL, ?_, G4c.botL (.head _)⟩
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos hbot]; exact .head _))))
            next => cases hφ
          · -- the atom clauses: identical at both budgets
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine ⟨prop q, ?_, G4c.init (.head _)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr ⟨prop q, hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihE b (A :: B :: Γ)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.and B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, or_mono (ihE b (A :: Γ)) (ihE b (B :: Γ))⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hFΓ, ?_⟩))
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨_, ?_, box_mono (ihE b (χ :: Γ))⟩
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hFΓ, ?_⟩))
                simp only
                rw [if_neg hg]
                exact .head _
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihE b (B :: Γ)⟩
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_,
                            imp_mono (G4c.init (.head _)) (ihE b (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE b (A₁.ifThen (B₁.ifThen B) :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE b (A₁.ifThen B :: B₁.ifThen B :: Γ)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, imp_mono
                                (imp_mono (ihE b' Γ) (ihA b' Γ (A₁.ifThen B₁)))
                                (ihE (b' + 1) (B :: Γ))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono
                            (imp_mono (ihE b (B₁.ifThen B :: Γ))
                              (ihA b (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihE b (B :: Γ))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩))
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, imp_mono (ihA b' Γ A₁)
                                  (ihE (b' + 1) (B :: Γ))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, imp_mono
                                  (box_mono (imp_mono (ihE b' Γ)
                                    (ihA b' Γ A₁.somehow)))
                                  (ihE (b' + 1) (B :: Γ))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, imp_mono
                                (box_mono (imp_mono (ihE b (x :: Γ))
                                  (ihA b (x :: Γ) A₁.somehow)))
                                (ihE b (B :: Γ))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- [itpA p S (fuel+1) b Γ C] ⊢ itpA p S (fuel+1) (b+1) Γ C
        intro b Γ C
        rw [itpA_succ p S fuel b Γ C, itpA_succ p S fuel (b + 1) Γ C]
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel b Γ C,
            ∃ ψ ∈ itpAgoal p S fuel (b + 1) Γ C, G4c [φ] ψ := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨prop q, ?_, G4c.init (.head _)⟩
                rw [if_neg hq]
                exact .head _
          | falsePLL =>
              simp only [itpAgoal] at hφ
              cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              exact ⟨_, .head _, and_mono (ihA b Γ C₁) (ihA b Γ C₂)⟩
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact ⟨_, .head _, ihA b Γ C₁⟩
              · rcases List.mem_singleton.mp hφ' with rfl
                exact ⟨_, .tail _ (.head _), ihA b Γ C₂⟩
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next hpres =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    refine ⟨_, ?_, imp_mono (ihE b' (C₁ :: Γ))
                      (ihA (b' + 1) (C₁ :: Γ) C₂)⟩
                    rw [if_pos hpres]
                    exact .head _
              next hpres =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨_, ?_, imp_mono (ihE b (C₁ :: Γ))
                  (ihA b (C₁ :: Γ) C₂)⟩
                rw [if_neg hpres]
                exact .head _
          | somehow D =>
              simp only [itpAgoal] at hφ ⊢
              cases b with
              | zero => cases hφ
              | succ b' =>
                  rcases List.mem_singleton.mp hφ with rfl
                  exact ⟨_, .head _,
                    box_mono (imp_mono (ihE b' Γ) (ihA (b' + 1) Γ D))⟩
        have hENV : ∀ φ ∈ itpAenv p S fuel b Γ C,
            ∃ ψ ∈ itpAenv p S fuel (b + 1) Γ C, G4c [φ] ψ := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨truePLL, ?_, G4c.truePLL_intro _⟩
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hFΓ, ?_⟩
                simp only
                rw [if_pos hg]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, ihA b (A :: B :: Γ) C⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.and B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, and_mono
                    (imp_mono (ihE b (A :: Γ)) (ihA b (A :: Γ) C))
                    (imp_mono (ihE b (B :: Γ)) (ihA b (B :: Γ) C))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.or B, hFΓ, ?_⟩
                  simp only
                  rw [if_neg h1, if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              · split at hin
                next => cases hin
                next hg =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, box_mono
                    (imp_mono (ihE b (χ :: Γ)) (ihA b (χ :: Γ) _))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩
                  simp only
                  rw [if_neg hg]
                  exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_, ihA b (B :: Γ) C⟩
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hFΓ, ?_⟩
                        simp only
                        rw [if_neg hBΓ, if_pos hBS, if_pos hq]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono (G4c.init (.head _))
                            (ihA b (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hBΓ, if_pos hBS, if_neg hq, if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihA b (A₁.ifThen (B₁.ifThen B) :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_,
                        ihA b (A₁.ifThen B :: B₁.ifThen B :: Γ) C⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hFΓ, ?_⟩
                      simp only
                      rw [if_neg h1, if_pos h2]
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, and_mono
                                (imp_mono (ihE b' Γ) (ihA b' Γ (A₁.ifThen B₁)))
                                (ihA (b' + 1) (B :: Γ) C)⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hDΓ, if_pos hDS, if_pos hBD, if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono
                            (imp_mono (ihE b (B₁.ifThen B :: Γ))
                              (ihA b (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                            (ihA b (B :: Γ) C)⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hFΓ, ?_⟩
                          simp only
                          rw [if_neg hDΓ, if_pos hDS, if_neg hBD, if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, and_mono (ihA b' Γ A₁)
                                  (ihA (b' + 1) (B :: Γ) C)⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, and_mono
                                  (box_mono (imp_mono (ihE b' Γ)
                                    (ihA b' Γ A₁.somehow)))
                                  (ihA (b' + 1) (B :: Γ) C)⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                                simp only
                                rw [if_neg hBΓ, if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hg =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, and_mono
                                (box_mono (imp_mono (ihE b (x :: Γ))
                                  (ihA b (x :: Γ) A₁.somehow)))
                                (ihA b (B :: Γ) C)⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩
                              simp only
                              rw [if_neg hBΓ, if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, ?_⟩))
                              simp only
                              rw [if_neg hg]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        exact itpAfull_map (map_append hGOAL hENV)
          (fun b' hb => ⟨b, rfl, by rw [hb]; exact ihE b' Γ⟩)

/-! ### Multi-step budget monotonicity

Composing the single steps with cut closes any budget gap, at every
fixed fuel — the absorption device that will make budgets above the
jump-goal threshold interchangeable. -/

theorem itp_budget_mono_le (p : String) (S : Finset PLLFormula) {b b' : Nat}
    (h : b ≤ b') : ∀ fuel,
    (∀ Γ, G4c [itpE p S fuel b' Γ] (itpE p S fuel b Γ)) ∧
    (∀ Γ C, G4c [itpA p S fuel b Γ C] (itpA p S fuel b' Γ C)) := by
  intro fuel
  induction h with
  | refl =>
      exact ⟨fun Γ => G4c.iden (.head _), fun Γ C => G4c.iden (.head _)⟩
  | @step m _ ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro Γ
        exact G4c.cut ((itp_budget_mono p S fuel).1 m Γ)
          (((ihE Γ).weaken _).perm (List.Perm.swap _ _ _))
      · intro Γ C
        exact G4c.cut (ihA Γ C)
          ((((itp_budget_mono p S fuel).2 m Γ C).weaken _).perm
            (List.Perm.swap _ _ _))

/-! ### p-freeness

Every clause builds from recursive values (p-free by the induction
hypotheses), non-`p` atoms (the clauses guard against `p` explicitly),
`⊤` and `⊥`; the truncation disjunct adds only an `orAll` over the
already-covered table. -/

private theorem mem_atoms_andAll {x : String} :
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

private theorem mem_atoms_orAll {x : String} :
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

set_option maxHeartbeats 4000000 in
/-- **The truncated quantifiers are p-free.** -/
theorem itp_pfree (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat),
    (∀ b Γ, p ∉ (itpE p S fuel b Γ).atoms) ∧
    (∀ b Γ C, p ∉ (itpA p S fuel b Γ C).atoms) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro b Γ h; simp [itpE, truePLL] at h
      · intro b Γ C h; simp [itpA] at h
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro b Γ hmem
        rw [itpE_succ p S fuel b Γ] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_andAll hmem
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause
            split at hφ
            · rcases List.mem_singleton.mp hφ with rfl
              simp at hx
            · cases hφ
          · -- the atom clauses
            obtain ⟨F, _, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                · cases heq
                · injection heq with heq'
                  subst heq'
                  rw [atoms_prop, Finset.mem_singleton] at hx
                  subst hx
                  simp_all
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihE _ _ hx
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  rw [atoms_or, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · exact ihE _ _ hx
                  · exact ihE _ _ hx
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                rcases List.mem_singleton.mp hin with rfl
                rw [atoms_somehow] at hx
                exact ihE _ _ hx
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next =>
                        rcases List.mem_singleton.mp hin with rfl
                        exact ihE _ _ hx
                      next =>
                        split at hin
                        next => cases hin
                        next =>
                          rcases List.mem_singleton.mp hin with rfl
                          rw [atoms_ifThen, Finset.mem_union] at hx
                          rcases hx with hx | hx
                          · rw [atoms_prop, Finset.mem_singleton] at hx
                            subst hx
                            simp_all
                          · exact ihE _ _ hx
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      exact ihE _ _ hx
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      exact ihE _ _ hx
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next =>
                        split at hin
                        next =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              rw [atoms_ifThen, Finset.mem_union] at hx
                              rcases hx with hx | hx
                              · rw [atoms_ifThen, Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · exact ihE _ _ hx
                                · exact ihA _ _ _ hx
                              · exact ihE _ _ hx
                        next => cases hin
                      next =>
                        split at hin
                        next =>
                          rcases List.mem_singleton.mp hin with rfl
                          rw [atoms_ifThen, Finset.mem_union] at hx
                          rcases hx with hx | hx
                          · rw [atoms_ifThen, Finset.mem_union] at hx
                            rcases hx with hx | hx
                            · exact ihE _ _ hx
                            · exact ihA _ _ _ hx
                          · exact ihE _ _ hx
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · rw [atoms_ifThen, Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · exact ihA _ _ _ hx
                                · exact ihE _ _ hx
                              · rcases List.mem_singleton.mp hin' with rfl
                                rw [atoms_ifThen, Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · rw [atoms_somehow, atoms_ifThen,
                                    Finset.mem_union] at hx
                                  rcases hx with hx | hx
                                  · exact ihE _ _ hx
                                  · exact ihA _ _ _ hx
                                · exact ihE _ _ hx
                        next => cases hin
                      · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next =>
                              injection heq with heq'
                              subst heq'
                              rw [atoms_ifThen, Finset.mem_union] at hx
                              rcases hx with hx | hx
                              · rw [atoms_somehow, atoms_ifThen,
                                  Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · exact ihE _ _ hx
                                · exact ihA _ _ _ hx
                              · exact ihE _ _ hx
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · intro b Γ C hmem
        rw [itpA_succ p S fuel b Γ C] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_orAll hmem
        -- the undecorated table, analysed once: consumed by both the
        -- main disjuncts and the truncation disjunct
        have hoth : ∀ ψ ∈ itpAoth p S fuel b Γ C, p ∉ ψ.atoms := by
          intro ψ hψ hx
          simp only [itpAoth] at hψ
          rcases List.mem_append.mp hψ with hψ | hψ
          · -- the goal clauses
            cases C with
            | prop q =>
                simp only [itpAgoal] at hψ
                split at hψ
                · cases hψ
                · rcases List.mem_singleton.mp hψ with rfl
                  rw [atoms_prop, Finset.mem_singleton] at hx
                  subst hx
                  simp_all
            | falsePLL => simp only [itpAgoal] at hψ; cases hψ
            | and C₁ C₂ =>
                simp only [itpAgoal] at hψ
                rcases List.mem_singleton.mp hψ with rfl
                rw [atoms_and, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihA _ _ _ hx
                · exact ihA _ _ _ hx
            | or C₁ C₂ =>
                simp only [itpAgoal] at hψ
                rcases List.mem_cons.mp hψ with rfl | hψ'
                · exact ihA _ _ _ hx
                · rcases List.mem_singleton.mp hψ' with rfl
                  exact ihA _ _ _ hx
            | ifThen C₁ C₂ =>
                simp only [itpAgoal] at hψ
                split at hψ
                next =>
                  cases b with
                  | zero => cases hψ
                  | succ b' =>
                      rcases List.mem_singleton.mp hψ with rfl
                      rw [atoms_ifThen, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · exact ihE _ _ hx
                      · exact ihA _ _ _ hx
                next =>
                  rcases List.mem_singleton.mp hψ with rfl
                  rw [atoms_ifThen, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · exact ihE _ _ hx
                  · exact ihA _ _ _ hx
            | somehow D =>
                simp only [itpAgoal] at hψ
                cases b with
                | zero => cases hψ
                | succ b' =>
                    rcases List.mem_singleton.mp hψ with rfl
                    rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihE _ _ hx
                    · exact ihA _ _ _ hx
          · -- the context clauses
            simp only [itpAenv] at hψ
            obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hψ
            cases F with
            | prop q =>
                simp only at hin
                split at hin
                · rcases List.mem_singleton.mp hin with rfl
                  simp [truePLL] at hx
                · cases hin
            | falsePLL => cases hin
            | and A B =>
                simp only at hin
                split at hin
                next => cases hin
                next =>
                  split at hin
                  next =>
                    rcases List.mem_singleton.mp hin with rfl
                    exact ihA _ _ _ hx
                  next => cases hin
            | or A B =>
                simp only at hin
                split at hin
                next => cases hin
                next =>
                  split at hin
                  next =>
                    rcases List.mem_singleton.mp hin with rfl
                    rw [atoms_and, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · rw [atoms_ifThen, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · exact ihE _ _ hx
                      · exact ihA _ _ _ hx
                    · rw [atoms_ifThen, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · exact ihE _ _ hx
                      · exact ihA _ _ _ hx
                  next => cases hin
            | somehow χ =>
                simp only at hin
                split at hin
                · split at hin
                  next => cases hin
                  next =>
                    rcases List.mem_singleton.mp hin with rfl
                    rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihE _ _ hx
                    · exact ihA _ _ _ hx
                all_goals cases hin
            | ifThen A' B =>
                cases A' with
                | prop q =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next =>
                      split at hin
                      next =>
                        split at hin
                        next =>
                          rcases List.mem_singleton.mp hin with rfl
                          exact ihA _ _ _ hx
                        next =>
                          split at hin
                          next => cases hin
                          next =>
                            rcases List.mem_singleton.mp hin with rfl
                            rw [atoms_and, Finset.mem_union] at hx
                            rcases hx with hx | hx
                            · rw [atoms_prop, Finset.mem_singleton] at hx
                              subst hx
                              simp_all
                            · exact ihA _ _ _ hx
                      next => cases hin
                | falsePLL => cases hin
                | and A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next =>
                      split at hin
                      next =>
                        rcases List.mem_singleton.mp hin with rfl
                        exact ihA _ _ _ hx
                      next => cases hin
                | or A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next =>
                      split at hin
                      next =>
                        rcases List.mem_singleton.mp hin with rfl
                        exact ihA _ _ _ hx
                      next => cases hin
                | ifThen A₁ B₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next =>
                      split at hin
                      next =>
                        split at hin
                        next =>
                          split at hin
                          next =>
                            cases b with
                            | zero => cases hin
                            | succ b' =>
                                rcases List.mem_singleton.mp hin with rfl
                                rw [atoms_and, Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · rw [atoms_ifThen, Finset.mem_union] at hx
                                  rcases hx with hx | hx
                                  · exact ihE _ _ hx
                                  · exact ihA _ _ _ hx
                                · exact ihA _ _ _ hx
                          next => cases hin
                        next =>
                          split at hin
                          next =>
                            rcases List.mem_singleton.mp hin with rfl
                            rw [atoms_and, Finset.mem_union] at hx
                            rcases hx with hx | hx
                            · rw [atoms_ifThen, Finset.mem_union] at hx
                              rcases hx with hx | hx
                              · exact ihE _ _ hx
                              · exact ihA _ _ _ hx
                            · exact ihA _ _ _ hx
                          next => cases hin
                      next => cases hin
                | somehow A₁ =>
                    simp only at hin
                    split at hin
                    next => cases hin
                    next =>
                      split at hin
                      next =>
                        rcases List.mem_append.mp hin with hin | hin
                        · split at hin
                          next =>
                            cases b with
                            | zero => cases hin
                            | succ b' =>
                                rcases List.mem_cons.mp hin with rfl | hin'
                                · rw [atoms_and, Finset.mem_union] at hx
                                  rcases hx with hx | hx
                                  · exact ihA _ _ _ hx
                                  · exact ihA _ _ _ hx
                                · rcases List.mem_singleton.mp hin' with rfl
                                  rw [atoms_and, Finset.mem_union] at hx
                                  rcases hx with hx | hx
                                  · rw [atoms_somehow, atoms_ifThen,
                                      Finset.mem_union] at hx
                                    rcases hx with hx | hx
                                    · exact ihE _ _ hx
                                    · exact ihA _ _ _ hx
                                  · exact ihA _ _ _ hx
                          next => cases hin
                        · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin
                          cases X with
                          | somehow x =>
                              simp only at heq
                              split at heq
                              next => cases heq
                              next =>
                                injection heq with heq'
                                subst heq'
                                rw [atoms_and, Finset.mem_union] at hx
                                rcases hx with hx | hx
                                · rw [atoms_somehow, atoms_ifThen,
                                    Finset.mem_union] at hx
                                  rcases hx with hx | hx
                                  · exact ihE _ _ hx
                                  · exact ihA _ _ _ hx
                                · exact ihA _ _ _ hx
                          | prop _ => cases heq
                          | falsePLL => cases heq
                          | and _ _ => cases heq
                          | or _ _ => cases heq
                          | ifThen _ _ => cases heq
                      next => cases hin
        cases C with
        | somehow D =>
            simp only [itpAfull] at hφ
            rcases List.mem_append.mp hφ with hφ | hφ
            · exact hoth φ hφ hx
            · -- the truncation disjunct
              split at hφ
              next => cases hφ
              next =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihE _ _ hx
                    · obtain ⟨ψ, hψ, hx⟩ := mem_atoms_orAll hx
                      exact hoth ψ hψ hx
        | prop q => simp only [itpAfull] at hφ; exact hoth φ hφ hx
        | falsePLL => simp only [itpAfull] at hφ; exact hoth φ hφ hx
        | and C₁ C₂ => simp only [itpAfull] at hφ; exact hoth φ hφ hx
        | or C₁ C₂ => simp only [itpAfull] at hφ; exact hoth φ hφ hx
        | ifThen C₁ C₂ => simp only [itpAfull] at hφ; exact hoth φ hφ hx

/-! ### Soundness (Pitts E1/A1)

`itpE p S fuel b Γ` is a consequence of `Γ`, and `itpA p S fuel b Γ C`
suffices for `C` alongside `Γ` — at every fuel *and every budget*.
One mutual fuel induction at the `G4s` level, exactly as for the v2
quantifiers: omission and space guards only remove obligations, the
budget-gated clauses are instances of the ∀-budget induction
hypotheses, and the one new case — the truncation disjunct — opens
with `laxL`, fires its guard by modus ponens against E1 at the inner
fuel, and lands on the same per-disjunct obligations as the main
proof (the `hOTH` bundle below serves both consumers). -/

private theorem memF {F : PLLFormula} {Γ : List PLLFormula} (h : F ∈ Γ) :
    F ∈ Γ.toFinset := List.mem_toFinset.mpr h

set_option maxHeartbeats 4000000 in
theorem itp_sound (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat),
    (∀ b Γ, G4s Γ.toFinset (itpE p S fuel b Γ)) ∧
    (∀ b Γ C, G4s (insert (itpA p S fuel b Γ C) Γ.toFinset) C) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro b Γ
        simp only [itpE]
        exact G4s.truePLL_intro _
      · intro b Γ C
        simp only [itpA]
        exact G4s.botL (Finset.mem_insert_self _ _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- E1: Γ ⊢ itpE p S (fuel+1) b Γ
        intro b Γ
        rw [itpE_succ p S fuel b Γ]
        refine G4s.andAll_intro ?_
        intro φ hφ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              exact G4s.botL (memF hbot)
            next => cases hφ
          · -- the atom clauses
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                · cases heq
                · injection heq with heq'
                  subst heq'
                  exact G4s.init (memF hFΓ)
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih' := ihE b (A :: B :: Γ)
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact G4s.andL (memF hFΓ) ih'
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih₁ := ihE b (A :: Γ)
                  rw [List.toFinset_cons] at ih₁
                  have ih₂ := ihE b (B :: Γ)
                  rw [List.toFinset_cons] at ih₂
                  exact G4s.orL (memF hFΓ) (G4s.orR1 ih₁) (G4s.orR2 ih₂)
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                rcases List.mem_singleton.mp hin with rfl
                have ih' := ihE b (χ :: Γ)
                rw [List.toFinset_cons] at ih'
                exact G4s.laxL (memF hFΓ) (G4s.laxR ih')
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        have ih' := ihE b (B :: Γ)
                        rw [List.toFinset_cons] at ih'
                        exact G4s.impLProp (memF hFΓ) (memF hq) ih'
                      next =>
                        split at hin
                        next => cases hin
                        next =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4s.impR ?_
                          have ih' := ihE b (B :: Γ)
                          rw [List.toFinset_cons] at ih'
                          refine G4s.impLProp
                            (Finset.mem_insert_of_mem (memF hFΓ))
                            (Finset.mem_insert_self _ _) ?_
                          exact ih'.weaken_subset
                            (Finset.insert_subset_insert _
                              (Finset.subset_insert _ _))
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      have ih' := ihE b (A₁.ifThen (B₁.ifThen B) :: Γ)
                      rw [List.toFinset_cons] at ih'
                      exact G4s.impLAnd (memF hFΓ) ih'
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      have ih' := ihE b (A₁.ifThen B :: B₁.ifThen B :: Γ)
                      rw [List.toFinset_cons, List.toFinset_cons] at ih'
                      exact G4s.impLOr (memF hFΓ) ih'
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next =>
                        split at hin
                        next =>
                          -- E8 at a present piece: guard components at
                          -- budget b', continuation at b = b'+1
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine G4s.impR ?_
                              have ihd := ihE (b' + 1) (B :: Γ)
                              rw [List.toFinset_cons] at ihd
                              refine G4s.impLImp
                                (Finset.mem_insert_of_mem (memF hFΓ)) ?_ ?_
                              · refine G4s.mp_adm
                                  (X := itpE p S fuel b' Γ)
                                  (Y := itpA p S fuel b' Γ (A₁.ifThen B₁))
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_self _ _)) ?_ ?_
                                · exact (ihE b' Γ).weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                                · exact (ihA b' Γ
                                      (A₁.ifThen B₁)).weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                              · exact ihd.weaken_subset
                                  (Finset.insert_subset_insert _
                                    (Finset.subset_insert _ _))
                        next => cases hin
                      next =>
                        split at hin
                        next =>
                          -- E8 at a fresh piece: the v2 shape
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4s.impR ?_
                          have ihe' := ihE b (B₁.ifThen B :: Γ)
                          rw [List.toFinset_cons] at ihe'
                          have iha' := ihA b (B₁.ifThen B :: Γ)
                            (A₁.ifThen B₁)
                          rw [List.toFinset_cons] at iha'
                          have ihd := ihE b (B :: Γ)
                          rw [List.toFinset_cons] at ihd
                          refine G4s.impLImp
                            (Finset.mem_insert_of_mem (memF hFΓ)) ?_ ?_
                          · refine G4s.mp_adm
                              (X := itpE p S fuel b (B₁.ifThen B :: Γ))
                              (Y := itpA p S fuel b (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁))
                              (Finset.mem_insert_of_mem
                                (Finset.mem_insert_self _ _)) ?_ ?_
                            · exact ihe'.weaken_subset (by
                                intro y hy
                                simp only [Finset.mem_insert] at hy ⊢
                                tauto)
                            · exact iha'.weaken_subset (by
                                intro y hy
                                simp only [Finset.mem_insert] at hy ⊢
                                tauto)
                          · exact ihd.weaken_subset
                              (Finset.insert_subset_insert _
                                (Finset.subset_insert _ _))
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · -- head clause: bare A(Γ ⇒ A₁) antecedent
                                refine G4s.impR ?_
                                have ihe := ihE (b' + 1) (B :: Γ)
                                rw [List.toFinset_cons] at ihe
                                refine G4s.impLLax
                                  (Finset.mem_insert_of_mem (memF hFΓ))
                                  (ihA b' Γ A₁) ?_
                                exact ihe.weaken_subset
                                  (Finset.insert_subset_insert _
                                    (Finset.subset_insert _ _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                -- γ-clause: the guard is its own witness
                                refine G4s.impR ?_
                                have ihe := ihE (b' + 1) (B :: Γ)
                                rw [List.toFinset_cons] at ihe
                                refine G4s.impLLaxLax
                                  (Finset.mem_insert_of_mem (memF hFΓ))
                                  (Finset.mem_insert_self _ _) ?_ ?_
                                · refine G4s.mp_adm
                                    (X := itpE p S fuel b' Γ)
                                    (Y := itpA p S fuel b' Γ A₁.somehow)
                                    (Finset.mem_insert_self _ _) ?_ ?_
                                  · exact (ihE b' Γ).weaken_subset (by
                                      intro y hy
                                      simp only [Finset.mem_insert] at hy ⊢
                                      tauto)
                                  · exact (ihA b' Γ
                                        A₁.somehow).weaken_subset (by
                                      intro y hy
                                      simp only [Finset.mem_insert] at hy ⊢
                                      tauto)
                                · exact ihe.weaken_subset
                                    (Finset.insert_subset_insert _
                                      (Finset.subset_insert _ _))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next =>
                              injection heq with heq'
                              subst heq'
                              refine G4s.impR ?_
                              have ihe := ihE b (B :: Γ)
                              rw [List.toFinset_cons] at ihe
                              refine G4s.impLLaxLax
                                (Finset.mem_insert_of_mem (memF hFΓ))
                                (Finset.mem_insert_self _ _) ?_ ?_
                              · -- open the Γ-side witness box, then MP
                                refine G4s.laxL
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_of_mem
                                      (memF hXΓ))) ?_
                                have ihe' := ihE b (x :: Γ)
                                rw [List.toFinset_cons] at ihe'
                                have iha' := ihA b (x :: Γ) A₁.somehow
                                rw [List.toFinset_cons] at iha'
                                refine G4s.mp_adm
                                  (X := itpE p S fuel b (x :: Γ))
                                  (Y := itpA p S fuel b (x :: Γ) A₁.somehow)
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_self _ _)) ?_ ?_
                                · exact ihe'.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                                · exact iha'.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                              · exact ihe.weaken_subset
                                  (Finset.insert_subset_insert _
                                    (Finset.subset_insert _ _))
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- A1: itpA p S (fuel+1) b Γ C, Γ ⊢ C
        intro b Γ C
        rw [itpA_succ p S fuel b Γ C]
        -- the goal-directed disjuncts
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel b Γ C,
            G4s (insert φ Γ.toFinset) C := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ
              split at hφ
              · cases hφ
              · rcases List.mem_singleton.mp hφ with rfl
                exact G4s.init (Finset.mem_insert_self _ _)
          | falsePLL => simp only [itpAgoal] at hφ; cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_singleton.mp hφ with rfl
              refine G4s.andL_ins ?_
              refine G4s.andR ?_ ?_
              · exact (ihA b Γ C₁).weaken_subset
                  (Finset.insert_subset_insert _
                    (Finset.subset_insert _ _))
              · exact (ihA b Γ C₂).weaken_subset (Finset.subset_insert _ _)
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact G4s.orR1 (ihA b Γ C₁)
              · rcases List.mem_singleton.mp hφ' with rfl
                exact G4s.orR2 (ihA b Γ C₂)
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ
              split at hφ
              next =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    refine G4s.impR ?_
                    have ihe := ihE b' (C₁ :: Γ)
                    rw [List.toFinset_cons] at ihe
                    have iha := ihA (b' + 1) (C₁ :: Γ) C₂
                    rw [List.toFinset_cons] at iha
                    refine G4s.mp_adm
                      (X := itpE p S fuel b' (C₁ :: Γ))
                      (Y := itpA p S fuel (b' + 1) (C₁ :: Γ) C₂)
                      (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _)) ?_ ?_
                    · exact ihe.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    · exact iha.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
              next =>
                rcases List.mem_singleton.mp hφ with rfl
                refine G4s.impR ?_
                have ihe := ihE b (C₁ :: Γ)
                rw [List.toFinset_cons] at ihe
                have iha := ihA b (C₁ :: Γ) C₂
                rw [List.toFinset_cons] at iha
                refine G4s.mp_adm (X := itpE p S fuel b (C₁ :: Γ))
                  (Y := itpA p S fuel b (C₁ :: Γ) C₂)
                  (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                  ?_ ?_
                · exact ihe.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact iha.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
          | somehow D =>
              simp only [itpAgoal] at hφ
              cases b with
              | zero => cases hφ
              | succ b' =>
                  rcases List.mem_singleton.mp hφ with rfl
                  refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                  refine G4s.mp_adm (X := itpE p S fuel b' Γ)
                    (Y := itpA p S fuel (b' + 1) Γ D)
                    (Finset.mem_insert_self _ _) ?_ ?_
                  · exact (ihE b' Γ).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
                  · exact (G4s.laxR (ihA (b' + 1) Γ D)).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
        -- the context-directed disjuncts
        have hENV : ∀ φ ∈ itpAenv p S fuel b Γ C,
            G4s (insert φ Γ.toFinset) C := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                obtain ⟨hq, hC⟩ := hg
                subst hq
                subst hC
                exact G4s.init (Finset.mem_insert_of_mem (memF hFΓ))
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.andL (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  have ih' := ihA b (A :: B :: Γ) C
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact ih'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next =>
                split at hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.andL_ins ?_
                  refine G4s.orL (Finset.mem_insert_of_mem
                    (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                  · have ihe := ihE b (A :: Γ)
                    rw [List.toFinset_cons] at ihe
                    have iha := ihA b (A :: Γ) C
                    rw [List.toFinset_cons] at iha
                    refine G4s.mp_adm (X := itpE p S fuel b (A :: Γ))
                      (Y := itpA p S fuel b (A :: Γ) C)
                      (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _)) ?_ ?_
                    · exact ihe.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    · exact iha.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                  · have ihe := ihE b (B :: Γ)
                    rw [List.toFinset_cons] at ihe
                    have iha := ihA b (B :: Γ) C
                    rw [List.toFinset_cons] at iha
                    refine G4s.mp_adm (X := itpE p S fuel b (B :: Γ))
                      (Y := itpA p S fuel b (B :: Γ) C)
                      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                        (Finset.mem_insert_self _ _))) ?_ ?_
                    · exact ihe.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    · exact iha.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              · split at hin
                next => cases hin
                next =>
                  rcases List.mem_singleton.mp hin with rfl
                  -- goal is ◯-shaped; open ◯χ, then the clause box
                  refine G4s.laxL
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  refine G4s.laxL
                    (Finset.mem_insert_of_mem
                      (Finset.mem_insert_self _ _)) ?_
                  have ihe := ihE b (χ :: Γ)
                  rw [List.toFinset_cons] at ihe
                  exact G4s.mp_adm (Finset.mem_insert_self _ _)
                    (ihe.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto))
                    ((ihA b (χ :: Γ) _).weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert, List.mem_toFinset,
                        List.mem_cons] at hy ⊢
                      tauto))
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine G4s.impLProp
                          (Finset.mem_insert_of_mem (memF hFΓ))
                          (Finset.mem_insert_of_mem (memF hq)) ?_
                        have ih' := ihA b (B :: Γ) C
                        rw [List.toFinset_cons] at ih'
                        exact ih'.weaken_subset (by
                          intro y hy
                          simp only [Finset.mem_insert] at hy ⊢
                          tauto)
                      next =>
                        split at hin
                        next => cases hin
                        next =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4s.andL_ins ?_
                          refine G4s.impLProp
                            (Finset.mem_insert_of_mem
                              (Finset.mem_insert_of_mem (memF hFΓ)))
                            (Finset.mem_insert_self _ _) ?_
                          have ih' := ihA b (B :: Γ) C
                          rw [List.toFinset_cons] at ih'
                          exact ih'.weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4s.impLAnd
                        (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                      have ih' := ihA b (A₁.ifThen (B₁.ifThen B) :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4s.impLOr
                        (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                      have ih' := ihA b (A₁.ifThen B :: B₁.ifThen B :: Γ) C
                      rw [List.toFinset_cons, List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      split at hin
                      next =>
                        split at hin
                        next =>
                          -- present piece: guard components at budget b'
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine G4s.andL_ins ?_
                              refine G4s.impLImp
                                (Finset.mem_insert_of_mem
                                  (Finset.mem_insert_of_mem (memF hFΓ)))
                                ?_ ?_
                              · refine G4s.mp_adm
                                  (X := itpE p S fuel b' Γ)
                                  (Y := itpA p S fuel b' Γ (A₁.ifThen B₁))
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_self _ _)) ?_ ?_
                                · exact (ihE b' Γ).weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                                · exact (ihA b' Γ
                                      (A₁.ifThen B₁)).weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                              · have ih' := ihA (b' + 1) (B :: Γ) C
                                rw [List.toFinset_cons] at ih'
                                exact ih'.weaken_subset (by
                                  intro y hy
                                  simp only [Finset.mem_insert] at hy ⊢
                                  tauto)
                        next => cases hin
                      next =>
                        split at hin
                        next =>
                          -- fresh piece: the v2 shape
                          rcases List.mem_singleton.mp hin with rfl
                          refine G4s.andL_ins ?_
                          refine G4s.impLImp
                            (Finset.mem_insert_of_mem
                              (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                          · have ihe := ihE b (B₁.ifThen B :: Γ)
                            rw [List.toFinset_cons] at ihe
                            have iha := ihA b (B₁.ifThen B :: Γ)
                              (A₁.ifThen B₁)
                            rw [List.toFinset_cons] at iha
                            refine G4s.mp_adm
                              (X := itpE p S fuel b (B₁.ifThen B :: Γ))
                              (Y := itpA p S fuel b (B₁.ifThen B :: Γ)
                                (A₁.ifThen B₁))
                              (Finset.mem_insert_of_mem
                                (Finset.mem_insert_self _ _)) ?_ ?_
                            · exact ihe.weaken_subset (by
                                intro y hy
                                simp only [Finset.mem_insert] at hy ⊢
                                tauto)
                            · exact iha.weaken_subset (by
                                intro y hy
                                simp only [Finset.mem_insert] at hy ⊢
                                tauto)
                          · have ih' := ihA b (B :: Γ) C
                            rw [List.toFinset_cons] at ih'
                            exact ih'.weaken_subset (by
                              intro y hy
                              simp only [Finset.mem_insert] at hy ⊢
                              tauto)
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next =>
                    split at hin
                    next =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · -- head: A(Γ ⇒ A₁) ∧ A(B::Γ ⇒ C)
                                refine G4s.andL_ins ?_
                                refine G4s.impLLax
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_of_mem (memF hFΓ)))
                                  ?_ ?_
                                · exact (ihA b' Γ A₁).weaken_subset
                                    (Finset.insert_subset_insert _
                                      (Finset.subset_insert _ _))
                                · have ih' := ihA (b' + 1) (B :: Γ) C
                                  rw [List.toFinset_cons] at ih'
                                  exact ih'.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                              · rcases List.mem_singleton.mp hin' with rfl
                                -- γ-form: the ◯-guard is its own witness
                                refine G4s.andL_ins ?_
                                refine G4s.impLLaxLax
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_of_mem (memF hFΓ)))
                                  (Finset.mem_insert_self _ _) ?_ ?_
                                · refine G4s.mp_adm
                                    (X := itpE p S fuel b' Γ)
                                    (Y := itpA p S fuel b' Γ A₁.somehow)
                                    (Finset.mem_insert_self _ _) ?_ ?_
                                  · exact (ihE b' Γ).weaken_subset (by
                                      intro y hy
                                      simp only [Finset.mem_insert] at hy ⊢
                                      tauto)
                                  · exact (ihA b' Γ
                                        A₁.somehow).weaken_subset (by
                                      intro y hy
                                      simp only [Finset.mem_insert] at hy ⊢
                                      tauto)
                                · have ih' := ihA (b' + 1) (B :: Γ) C
                                  rw [List.toFinset_cons] at ih'
                                  exact ih'.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next =>
                              injection heq with heq'
                              subst heq'
                              refine G4s.andL_ins ?_
                              refine G4s.impLLaxLax
                                (Finset.mem_insert_of_mem
                                  (Finset.mem_insert_of_mem (memF hFΓ)))
                                (Finset.mem_insert_self _ _) ?_ ?_
                              · -- open the Γ-side box, then MP
                                refine G4s.laxL
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_of_mem
                                      (Finset.mem_insert_of_mem
                                        (memF hXΓ)))) ?_
                                have ihe := ihE b (x :: Γ)
                                rw [List.toFinset_cons] at ihe
                                have iha := ihA b (x :: Γ) A₁.somehow
                                rw [List.toFinset_cons] at iha
                                refine G4s.mp_adm
                                  (X := itpE p S fuel b (x :: Γ))
                                  (Y := itpA p S fuel b (x :: Γ) A₁.somehow)
                                  (Finset.mem_insert_of_mem
                                    (Finset.mem_insert_self _ _)) ?_ ?_
                                · exact ihe.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                                · exact iha.weaken_subset (by
                                    intro y hy
                                    simp only [Finset.mem_insert] at hy ⊢
                                    tauto)
                              · have ih' := ihA b (B :: Γ) C
                                rw [List.toFinset_cons] at ih'
                                exact ih'.weaken_subset (by
                                  intro y hy
                                  simp only [Finset.mem_insert] at hy ⊢
                                  tauto)
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        -- the undecorated table, bundled once: consumed by both the
        -- main disjunct cases and the truncation case
        have hOTH : ∀ φ ∈ itpAoth p S fuel b Γ C,
            G4s (insert φ Γ.toFinset) C := by
          intro φ hφ
          simp only [itpAoth] at hφ
          rcases List.mem_append.mp hφ with hφ | hφ
          · exact hGOAL φ hφ
          · exact hENV φ hφ
        refine G4s.orAll_elim ?_
        intro φ hφ
        cases C with
        | somehow D =>
            simp only [itpAfull] at hφ
            rcases List.mem_append.mp hφ with hφ | hφ
            · exact hOTH φ hφ
            · -- the truncation disjunct: open with laxL, fire the
              -- guard by MP against E1 at (fuel, b'), then land on
              -- the bundled per-disjunct obligations
              split at hφ
              next => cases hφ
              next =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                    refine G4s.mp_adm (X := itpE p S fuel b' Γ)
                      (Y := orAll (itpAoth p S fuel (b' + 1) Γ D.somehow))
                      (Finset.mem_insert_self _ _) ?_ ?_
                    · exact (ihE b' Γ).weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                    · refine G4s.orAll_elim ?_
                      intro ψ hψ
                      exact (hOTH ψ hψ).weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
        | prop q => simp only [itpAfull] at hφ; exact hOTH φ hφ
        | falsePLL => simp only [itpAfull] at hφ; exact hOTH φ hφ
        | and C₁ C₂ => simp only [itpAfull] at hφ; exact hOTH φ hφ
        | or C₁ C₂ => simp only [itpAfull] at hφ; exact hOTH φ hφ
        | ifThen C₁ C₂ => simp only [itpAfull] at hφ; exact hOTH φ hφ

/-! ### Set-congruence

`itpE`/`itpA` respect context-set equality up to provable
equivalence, at every fuel and budget: set-equal contexts yield
clause tables whose members are pointwise inter-derivable (same
principals, transported guards, congruent subcontexts).  One
direction suffices — the statement is ∀-quantified over both lists,
so the symmetric instance supplies the contravariant positions (the
`(E ⇢ A)`-guard antecedents and the truncation disjunct's `E`-feed).
This is the v3 counterpart of `inter_congr`, and the entry ticket for
the absorption lemma: seen-state arguments may treat the finitely
many context-*sets* as the true state space. -/

/-- Two-context version of `itpAfull_box_map`: the ◯-goal disjunction
with its truncation disjunct, mapped member-wise across two (not
necessarily equal) contexts.  Nonemptiness of the `others` transfers
through the mapping; `htr` feeds the contravariant `E`-guard of the
truncation disjunct. -/
theorem itpAfull_box_map₂ {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ₁ Γ₂ : List PLLFormula} {D : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ₁ (D.somehow),
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ₂ (D.somehow), G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ₂] (itpE p S f₁ b₁' Γ₁)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ₁ (D.somehow))]
        (orAll (itpAfull p S f₂ b₂ Γ₂ (D.somehow))) := by
  simp only [itpAfull]
  refine G4c.orAll_elim ?_
  intro φ hφ
  rcases List.mem_append.mp hφ with hφ | hφ
  · obtain ⟨ψ, hψ, hd⟩ := hoth φ hφ
    exact G4c.orAll_intro (List.mem_append.mpr (Or.inl hψ)) hd
  · by_cases h1 : (itpAoth p S f₁ b₁ Γ₁ (D.somehow)).isEmpty = true
    · rw [if_pos h1] at hφ; cases hφ
    · rw [if_neg h1] at hφ
      cases b₁ with
      | zero => cases hφ
      | succ b₁' =>
          rcases List.mem_singleton.mp hφ with rfl
          obtain ⟨b₂', rfl, hE⟩ := htr b₁' rfl
          have h2 : ¬ (itpAoth p S f₂ (b₂' + 1) Γ₂ (D.somehow)).isEmpty = true := by
            intro h2
            have h2' : itpAoth p S f₂ (b₂' + 1) Γ₂ (D.somehow) = [] := by
              simpa using h2
            cases hl : itpAoth p S f₁ (b₁' + 1) Γ₁ (D.somehow) with
            | nil => rw [hl] at h1; simp at h1
            | cons a t =>
                obtain ⟨ψ, hψ, -⟩ := hoth a (by rw [hl]; exact .head _)
                rw [h2'] at hψ; cases hψ
          refine G4c.orAll_intro ?_ (box_mono (imp_mono hE (orAll_map hoth)))
          refine List.mem_append.mpr (Or.inr ?_)
          rw [if_neg h2]
          exact .head _

/-- Two-context version of `itpAfull_map`: dispatch on the goal shape
(the truncation disjunct exists only for ◯-goals). -/
theorem itpAfull_map₂ {p : String} {S : Finset PLLFormula}
    {f₁ b₁ f₂ b₂ : Nat} {Γ₁ Γ₂ : List PLLFormula} {C : PLLFormula}
    (hoth : ∀ φ ∈ itpAoth p S f₁ b₁ Γ₁ C,
        ∃ ψ ∈ itpAoth p S f₂ b₂ Γ₂ C, G4c [φ] ψ)
    (htr : ∀ b₁', b₁ = b₁' + 1 → ∃ b₂', b₂ = b₂' + 1 ∧
        G4c [itpE p S f₂ b₂' Γ₂] (itpE p S f₁ b₁' Γ₁)) :
    G4c [orAll (itpAfull p S f₁ b₁ Γ₁ C)]
        (orAll (itpAfull p S f₂ b₂ Γ₂ C)) := by
  cases C with
  | somehow D => exact itpAfull_box_map₂ hoth htr
  | prop q => simp only [itpAfull]; exact orAll_map hoth
  | falsePLL => simp only [itpAfull]; exact orAll_map hoth
  | and C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | or C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth
  | ifThen C₁ C₂ => simp only [itpAfull]; exact orAll_map hoth

set_option maxHeartbeats 4000000 in
/-- **Set-congruence** of the truncated quantifiers, one direction
(the symmetric instance gives the other). -/
theorem itp_congr (p : String) (S : Finset PLLFormula) : ∀ (fuel : Nat),
    (∀ b Γ₁ Γ₂, Γ₁.toFinset = Γ₂.toFinset →
      G4c [itpE p S fuel b Γ₁] (itpE p S fuel b Γ₂)) ∧
    (∀ b Γ₁ Γ₂ C, Γ₁.toFinset = Γ₂.toFinset →
      G4c [itpA p S fuel b Γ₁ C] (itpA p S fuel b Γ₂ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro b Γ₁ Γ₂ _
        simp only [itpE]
        exact G4c.truePLL_intro _
      · intro b Γ₁ Γ₂ C _
        simp only [itpA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- E-side: [itpE p S (fuel+1) b Γ₁] ⊢ itpE p S (fuel+1) b Γ₂
        intro b Γ₁ Γ₂ hset
        have hg : ∀ (G : PLLFormula), G ∈ Γ₁ ↔ G ∈ Γ₂ := by
          intro G
          simp only [← List.mem_toFinset]
          rw [hset]
        have hset1 : ∀ (X : PLLFormula),
            (X :: Γ₁).toFinset = (X :: Γ₂).toFinset := by
          intro X
          rw [List.toFinset_cons, List.toFinset_cons, hset]
        have hset2 : ∀ (X Y : PLLFormula),
            (X :: Y :: Γ₁).toFinset = (X :: Y :: Γ₂).toFinset := by
          intro X Y
          simp only [List.toFinset_cons, hset]
        rw [itpE_succ p S fuel b Γ₁, itpE_succ p S fuel b Γ₂]
        refine andAll_map ?_
        intro φ hφ
        simp only [itpEcls] at hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine ⟨falsePLL, ?_, G4c.botL (.head _)⟩
              simp only [itpEcls]
              exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
                (Or.inl (by rw [if_pos ((hg _).mpr hbot)]; exact .head _))))
            next => cases hφ
          · -- the atom clauses
            obtain ⟨F, hFΓ, heq⟩ := List.mem_filterMap.mp hφ
            cases F with
            | prop q =>
                simp only at heq
                split at heq
                next => cases heq
                next hq =>
                  injection heq with heq'
                  subst heq'
                  refine ⟨prop q, ?_, G4c.init (.head _)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inl (List.mem_append.mpr
                    (Or.inr (List.mem_filterMap.mpr
                      ⟨prop q, (hg _).mpr hFΓ, ?_⟩))))
                  simp only
                  rw [if_neg hq]
            | falsePLL => cases heq
            | and _ _ => cases heq
            | or _ _ => cases heq
            | ifThen _ _ => cases heq
            | somehow _ => cases heq
        · -- the rule clauses: same principal, transported guards,
          -- congruent subcontexts
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          have hF₁ : F ∈ Γ₁ := (hg _).mpr hFΓ
          cases F with
          | prop _ => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  have h1' : ¬(A ∈ Γ₁ ∧ B ∈ Γ₁) :=
                    fun hc => h1 ⟨(hg _).mp hc.1, (hg _).mp hc.2⟩
                  have h2' : (A ∈ Γ₁ ∨ A ∈ S) ∧ (B ∈ Γ₁ ∨ B ∈ S) :=
                    ⟨h2.1.imp (hg _).mpr id, h2.2.imp (hg _).mpr id⟩
                  refine ⟨_, ?_,
                    ihE b (A :: B :: Γ₁) (A :: B :: Γ₂) (hset2 A B)⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.and B, hF₁, ?_⟩))
                  simp only
                  rw [if_neg h1', if_pos h2']
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  have h1' : ¬(A ∈ Γ₁ ∨ B ∈ Γ₁) :=
                    fun hc => h1 (hc.imp (hg _).mp (hg _).mp)
                  refine ⟨_, ?_, or_mono
                    (ihE b (A :: Γ₁) (A :: Γ₂) (hset1 A))
                    (ihE b (B :: Γ₁) (B :: Γ₂) (hset1 B))⟩
                  simp only [itpEcls]
                  refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨A.or B, hF₁, ?_⟩))
                  simp only
                  rw [if_neg h1', if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              next => cases hin
              next hng =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨_, ?_, box_mono
                  (ihE b (χ :: Γ₁) (χ :: Γ₂) (hset1 χ))⟩
                simp only [itpEcls]
                refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                  ⟨χ.somehow, hF₁, ?_⟩))
                simp only
                rw [if_neg (fun hc => hng (hc.imp (hg _).mp id))]
                exact .head _
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_,
                          ihE b (B :: Γ₁) (B :: Γ₂) (hset1 B)⟩
                        simp only [itpEcls]
                        refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hF₁, ?_⟩))
                        simp only
                        rw [if_neg (fun hc => hBΓ ((hg _).mp hc)),
                          if_pos hBS, if_pos ((hg _).mpr hq)]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono (G4c.init (.head _))
                            (ihE b (B :: Γ₁) (B :: Γ₂) (hset1 B))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF₁, ?_⟩))
                          simp only
                          rw [if_neg (fun hc => hBΓ ((hg _).mp hc)),
                            if_pos hBS,
                            if_neg (fun hc => hq ((hg _).mp hc)), if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihE b
                        (A₁.ifThen (B₁.ifThen B) :: Γ₁)
                        (A₁.ifThen (B₁.ifThen B) :: Γ₂) (hset1 _)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hF₁, ?_⟩))
                      simp only
                      rw [if_neg (fun hc => h1 ((hg _).mp hc)), if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      have h1' : ¬(A₁.ifThen B ∈ Γ₁ ∧ B₁.ifThen B ∈ Γ₁) :=
                        fun hc => h1 ⟨(hg _).mp hc.1, (hg _).mp hc.2⟩
                      have h2' : (A₁.ifThen B ∈ Γ₁ ∨ A₁.ifThen B ∈ S) ∧
                          (B₁.ifThen B ∈ Γ₁ ∨ B₁.ifThen B ∈ S) :=
                        ⟨h2.1.imp (hg _).mpr id, h2.2.imp (hg _).mpr id⟩
                      refine ⟨_, ?_, ihE b
                        (A₁.ifThen B :: B₁.ifThen B :: Γ₁)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ₂) (hset2 _ _)⟩
                      simp only [itpEcls]
                      refine List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hF₁, ?_⟩))
                      simp only
                      rw [if_neg h1', if_pos h2']
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, imp_mono
                                (imp_mono (ihE b' Γ₁ Γ₂ hset)
                                  (ihA b' Γ₂ Γ₁ (A₁.ifThen B₁) hset.symm))
                                (ihE (b' + 1) (B :: Γ₁) (B :: Γ₂) (hset1 B))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨(A₁.ifThen B₁).ifThen B, hF₁, ?_⟩))
                              simp only
                              rw [if_neg (fun hc => hDΓ ((hg _).mp hc)),
                                if_pos hDS, if_pos ((hg _).mpr hBD),
                                if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, imp_mono
                            (imp_mono
                              (ihE b (B₁.ifThen B :: Γ₁)
                                (B₁.ifThen B :: Γ₂) (hset1 _))
                              (ihA b (B₁.ifThen B :: Γ₂)
                                (B₁.ifThen B :: Γ₁) (A₁.ifThen B₁)
                                (hset1 _).symm))
                            (ihE b (B :: Γ₁) (B :: Γ₂) (hset1 B))⟩
                          simp only [itpEcls]
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨(A₁.ifThen B₁).ifThen B, hF₁, ?_⟩))
                          simp only
                          rw [if_neg (fun hc => hDΓ ((hg _).mp hc)),
                            if_pos hDS,
                            if_neg (fun hc => hBD ((hg _).mp hc)),
                            if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, imp_mono
                                  (ihA b' Γ₂ Γ₁ A₁ hset.symm)
                                  (ihE (b' + 1) (B :: Γ₁) (B :: Γ₂)
                                    (hset1 B))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hF₁, ?_⟩))
                                simp only
                                rw [if_neg (fun hc => hBΓ ((hg _).mp hc)),
                                  if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, imp_mono
                                  (box_mono (imp_mono (ihE b' Γ₁ Γ₂ hset)
                                    (ihA b' Γ₂ Γ₁ A₁.somehow hset.symm)))
                                  (ihE (b' + 1) (B :: Γ₁) (B :: Γ₂)
                                    (hset1 B))⟩
                                simp only [itpEcls]
                                refine List.mem_append.mpr (Or.inr
                                  (List.mem_flatMap.mpr
                                    ⟨A₁.somehow.ifThen B, hF₁, ?_⟩))
                                simp only
                                rw [if_neg (fun hc => hBΓ ((hg _).mp hc)),
                                  if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hng =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, imp_mono
                                (box_mono (imp_mono
                                  (ihE b (x :: Γ₁) (x :: Γ₂) (hset1 x))
                                  (ihA b (x :: Γ₂) (x :: Γ₁) A₁.somehow
                                    (hset1 x).symm)))
                                (ihE b (B :: Γ₁) (B :: Γ₂) (hset1 B))⟩
                              simp only [itpEcls]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF₁, ?_⟩))
                              simp only
                              rw [if_neg (fun hc => hBΓ ((hg _).mp hc)),
                                if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr
                                  ⟨x.somehow, (hg _).mpr hXΓ, ?_⟩))
                              simp only
                              rw [if_neg (fun hc => hng
                                (hc.imp (hg _).mp id))]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
      · -- A-side: [itpA p S (fuel+1) b Γ₁ C] ⊢ itpA p S (fuel+1) b Γ₂ C
        intro b Γ₁ Γ₂ C hset
        have hg : ∀ (G : PLLFormula), G ∈ Γ₁ ↔ G ∈ Γ₂ := by
          intro G
          simp only [← List.mem_toFinset]
          rw [hset]
        have hset1 : ∀ (X : PLLFormula),
            (X :: Γ₁).toFinset = (X :: Γ₂).toFinset := by
          intro X
          rw [List.toFinset_cons, List.toFinset_cons, hset]
        have hset2 : ∀ (X Y : PLLFormula),
            (X :: Y :: Γ₁).toFinset = (X :: Y :: Γ₂).toFinset := by
          intro X Y
          simp only [List.toFinset_cons, hset]
        rw [itpA_succ p S fuel b Γ₁ C, itpA_succ p S fuel b Γ₂ C]
        have hGOAL : ∀ φ ∈ itpAgoal p S fuel b Γ₁ C,
            ∃ ψ ∈ itpAgoal p S fuel b Γ₂ C, G4c [φ] ψ := by
          intro φ hφ
          cases C with
          | prop q =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨prop q, ?_, G4c.init (.head _)⟩
                rw [if_neg hq]
                exact .head _
          | falsePLL =>
              simp only [itpAgoal] at hφ
              cases hφ
          | and C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_singleton.mp hφ with rfl
              exact ⟨_, .head _, and_mono (ihA b Γ₁ Γ₂ C₁ hset)
                (ihA b Γ₁ Γ₂ C₂ hset)⟩
          | or C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact ⟨_, .head _, ihA b Γ₁ Γ₂ C₁ hset⟩
              · rcases List.mem_singleton.mp hφ' with rfl
                exact ⟨_, .tail _ (.head _), ihA b Γ₁ Γ₂ C₂ hset⟩
          | ifThen C₁ C₂ =>
              simp only [itpAgoal] at hφ ⊢
              split at hφ
              next hpres =>
                cases b with
                | zero => cases hφ
                | succ b' =>
                    rcases List.mem_singleton.mp hφ with rfl
                    refine ⟨_, ?_, imp_mono
                      (ihE b' (C₁ :: Γ₂) (C₁ :: Γ₁) (hset1 C₁).symm)
                      (ihA (b' + 1) (C₁ :: Γ₁) (C₁ :: Γ₂) C₂ (hset1 C₁))⟩
                    rw [if_pos ((hg _).mp hpres)]
                    exact .head _
              next hpres =>
                rcases List.mem_singleton.mp hφ with rfl
                refine ⟨_, ?_, imp_mono
                  (ihE b (C₁ :: Γ₂) (C₁ :: Γ₁) (hset1 C₁).symm)
                  (ihA b (C₁ :: Γ₁) (C₁ :: Γ₂) C₂ (hset1 C₁))⟩
                rw [if_neg (fun hc => hpres ((hg _).mpr hc))]
                exact .head _
          | somehow D =>
              simp only [itpAgoal] at hφ ⊢
              cases b with
              | zero => cases hφ
              | succ b' =>
                  rcases List.mem_singleton.mp hφ with rfl
                  exact ⟨_, .head _, box_mono
                    (imp_mono (ihE b' Γ₂ Γ₁ hset.symm)
                      (ihA (b' + 1) Γ₁ Γ₂ D hset))⟩
        have hENV : ∀ φ ∈ itpAenv p S fuel b Γ₁ C,
            ∃ ψ ∈ itpAenv p S fuel b Γ₂ C, G4c [φ] ψ := by
          intro φ hφ
          simp only [itpAenv] at hφ
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          have hF₂ : F ∈ Γ₂ := (hg _).mp hFΓ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hgd =>
                rcases List.mem_singleton.mp hin with rfl
                refine ⟨truePLL, ?_, G4c.truePLL_intro _⟩
                simp only [itpAenv]
                refine List.mem_flatMap.mpr ⟨prop q, hF₂, ?_⟩
                simp only
                rw [if_pos hgd]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  have h1' : ¬(A ∈ Γ₂ ∧ B ∈ Γ₂) :=
                    fun hc => h1 ⟨(hg _).mpr hc.1, (hg _).mpr hc.2⟩
                  have h2' : (A ∈ Γ₂ ∨ A ∈ S) ∧ (B ∈ Γ₂ ∨ B ∈ S) :=
                    ⟨h2.1.imp (hg _).mp id, h2.2.imp (hg _).mp id⟩
                  refine ⟨_, ?_,
                    ihA b (A :: B :: Γ₁) (A :: B :: Γ₂) C (hset2 A B)⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.and B, hF₂, ?_⟩
                  simp only
                  rw [if_neg h1', if_pos h2']
                  exact .head _
                next => cases hin
          | or A B =>
              simp only at hin
              split at hin
              next => cases hin
              next h1 =>
                split at hin
                next h2 =>
                  rcases List.mem_singleton.mp hin with rfl
                  have h1' : ¬(A ∈ Γ₂ ∨ B ∈ Γ₂) :=
                    fun hc => h1 (hc.imp (hg _).mpr (hg _).mpr)
                  refine ⟨_, ?_, and_mono
                    (imp_mono (ihE b (A :: Γ₂) (A :: Γ₁) (hset1 A).symm)
                      (ihA b (A :: Γ₁) (A :: Γ₂) C (hset1 A)))
                    (imp_mono (ihE b (B :: Γ₂) (B :: Γ₁) (hset1 B).symm)
                      (ihA b (B :: Γ₁) (B :: Γ₂) C (hset1 B)))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨A.or B, hF₂, ?_⟩
                  simp only
                  rw [if_neg h1', if_pos h2]
                  exact .head _
                next => cases hin
          | somehow χ =>
              simp only at hin
              split at hin
              · split at hin
                next => cases hin
                next hng =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine ⟨_, ?_, box_mono
                    (imp_mono (ihE b (χ :: Γ₂) (χ :: Γ₁) (hset1 χ).symm)
                      (ihA b (χ :: Γ₁) (χ :: Γ₂) _ (hset1 χ)))⟩
                  simp only [itpAenv]
                  refine List.mem_flatMap.mpr ⟨χ.somehow, hF₂, ?_⟩
                  simp only
                  rw [if_neg (fun hc => hng (hc.imp (hg _).mpr id))]
                  exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      split at hin
                      next hq =>
                        rcases List.mem_singleton.mp hin with rfl
                        refine ⟨_, ?_,
                          ihA b (B :: Γ₁) (B :: Γ₂) C (hset1 B)⟩
                        simp only [itpAenv]
                        refine List.mem_flatMap.mpr
                          ⟨(prop q).ifThen B, hF₂, ?_⟩
                        simp only
                        rw [if_neg (fun hc => hBΓ ((hg _).mpr hc)),
                          if_pos hBS, if_pos ((hg _).mp hq)]
                        exact .head _
                      next hq =>
                        split at hin
                        next => cases hin
                        next hqp =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono (G4c.init (.head _))
                            (ihA b (B :: Γ₁) (B :: Γ₂) C (hset1 B))⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(prop q).ifThen B, hF₂, ?_⟩
                          simp only
                          rw [if_neg (fun hc => hBΓ ((hg _).mpr hc)),
                            if_pos hBS,
                            if_neg (fun hc => hq ((hg _).mpr hc)),
                            if_neg hqp]
                          exact .head _
                    next => cases hin
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine ⟨_, ?_, ihA b
                        (A₁.ifThen (B₁.ifThen B) :: Γ₁)
                        (A₁.ifThen (B₁.ifThen B) :: Γ₂) C (hset1 _)⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.and B₁).ifThen B, hF₂, ?_⟩
                      simp only
                      rw [if_neg (fun hc => h1 ((hg _).mpr hc)), if_pos h2]
                      exact .head _
                    next => cases hin
              | or A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next h1 =>
                    split at hin
                    next h2 =>
                      rcases List.mem_singleton.mp hin with rfl
                      have h1' : ¬(A₁.ifThen B ∈ Γ₂ ∧ B₁.ifThen B ∈ Γ₂) :=
                        fun hc => h1 ⟨(hg _).mpr hc.1, (hg _).mpr hc.2⟩
                      have h2' : (A₁.ifThen B ∈ Γ₂ ∨ A₁.ifThen B ∈ S) ∧
                          (B₁.ifThen B ∈ Γ₂ ∨ B₁.ifThen B ∈ S) :=
                        ⟨h2.1.imp (hg _).mp id, h2.2.imp (hg _).mp id⟩
                      refine ⟨_, ?_, ihA b
                        (A₁.ifThen B :: B₁.ifThen B :: Γ₁)
                        (A₁.ifThen B :: B₁.ifThen B :: Γ₂) C (hset2 _ _)⟩
                      simp only [itpAenv]
                      refine List.mem_flatMap.mpr
                        ⟨(A₁.or B₁).ifThen B, hF₂, ?_⟩
                      simp only
                      rw [if_neg h1', if_pos h2']
                      exact .head _
                    next => cases hin
              | ifThen A₁ B₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hDΓ =>
                    split at hin
                    next hDS =>
                      split at hin
                      next hBD =>
                        split at hin
                        next hABD =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_singleton.mp hin with rfl
                              refine ⟨_, ?_, and_mono
                                (imp_mono (ihE b' Γ₂ Γ₁ hset.symm)
                                  (ihA b' Γ₁ Γ₂ (A₁.ifThen B₁) hset))
                                (ihA (b' + 1) (B :: Γ₁) (B :: Γ₂) C
                                  (hset1 B))⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨(A₁.ifThen B₁).ifThen B, hF₂, ?_⟩
                              simp only
                              rw [if_neg (fun hc => hDΓ ((hg _).mpr hc)),
                                if_pos hDS, if_pos ((hg _).mp hBD),
                                if_pos hABD]
                              exact .head _
                        next => cases hin
                      next hBD =>
                        split at hin
                        next hBDS =>
                          rcases List.mem_singleton.mp hin with rfl
                          refine ⟨_, ?_, and_mono
                            (imp_mono
                              (ihE b (B₁.ifThen B :: Γ₂)
                                (B₁.ifThen B :: Γ₁) (hset1 _).symm)
                              (ihA b (B₁.ifThen B :: Γ₁)
                                (B₁.ifThen B :: Γ₂) (A₁.ifThen B₁)
                                (hset1 _)))
                            (ihA b (B :: Γ₁) (B :: Γ₂) C (hset1 B))⟩
                          simp only [itpAenv]
                          refine List.mem_flatMap.mpr
                            ⟨(A₁.ifThen B₁).ifThen B, hF₂, ?_⟩
                          simp only
                          rw [if_neg (fun hc => hDΓ ((hg _).mpr hc)),
                            if_pos hDS,
                            if_neg (fun hc => hBD ((hg _).mpr hc)),
                            if_pos hBDS]
                          exact .head _
                        next => cases hin
                    next => cases hin
              | somehow A₁ =>
                  simp only at hin
                  split at hin
                  next => cases hin
                  next hBΓ =>
                    split at hin
                    next hBS =>
                      rcases List.mem_append.mp hin with hin | hin
                      · split at hin
                        next hAS =>
                          cases b with
                          | zero => cases hin
                          | succ b' =>
                              rcases List.mem_cons.mp hin with rfl | hin'
                              · refine ⟨_, ?_, and_mono
                                  (ihA b' Γ₁ Γ₂ A₁ hset)
                                  (ihA (b' + 1) (B :: Γ₁) (B :: Γ₂) C
                                    (hset1 B))⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF₂, ?_⟩
                                simp only
                                rw [if_neg (fun hc => hBΓ ((hg _).mpr hc)),
                                  if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr (Or.inl (.head _))
                              · rcases List.mem_singleton.mp hin' with rfl
                                refine ⟨_, ?_, and_mono
                                  (box_mono (imp_mono
                                    (ihE b' Γ₂ Γ₁ hset.symm)
                                    (ihA b' Γ₁ Γ₂ A₁.somehow hset)))
                                  (ihA (b' + 1) (B :: Γ₁) (B :: Γ₂) C
                                    (hset1 B))⟩
                                simp only [itpAenv]
                                refine List.mem_flatMap.mpr
                                  ⟨A₁.somehow.ifThen B, hF₂, ?_⟩
                                simp only
                                rw [if_neg (fun hc => hBΓ ((hg _).mpr hc)),
                                  if_pos hBS, if_pos hAS]
                                exact List.mem_append.mpr
                                  (Or.inl (.tail _ (.head _)))
                        next => cases hin
                      · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin
                        cases X with
                        | somehow x =>
                            simp only at heq
                            split at heq
                            next => cases heq
                            next hng =>
                              injection heq with heq'
                              subst heq'
                              refine ⟨_, ?_, and_mono
                                (box_mono (imp_mono
                                  (ihE b (x :: Γ₂) (x :: Γ₁)
                                    (hset1 x).symm)
                                  (ihA b (x :: Γ₁) (x :: Γ₂) A₁.somehow
                                    (hset1 x))))
                                (ihA b (B :: Γ₁) (B :: Γ₂) C (hset1 B))⟩
                              simp only [itpAenv]
                              refine List.mem_flatMap.mpr
                                ⟨A₁.somehow.ifThen B, hF₂, ?_⟩
                              simp only
                              rw [if_neg (fun hc => hBΓ ((hg _).mpr hc)),
                                if_pos hBS]
                              refine List.mem_append.mpr (Or.inr
                                (List.mem_filterMap.mpr
                                  ⟨x.somehow, (hg _).mp hXΓ, ?_⟩))
                              simp only
                              rw [if_neg (fun hc => hng
                                (hc.imp (hg _).mpr id))]
                        | prop _ => cases heq
                        | falsePLL => cases heq
                        | and _ _ => cases heq
                        | or _ _ => cases heq
                        | ifThen _ _ => cases heq
                    next => cases hin
        exact itpAfull_map₂ (map_append hGOAL hENV)
          (fun b' hb => ⟨b', hb, ihE b' Γ₂ Γ₁ hset.symm⟩)

end PLLND
