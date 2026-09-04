import LaxLogic.PLLConfluence

/-!
# Idempotence is inter-derivability, not isomorphism

`◯◯M ⊣⊢ ◯M` is witnessed by two proof terms: the multiplication

  `μ = λx. let val y ⇐ x in y  :  ◯◯M ⊃ ◯M`

and the unit at `◯M`

  `η = λx. val x  :  ◯M ⊃ ◯◯M`.

This file machine-checks that they are **not mutually inverse** under
the reduction of `PLLTerms.lean`:

* `μ ∘ η` reduces to the identity — the monad's unit law
  `μ ∘ η_{◯M} = id`, holding as computation (the `let` fires on the
  `val`);
* `η ∘ μ` does **not**: it normalises to the re-thunked term
  `λx. val (let val y ⇐ x in y)`, which is stuck — `x` is an opaque
  variable, so the `let` cannot fire and the outer `val` freezes it —
  and the composite's complete reduction graph is computed here to be
  exactly four terms, none of them the identity
  (`not_steps_eta_mu_id`).  In particular the composite and the
  identity have no common reduct (`eta_mu_id_not_joinable`).

So the two directions of idempotence are different operations on
evidence: collapsing a belief about a belief and then re-asserting
belief in the result is not a null operation.  In monad-theoretic
terms, `η` is a section of `μ` up to reduction, but not an inverse —
the proof-term monad is not idempotent as a monad, although `◯◯M` and
`◯M` are inter-derivable.  (If `μ` had *any* two-sided inverse up to
reduction it would have to be its section `η`, so this single failure
refutes invertibility of `μ` outright.)

Both normal forms are computed by the certified fuelled normaliser
`Tm.reduceFuel` of `PLLStrongNorm.lean`, by `rfl`, uniformly in `M`;
`Tm.reduceFuel_sound` then delivers the `Steps` and `Nf` facts for
free.  With confluence (`PLLConfluence.lean`) the separation also
holds up to the full equivalence closure of reduction:
`eta_mu_not_conv_id`.  The reduction-graph argument is kept as well
because it is unconditional and choice-free (`[propext]`); the
conversion-level statement inherits `Classical.choice` from the
strong-normalisation theorem behind Newman's lemma.
-/

open PLLFormula

namespace PLLND

variable (M : PLLFormula)

/-- The multiplication `μ : ◯◯M ⊃ ◯M` — `λx. let val y ⇐ x in y`.
(Under Curry–Howard, `(muTm M).toND` is the idempotence derivation.) -/
def muTm : Tm [] ((somehow (somehow M)).ifThen (somehow M)) :=
  .lam (.bind (.var .here) (.var .here))

/-- The unit at `◯M`, `η : ◯M ⊃ ◯◯M` — `λx. val x`. -/
def etaTm : Tm [] ((somehow M).ifThen (somehow (somehow M))) :=
  .lam (.val (.var .here))

/-- The identity term at `φ`. -/
def idTm (φ : PLLFormula) : Tm [] (φ.ifThen φ) := .lam (.var .here)

/-- Composition of closed function terms: `g ∘ f = λx. g (f x)`. -/
def compTm {A B C : PLLFormula} (g : Tm [] (B.ifThen C))
    (f : Tm [] (A.ifThen B)) : Tm [] (A.ifThen C) :=
  .lam (.app g.weaken (.app f.weaken (.var .here)))

/-- The normal form of `η ∘ μ`: `λx. val (let val y ⇐ x in y)` — the
pending collapse, re-thunked.  Visibly not the identity. -/
def etaMuNf : Tm [] ((somehow (somehow M)).ifThen (somehow (somehow M))) :=
  .lam (.val (.bind (.var .here) (.var .here)))

/-! ## The normaliser computes both composites (by `rfl`, `M` free) -/

theorem reduce_mu_eta :
    (compTm (muTm M) (etaTm M)).reduceFuel 8 = (idTm (somehow M), true) := rfl

theorem reduce_eta_mu :
    (compTm (etaTm M) (muTm M)).reduceFuel 8 = (etaMuNf M, true) := rfl

/-- `μ ∘ η` reduces to the identity: the unit law as computation. -/
theorem mu_eta_steps_id :
    Steps (compTm (muTm M) (etaTm M)) (idTm (somehow M)) :=
  (Tm.reduceFuel_sound 8 _).1

/-- `η ∘ μ` reduces to the re-thunked normal form. -/
theorem eta_mu_steps_nf :
    Steps (compTm (etaTm M) (muTm M)) (etaMuNf M) :=
  (Tm.reduceFuel_sound 8 _).1

theorem etaMuNf_nf : Nf (etaMuNf M) :=
  (Tm.reduceFuel_sound 8 (compTm (etaTm M) (muTm M))).2 rfl

theorem idTm_nf : Nf (idTm (somehow M)) :=
  (Tm.reduceFuel_sound 8 (compTm (muTm M) (etaTm M))).2 rfl

/-! ## The complete reduction graph of `η ∘ μ`

Writing the composite `T₀ = λx. (λy. val y) ((λz. let val w ⇐ z in w) x)`,
its reducts are exactly

  `T₁ = λx. val ((λz. let val w ⇐ z in w) x)`   (outer β first)
  `T₂ = λx. (λy. val y) (let val w ⇐ x in w)`   (inner β first)
  `T₃ = λx. val (let val w ⇐ x in w)`           (`etaMuNf`, normal)

with `T₀ → T₁ → T₃`, `T₀ → T₂ → T₃`, and nothing else: four terms,
closed under `Step`, and the identity is not among them. -/

private def T1 : Tm [] ((somehow (somehow M)).ifThen (somehow (somehow M))) :=
  .lam (.val (.app (.lam (.bind (.var .here) (.var .here))) (.var .here)))

private def T2 : Tm [] ((somehow (somehow M)).ifThen (somehow (somehow M))) :=
  .lam (.app (.lam (.val (.var .here))) (.bind (.var .here) (.var .here)))

private theorem step_T0 {u} (h : Step (compTm (etaTm M) (muTm M)) u) :
    u = T1 M ∨ u = T2 M := by
  have e : compTm (etaTm M) (muTm M) =
      .lam (.app (.lam (.val (.var .here)))
        (.app (.lam (.bind (.var .here) (.var .here))) (.var .here))) := rfl
  rw [e] at h
  cases h with
  | lamCong hb =>
    cases hb with
    | beta t s => left; rfl
    | appCong₁ hf =>
      cases hf with
      | lamCong hv => cases hv with | valCong hx => cases hx
    | appCong₂ ha =>
      cases ha with
      | beta t s => right; rfl
      | appCong₁ hg =>
        cases hg with
        | lamCong hb2 =>
          cases hb2 with
          | bindCong₁ h1 => cases h1
          | bindCong₂ h2 => cases h2
      | appCong₂ hx => cases hx

private theorem step_T1 {u} (h : Step (T1 M) u) : u = etaMuNf M := by
  cases h with
  | lamCong hb =>
    cases hb with
    | valCong ha =>
      cases ha with
      | beta t s => rfl
      | appCong₁ hg =>
        cases hg with
        | lamCong hb2 =>
          cases hb2 with
          | bindCong₁ h1 => cases h1
          | bindCong₂ h2 => cases h2
      | appCong₂ hx => cases hx

private theorem step_T2 {u} (h : Step (T2 M) u) : u = etaMuNf M := by
  cases h with
  | lamCong hb =>
    cases hb with
    | beta t s => rfl
    | appCong₁ hf =>
      cases hf with
      | lamCong hv => cases hv with | valCong hx => cases hx
    | appCong₂ ha =>
      cases ha with
      | bindCong₁ h1 => cases h1
      | bindCong₂ h2 => cases h2

private theorem step_T3 {u} (h : Step (etaMuNf M) u) : False := by
  cases h with
  | lamCong hb =>
    cases hb with
    | valCong ha =>
      cases ha with
      | bindCong₁ h1 => cases h1
      | bindCong₂ h2 => cases h2

/-- The four-term set is closed under reduction. -/
private theorem steps_inv
    {t u : Tm [] ((somehow (somehow M)).ifThen (somehow (somehow M)))}
    (h : Steps t u)
    (ht : t = compTm (etaTm M) (muTm M) ∨ t = T1 M ∨ t = T2 M ∨ t = etaMuNf M) :
    u = compTm (etaTm M) (muTm M) ∨ u = T1 M ∨ u = T2 M ∨ u = etaMuNf M := by
  induction h with
  | refl t => exact ht
  | head hstep _ ih =>
    apply ih
    rcases ht with h0 | h1 | h2 | h3
    · subst h0
      rcases step_T0 M hstep with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · subst h1
      exact Or.inr (Or.inr (Or.inr (step_T1 M hstep)))
    · subst h2
      exact Or.inr (Or.inr (Or.inr (step_T2 M hstep)))
    · subst h3
      exact absurd hstep (fun h => step_T3 M h)

/-- **`η ∘ μ` does not reduce to the identity**, by any reduction
sequence: its complete reduction graph is the four terms above, and the
identity is not among them. -/
theorem not_steps_eta_mu_id :
    ¬ Steps (compTm (etaTm M) (muTm M)) (idTm (somehow (somehow M))) := by
  intro h
  rcases steps_inv M h (Or.inl rfl) with h | h | h | h <;>
    simp [compTm, Tm.weaken, Tm.rename, T1, T2, etaMuNf, idTm, etaTm, muTm] at h

/-- The identity is normal: its only reduct is itself. -/
private theorem steps_id_eq {φ : PLLFormula} {t u : Tm [] (φ.ifThen φ)}
    (h : Steps t u) (ht : t = idTm φ) : u = idTm φ := by
  induction h with
  | refl _ => exact ht
  | head hstep _ _ =>
    subst ht
    cases hstep with
    | lamCong hb => cases hb

/-- `η ∘ μ` and the identity have no common reduct. -/
theorem eta_mu_id_not_joinable :
    ¬ ∃ u, Steps (compTm (etaTm M) (muTm M)) u ∧
      Steps (idTm (somehow (somehow M))) u := by
  rintro ⟨u, h1, h2⟩
  exact not_steps_eta_mu_id M (steps_id_eq h2 rfl ▸ h1)

/-- **Idempotence is inter-derivability, not isomorphism**: the
canonical pair `μ : ◯◯M ⊃ ◯M`, `η : ◯M ⊃ ◯◯M` satisfies the unit law
`μ ∘ η ⇝* id`, but `η ∘ μ` never reaches the identity. -/
theorem mu_eta_not_mutually_inverse :
    Steps (compTm (muTm M) (etaTm M)) (idTm (somehow M)) ∧
    ¬ Steps (compTm (etaTm M) (muTm M)) (idTm (somehow (somehow M))) :=
  ⟨mu_eta_steps_id M, not_steps_eta_mu_id M⟩

/-- **`η ∘ μ` is not convertible to the identity**: the separation up
to the full equivalence closure of reduction, by Church–Rosser — a
conversion would give a common reduct, which `eta_mu_id_not_joinable`
rules out. -/
theorem eta_mu_not_conv_id :
    ¬ Conv (compTm (etaTm M) (muTm M)) (idTm (somehow (somehow M))) :=
  fun h => eta_mu_id_not_joinable M h.joinable

/-! ## Axiom audit (build-time guards) -/

/-- info: 'PLLND.mu_eta_not_mutually_inverse' depends on axioms: [propext] -/
#guard_msgs in
#print axioms mu_eta_not_mutually_inverse

/-- info: 'PLLND.eta_mu_id_not_joinable' depends on axioms: [propext] -/
#guard_msgs in
#print axioms eta_mu_id_not_joinable

/--
info: 'PLLND.eta_mu_not_conv_id' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eta_mu_not_conv_id

end PLLND
