/-!
# Tactics distilled from the PLL normalisation development

Three patterns recurred across `PLLSubst`, `PLLNormal`, `PLLStrongNorm` and
`PLLReducibility` often enough — and cost enough iteration when written by
hand — to be worth packaging before the ⊤⊤-lifting session consumes them at
scale:

* `mirror` — the *congruence-mirror* step: a goal `R (c t₁ … tₙ) (c t₁' … tₙ')`
  closed by the matching constructor of `R`, premises discharged from
  hypotheses (induction hypotheses included, instantiating their
  quantifiers).  Collapses the 17–22-case inductions that translate one
  step relation into another (`toStep`, preservation under
  renaming/substitution, `step_split`).

* `lift_cases` — the pointwise σ-algebra step: a goal
  `∀ ψ (v : Var (χ :: Γ) ψ), lhs v = rhs v` where both the `here` and
  `there` cases hold by `rfl`.  This is the binder case of every
  composition law.

* `Acc.pairInduction` / `Acc.tripleInduction` — simultaneous accessibility
  induction on two or three terms, packaged as eliminators.  The hand-rolled
  version (revert invariants / nest `induction … with | intro` / re-intro /
  rebuild `Acc` witnesses with `.intro`) was the single most error-prone
  move in the reducibility file; these eliminators do the bookkeeping once,
  in term mode, so the motive is explicit and nothing is silently
  generalized.  Stated for arbitrary relations so they serve `RStep` today
  and full `Step` in the ⊤⊤ file.
-/

/-! ### Congruence mirroring -/

/-- Close a goal headed by an inductive relation by applying its (first
unifying) constructor, then discharging the premises with `solve_by_elim`
over the local context.  Intended for congruence cases of step-relation
inductions, where the matching constructor is shape-determined and its
premise is the induction hypothesis (possibly at an instantiated
renaming/substitution). -/
macro "mirror" : tactic => `(tactic| (constructor <;> solve_by_elim))

/-! ### Pointwise lifted-variable analysis -/

/-- Discharge a pointwise goal `∀ ψ (v : Var _ ψ), lhs v = rhs v` (the
binder case of a σ-algebra law) when both the `here` and `there` cases are
definitional. -/
macro "lift_cases" : tactic =>
  `(tactic| (intro _ v; cases v with
      | here => rfl
      | there _ => rfl))

/-! ### Simultaneous accessibility induction -/

universe u v w

/-- Accessibility induction with the accessibility witness re-supplied to
the step case (the raw recursor drops it, forcing manual `.intro`
reconstruction at every use). -/
theorem Acc.selfInduction {α : Sort u} {r : α → α → Prop} {P : α → Prop}
    {a : α} (ha : Acc r a)
    (H : ∀ a, Acc r a → (∀ a', r a' a → P a') → P a) : P a :=
  Acc.rec (fun x hx ih => H x ⟨x, hx⟩ ih) ha

/-- Simultaneous accessibility induction on a pair: prove `P a b` given
that `P` may assume itself at any `r`-predecessor of `a` (same `b`) and at
any `q`-predecessor of `b` (same `a`).  The step hypothesis also receives
both accessibility witnesses. -/
theorem Acc.pairInduction {α : Sort u} {β : Sort v}
    {r : α → α → Prop} {q : β → β → Prop} {P : α → β → Prop}
    {a : α} {b : β} (ha : Acc r a) (hb : Acc q b)
    (H : ∀ a b, Acc r a → Acc q b →
      (∀ a', r a' a → P a' b) → (∀ b', q b' b → P a b') → P a b) :
    P a b :=
  Acc.rec (motive := fun a _ => ∀ b, Acc q b → P a b)
    (fun a haacc iha _b hb =>
      Acc.rec (motive := fun b _ => P a b)
        (fun b hbacc ihb =>
          H a b ⟨a, haacc⟩ ⟨b, hbacc⟩
            (fun a' hr => iha a' hr b ⟨b, hbacc⟩)
            (fun b' hq => ihb b' hq))
        hb)
    ha b hb

/-- Transfer accessibility along a simulation: if every `R`-predecessor of
`f a` is the image of an `r`-predecessor of `a`, then accessibility of `a`
gives accessibility of `f a`.  This is the shape of every "SN is preserved
by a unary constructor / by renaming" lemma: `inv` is the step-inversion
fact for `f`. -/
theorem Acc.of_inversion {α : Sort u} {β : Sort v}
    {r : α → α → Prop} {R : β → β → Prop} {f : α → β}
    (inv : ∀ {a : α} {y : β}, R y (f a) → ∃ a', y = f a' ∧ r a' a)
    {a : α} (ha : Acc r a) : Acc R (f a) :=
  Acc.selfInduction (P := fun x => Acc R (f x)) ha fun a _ ih =>
    Acc.intro (f a) fun _y hy =>
      match inv hy with
      | ⟨a', heq, hr⟩ => heq ▸ ih a' hr

/-- Binary variant of `Acc.of_inversion`, for two-argument constructors
whose steps are exactly the congruence steps in either argument. -/
theorem Acc.of_inversion₂ {α : Sort u} {β : Sort v} {γ : Sort w}
    {r : α → α → Prop} {q : β → β → Prop} {R : γ → γ → Prop} {f : α → β → γ}
    (inv : ∀ {a : α} {b : β} {y : γ}, R y (f a b) →
      (∃ a', y = f a' b ∧ r a' a) ∨ (∃ b', y = f a b' ∧ q b' b))
    {a : α} {b : β} (ha : Acc r a) (hb : Acc q b) : Acc R (f a b) :=
  Acc.pairInduction (P := fun a b => Acc R (f a b)) ha hb fun a b _ _ iha ihb =>
    Acc.intro (f a b) fun _y hy =>
      match inv hy with
      | .inl ⟨a', heq, hr⟩ => heq ▸ iha a' hr
      | .inr ⟨b', heq, hq⟩ => heq ▸ ihb b' hq

/-- Simultaneous accessibility induction on a triple; the three-branch
analogue of `Acc.pairInduction`. -/
theorem Acc.tripleInduction {α : Sort u} {β : Sort v} {γ : Sort w}
    {r : α → α → Prop} {q : β → β → Prop} {p : γ → γ → Prop}
    {P : α → β → γ → Prop}
    {a : α} {b : β} {c : γ} (ha : Acc r a) (hb : Acc q b) (hc : Acc p c)
    (H : ∀ a b c, Acc r a → Acc q b → Acc p c →
      (∀ a', r a' a → P a' b c) → (∀ b', q b' b → P a b' c) →
      (∀ c', p c' c → P a b c') → P a b c) :
    P a b c :=
  Acc.rec (motive := fun a _ => ∀ b, Acc q b → ∀ c, Acc p c → P a b c)
    (fun a haacc iha _b hb =>
      Acc.rec (motive := fun b _ => ∀ c, Acc p c → P a b c)
        (fun b hbacc ihb _c hc =>
          Acc.rec (motive := fun c _ => P a b c)
            (fun c hcacc ihc =>
              H a b c ⟨a, haacc⟩ ⟨b, hbacc⟩ ⟨c, hcacc⟩
                (fun a' hr => iha a' hr b ⟨b, hbacc⟩ c ⟨c, hcacc⟩)
                (fun b' hq => ihb b' hq c ⟨c, hcacc⟩)
                (fun c' hp => ihc c' hp))
            hc)
        hb)
    ha b hb c hc
