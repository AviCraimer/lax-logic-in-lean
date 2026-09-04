import LaxLogic.PLLTerms

/-!
# Proof terms compute constraints (F&M §1(6): timing analysis)

F&M motivate `◯` by timing analysis of combinational circuits (p. 5,
following Mendler 1996): `◯M` reads "`M` holds under some constraint", and

* `◯R` corresponds to a wire — delay `0`;
* `◯M` to sequential composition — *addition* of delays;
* `◯S` to parallel composition — *maximum* of delays;

so proofs over the delay algebra `(ℕ, 0, +, max)` compute data-dependent
timing constraints.

This file realises that reading denotationally: interpret `◯φ` as `M × ⟦φ⟧`
for a combination structure `(M, op, e)` — a writer monad, with `val`
emitting the unit constraint `e` and `bind` combining constraints with
`op`.  Evaluation of a proof term then *is* constraint extraction.
Instantiating `(ℕ, +, 0)` gives accumulated sequential delay;
instantiating `(ℕ, max, 0)` gives the ready-time reading.  The worked
example is the two-gate circuit: a proof of `A ⊃ ◯C` from gates
`A ⊃ ◯B` and `B ⊃ ◯C` evaluates to delay `d₁ + d₂`, **by `rfl`** — the
constraint is computed by the kernel from the proof term.

No laws about `(M, op, e)` are needed: we evaluate proofs, we do not prove
program equivalences.  (For the monad laws one would ask for a monoid, and
the `Step`-reduction of `PLLTerms.lean` would be sound for the semantics —
future work.)
-/

open PLLFormula

namespace PLLND

variable {M : Type} (op : M → M → M) (e : M) (base : String → Type)

/-- Denotational semantics: `◯` is the writer over `(M, op, e)`. -/
def sem : PLLFormula → Type
  | .prop a => base a
  | .falsePLL => Empty
  | .and φ ψ => sem φ × sem ψ
  | .or φ ψ => sem φ ⊕ sem ψ
  | .ifThen φ ψ => sem φ → sem ψ
  | .somehow φ => M × sem φ

/-- Environments: iterated products over the context. -/
def Env : List PLLFormula → Type
  | [] => PUnit
  | φ :: Γ => sem (M := M) base φ × Env Γ

/-- Variable lookup. -/
def Var.look : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Var Γ φ → Env (M := M) base Γ → sem (M := M) base φ
  | _, _, .here, ρ => ρ.1
  | _, _, .there v, ρ => v.look ρ.2

/-- Evaluation of proof terms — constraint extraction. -/
def Tm.eval : ∀ {Γ : List PLLFormula} {φ : PLLFormula},
    Tm Γ φ → Env (M := M) base Γ → sem (M := M) base φ
  | _, _, .var v, ρ => v.look base ρ
  | _, _, .abort _ t, ρ => (t.eval ρ).elim
  | _, _, .lam t, ρ => fun a => t.eval (a, ρ)
  | _, _, .app t s, ρ => t.eval ρ (s.eval ρ)
  | _, _, .pair t s, ρ => (t.eval ρ, s.eval ρ)
  | _, _, .fst t, ρ => (t.eval ρ).1
  | _, _, .snd t, ρ => (t.eval ρ).2
  | _, _, .inl t, ρ => .inl (t.eval ρ)
  | _, _, .inr t, ρ => .inr (t.eval ρ)
  | _, _, .case t u₁ u₂, ρ =>
      match t.eval ρ with
      | .inl a => u₁.eval (a, ρ)
      | .inr b => u₂.eval (b, ρ)
  | _, _, .val t, ρ => (e, t.eval ρ)
  | _, _, .bind t u, ρ =>
      let p := t.eval ρ
      let q := u.eval (p.2, ρ)
      (op p.1 q.1, q.2)

/-! ### The two-gate circuit (F&M §1(6))

Atoms `A`, `B`, `C` are signal stabilities; a gate is an assumption
`A ⊃ ◯B` whose *environment entry* carries its delay.  Sequential
composition of two gates is the proof term

  `λ x. bind (g₁ x) (g₂ ·)  :  A ⊃ ◯C`

and its evaluation computes the composite constraint. -/

private abbrev A := prop "A"
private abbrev B := prop "B"
private abbrev C := prop "C"

/-- The sequential composition of two gates, as a proof term:
`Γ = [A ⊃ ◯B, B ⊃ ◯C] ⊢ A ⊃ ◯C`. -/
def twoGates : Tm [A.ifThen (somehow B), B.ifThen (somehow C)]
    (A.ifThen (somehow C)) :=
  .lam (.bind
    (.app (.var (.there .here)) (.var .here))
    (.app (.var (.there (.there (.there .here)))) (.var .here)))

/-- A gate with delay `d`: semantically, a function emitting constraint
`d`. -/
def gate {M : Type} {base : String → Type} {a b : String}
    (d : M) (f : base a → base b) :
    sem (M := M) base ((prop a).ifThen (somehow (prop b))) :=
  fun x => (d, f x)

/-- **Sequential gates add their delays** (F&M: "`◯M` deals with the
sequential composition of circuits, which involves the addition `+` of
delays") — and the constraint is computed from the proof term by `rfl`. -/
example (d₁ d₂ : ℕ) (u : Unit) :
    (twoGates.eval (· + ·) 0 (fun _ => Unit)
      (gate d₁ id, (gate d₂ id, PUnit.unit)) u).1 = d₁ + d₂ :=
  rfl

/-- Under the ready-time reading `(ℕ, max, 0)`, the same proof term
computes the maximum instead. -/
example (d₁ d₂ : ℕ) (u : Unit) :
    (twoGates.eval Nat.max 0 (fun _ => Unit)
      (gate d₁ id, (gate d₂ id, PUnit.unit)) u).1 = Nat.max d₁ d₂ :=
  rfl

/-- The `◯R` proof term (a wire) emits the unit constraint `0`. -/
example (u : Unit) :
    ((Tm.lam (.val (.var .here)) :
        Tm [] (A.ifThen (somehow A))).eval (· + ·) 0 (fun _ => Unit)
      PUnit.unit u).1 = 0 :=
  rfl

/-- The `◯M` proof term (monadic join, `λ x. bind x id`) *combines* the two
constraint layers: sequential composition of constraints. -/
def joinTm : Tm [] ((somehow (somehow A)).ifThen (somehow A)) :=
  .lam (.bind (.var .here) (.var .here))

example (d d' : ℕ) (u : Unit) :
    (joinTm.eval (· + ·) 0 (fun _ => Unit) PUnit.unit (d, (d', u))).1
      = d + d' :=
  rfl

/-- Evaluation respects the Curry–Howard reading: `twoGates` really is the
`laxElim`-composition proof of `A ⊃ ◯C`. -/
example : Nonempty (LaxND [A.ifThen (somehow B), B.ifThen (somehow C)]
    (A.ifThen (somehow C))) :=
  ⟨twoGates.toND⟩

end PLLND
