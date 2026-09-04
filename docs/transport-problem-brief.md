# Handoff brief: the transport problem in dependently typed definitions

**Purpose.** Reference document for Claude Code, working in a local clone of a Lean 4
development of lax logic. Development of key normalisation theorems is blocked by
casts between `T n` and `T m` where `n = m` holds only propositionally. This brief
names the problem, gives concrete Lean 4 and Agda examples of each mitigation, and
ends with an audit checklist and suggested task order for the repo.

---

## 1. Terminology (for searching literature, Zulip, and mathlib)

- **Transport problem / "DTT hell" / "transport hell"** — needing
  `Eq.rec` / `cast` / `▸` to move a term of `T m` to `T n` along `h : m = n`,
  and the resulting proliferation of casts through every later statement.
- **Green slime** (Conor McBride) — the *root cause*: an inductive family whose
  indices are arbitrary *expressions* (`Fin (x + y)`, `Tm Γ (A.subst σ)`) rather
  than variables or constructor forms. Unification cannot invert `x + y`, so
  dependent pattern matching gets stuck and every use site needs a transport.
- **`motive is not type correct`** — Lean's error when `rw` on an index would
  produce an ill-typed `Eq.rec` motive. It is the compiler telling you that you
  are rewriting *under* a dependency.
- **Heterogeneous equality** — `HEq` in Lean (`a ≍ b` between `a : α`, `b : β`),
  a.k.a. John Major equality (McBride). Useful as an intermediate language, not
  as a final statement form.

## 2. Foundational context (why no framework dissolves this in Lean)

- **HoTT does not remove transports; it legitimises them.** Univalence turns
  equivalences into equalities, giving you *more* things to transport along.
  HoTT libraries are full of `transport` / `pathover` bookkeeping.
- **Cubical TT / Observational TT** make transport *compute* on type formers
  (e.g. transporting a pair reduces to a pair of transports), which removes much
  of the pain. Agda has cubical mode; **Lean 4 does not** and will not.
- **Agda's `REWRITE` pragma** lets a proven propositional equation (e.g.
  `n + zero ≡ n`) become *definitional*, dissolving whole classes of slime.
  No Lean analogue.
- **Lean's compensations:** definitional proof irrelevance and UIP. All proofs
  of `n = m : Nat` are definitionally equal, so cast-coherence lemmas
  (`cast_cast`, triangle/pentagon-style conditions) are trivially provable by
  `subst`. There is no coherence tower as in HoTT. Exploit this: a small,
  finite `simp` set fully normalises cast expressions.
- **Coercions (`Coe`, `CoeSort`, unification hints) cannot help.** They fire
  during elaboration on definitional gaps. The gap here is propositional — no
  instance can see the proof `n = m`. This is why the coercion route failed.

## 3. The problem, minimally (both systems)

### Agda — pattern matching stuck on slime

```agda
foo : (x y : ℕ) → Fin (x + y) → ⊤
foo x y fz     = ?   -- rejected:
foo x y (fs _) = ?
-- "I'm not sure if there should be a case for fz ...
--  stuck unification problem: suc n ≟ x + y"
```

The standard Agda repairs: `with x + y in p` (retains `p : x + y ≡ suc n`),
or the inspect idiom. Both are manual transport management.

### Lean 4 — the same wall

```lean
inductive Vec (α : Type u) : Nat → Type u
  | nil  : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def append : Vec α m → Vec α n → Vec α (m + n)
  | .nil,       ys => (Nat.zero_add n ▸ ys : Vec α (0 + n))  -- cast already!
  | .cons a xs, ys => Nat.succ_add .. ▸ .cons a (append xs ys)
```

(With Lean's `m + n` recursion on the *right* argument you can dodge this
particular one — index-arithmetic choices matter, see §5.1 — but any statement
like `append (append xs ys) zs = append xs (append ys zs)` is *ill-typed*:
LHS : `Vec α ((a+b)+c)`, RHS : `Vec α (a+(b+c))`. Only a cast or `HEq` can
even state it.)

## 4. The mitigation arsenal, with examples

Ordered by leverage. **4.1 and 4.2 are design-time; prefer them. 4.3–4.5 are
proof-time; needed for whatever slime survives.**

### 4.1 Eliminate slime at the definition (McBride's rule + fording)

**Rule:** in constructor *return types*, indices must be variables or
constructor patterns — never function applications.

**Fording** (Henry Ford: "any colour, so long as it's black"): replace a slimy
index with a fresh variable plus an explicit equation.

```lean
-- BEFORE: slime — index is a function application
inductive Tm : Ctx → Ty → Type
  | tsubst : Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A.substTy σ)

-- AFTER: forded — index is a variable; the equation is ordinary data
inductive Tm : Ctx → Ty → Type
  | tsubst : Tm Γ A → (σ : Sub Δ Γ) → (B : Ty) → B = A.substTy σ → Tm Δ B
```

Now `cases`/`induction` succeed, and the equation lands in context where
`subst` can consume it. Costs: constructors carry equations; smart
constructors (`def tsubst' t σ := .tsubst t σ _ rfl`) hide this from users.

Agda equivalent:

```agda
data Tm : Ctx → Ty → Set where
  tsubst : Tm Γ A → (σ : Sub Δ Γ) → ∀ B → B ≡ substTy A σ → Tm Δ B
```

**Sub-case — recursion structure:** pick definitions so indices stay
canonical. `Vec.append` recursing on the left forces `succ (m + n) = succ m + n`
obligations or not depending on how `+` recurses. Aligning your recursion with
the recursion of the index-level function removes casts *definitionally*.

### 4.2 Extrinsic (or less-indexed) syntax — the big lever for normalisation

For normalisation developments the classic trade is:

- **Intrinsically typed terms** `Tm : Ctx → Ty → Type`: type preservation is
  free, but weakening/substitution lemmas do index arithmetic → slime →
  transport hell in exactly the strengthening/commutation lemmas a
  normalisation proof needs.
- **Well-scoped, extrinsically typed**: terms indexed only by scope (`Nat`),
  typing as a separate relation. Indices are then only ever `n` and `n + 1`
  (constructor forms) — no slime.

```lean
-- Well-scoped terms: the only index operations are 0 and +1 (canonical!)
inductive Tm : Nat → Type
  | var : Fin n → Tm n
  | app : Tm n → Tm n → Tm n
  | lam : Tm (n + 1) → Tm n
  | box : Tm n → Tm n            -- lax modality ○/◯ as appropriate

-- Typing is a Prop-valued relation; equalities about types are ordinary
-- rewriting, never transports:
inductive HasTy : Ctx n → Tm n → Ty → Prop
  | var  : Γ.get i = A → HasTy Γ (.var i) A
  | app  : HasTy Γ f (.arr A B) → HasTy Γ a A → HasTy Γ (.app f a) B
  | lam  : HasTy (Γ.cons A) t B → HasTy Γ (.lam t) (.arr A B)
  ...
```

Normalisation then proceeds via logical relations on *untyped-but-scoped*
terms, with typing hypotheses threaded through — the standard architecture in
most large Lean/Rocq metatheory developments precisely to pre-empt transport
hell. Preservation/progress are proved once, instead of being wired into the
syntax.

**Companion move — parallel substitution (σ-calculus / Autosubst style):**
make *one* operation primitive and derive the rest, so no lemma ever mentions
index arithmetic:

```lean
def Ren (m n : Nat) := Fin m → Fin n
def Sub (m n : Nat) := Fin m → Tm n

def Tm.rename : Tm m → Ren m n → Tm n
  | .var i,   ρ => .var (ρ i)
  | .app f a, ρ => .app (f.rename ρ) (a.rename ρ)
  | .lam t,   ρ => .lam (t.rename (up ρ))   -- up lifts under a binder
  | .box t,   ρ => .box (t.rename ρ)

def Tm.subst : Tm m → Sub m n → Tm n := ...  -- same shape

-- The σ-calculus equations (subst_subst, rename_subst, up_comp, ...) become a
-- simp set. Every substitution lemma in the normalisation proof is then simp +
-- funext-free equational reasoning about functions Fin m → Tm n. Zero casts.
```

If the lax modality demands *typed* syntax (e.g. the ○-introduction rule
constrains contexts non-trivially), consider the hybrid: well-scoped syntax +
typed *judgments*, and prove normalisation of the judgment relation.

### 4.3 The `generalize`-then-`subst` idiom (proof-time)

`subst` requires a variable on one side of the equation. Manufacture one:

```lean
example (v : Vec α (n + 0)) : P (n + 0) v := by
  -- rw [Nat.add_zero] at v  -- ✗ motive is not type correct
  generalize h : n + 0 = k at v ⊢   -- v : Vec α k, goal P k v, h : n + 0 = k
  -- now rewrite h with plain Nat lemmas; induction on v is unblocked
```

Before `induction` on an indexed term whose index is compound, the ritual is:
`revert` dependents → `generalize` the index (keeping the equation) →
`induction` → in each case, `subst`/`omega` the equation. When `generalize`
itself fails because auxiliary `match`/proof terms mention the index, the
known workaround is to write the generalisation motive explicitly with
`suffices ∀ k h, ... from this _ rfl` — ugly but effective (documented on
Zulip: "Cannot rewrite term being cased on").

### 4.4 A cast API with a simp normal form (the `eqToHom` lesson)

Mathlib's category theory is the canonical worked instance of your exact
problem: morphisms are dependently typed over objects, so object equalities
are poison. Mathlib's answer is **not** to rewrite, but to reify the equality
as a term — `eqToHom (h : X = Y) : X ⟶ Y` — plus simp lemmas
(`eqToHom_refl`, `eqToHom_trans`, `eqToHom_map`, naturality/conjugation forms)
so the reified casts *cancel* at the right moment. `Functor.ext` even states
its hypothesis in this form (`F.map f = eqToHom .. ≫ G.map f ≫ eqToHom ..`)
because the naive statement is unusable.

Transplant the pattern. For each slimy family `T : I → Type`, define one
blessed cast and normalise everything into it:

```lean
def Vec.cast (h : m = n) : Vec α m → Vec α n := fun v => h ▸ v

@[simp] theorem Vec.cast_rfl (v : Vec α n) : v.cast rfl = v := rfl

@[simp] theorem Vec.cast_cast (h₁ : m = n) (h₂ : n = k) (v : Vec α m) :
    (v.cast h₁).cast h₂ = v.cast (h₁.trans h₂) := by subst h₁; subst h₂; rfl

-- One commuting lemma per constructor / operation, phrased so simp can match:
@[simp] theorem Vec.cast_cons (h : m = n) (a : α) (v : Vec α m) :
    (Vec.cons a v).cast (by omega : m + 1 = n + 1) = Vec.cons a (v.cast h) := by
  subst h; rfl

@[simp] theorem Vec.cast_append_left (h : m = m') (xs : Vec α m) (ys : Vec α n) :
    (xs.cast h).append ys = (xs.append ys).cast (by omega) := by
  subst h; rfl
```

Design notes that make this work:

- Every proof of every cast lemma is `subst` + `rfl` (UIP does the rest).
  Writing them is mechanical — ideal work to delegate wholesale to Claude Code.
- Choose a **normal form direction** (e.g. "push casts toward variables /
  leaves") and orient all simp lemmas that way; casts then meet and cancel via
  `cast_cast`/`cast_rfl`.
- Proof obligations for the *index* equalities inside lemmas should be
  discharged by `omega` (Nat/Int indices) so simp application is frictionless.
- Statements of public lemmas should mention `T.cast` (one blessed function),
  never raw `▸` / `Eq.rec` / `cast` — mixed cast spellings defeat simp.
- Mathlib precedents to imitate: `Fin.cast`, `List.Vector.cast` and their simp
  sets; `CategoryTheory.eqToHom` for the richer, composition-aware variant.

### 4.5 `HEq` as scaffolding (state hetero, finish homo)

Some statements (associativity over `(a+b)+c` vs `a+(b+c)`) are only directly
expressible heterogeneously. Pattern: prove the `HEq`, convert at the boundary.

```lean
theorem append_assoc (xs : Vec α a) (ys : Vec α b) (zs : Vec α c) :
    HEq ((xs.append ys).append zs) (xs.append (ys.append zs)) := by
  induction xs with
  | nil => simp [Vec.append]
  | cons x xs ih => simp [Vec.append]; exact heq_congr ih  -- sketch

-- Boundary conversion back to a cast equation:
theorem append_assoc' (xs : Vec α a) (ys : Vec α b) (zs : Vec α c) :
    (xs.append ys).append zs
      = (xs.append (ys.append zs)).cast (Nat.add_assoc ..).symm := by
  have h := append_assoc xs ys zs
  exact eq_of_heq (h.trans (Vec.cast_heq ..).symm)
```

Key bridge lemmas in core: `eqRec_heq`, `cast_heq`, `heq_of_eqRec_eq`,
`heq_iff_eq`, `eq_of_heq`. Rules of thumb: `HEq` in *private* lemmas only;
never in a definition's type; convert to `Eq`-of-cast at API boundaries.
`simp` has some `HEq` congruence support but it is far weaker than for `Eq` —
another reason to keep it internal.

### 4.6 Small proof-time helpers worth knowing (Lean)

- `omega` — closes the Nat/Int index equalities that parameterise every cast.
- `subst_vars`, `cases h` (on `h : a = b`) — bulk substitution.
- `conv ... rw` — targeted rewriting that sometimes sidesteps bad motives.
- `simp only [Vec.cast_*]` with your §4.4 set — the workhorse.
- `congr`/`hcongr` — splits goals into index equality + `HEq` of payloads.
- `grind` (Lean ≥ 4.22) — worth trying on cast-cancellation goals once the
  simp set exists, but it is not a transport solver.

## 5. Tooling landscape (why you build the API instead of importing one)

- **Trocq** (Cohen–Crance–Mahboubi, TOPLAS 2025; Rocq plugin in Coq-Elpi):
  proof transfer via a generalised univalent-parametricity translation;
  handles relations weaker than equivalence and avoids the univalence axiom
  where possible. The right *ideas*; **no Lean port exists**.
- **Isabelle `Transfer`/`Lifting`**: mature analogue in a simpler type theory.
- **Lean today**: `norm_cast`/`push_cast` handle *coercion* casts only (they
  will not touch `Eq.rec`); `equiv_rw` rewrites along `Equiv`s in limited
  positions; generalised rewriting (Rocq's `setoid_rewrite`) is *not
  implemented*, with only exploratory community work. Conclusion: in Lean, the
  §4.1–4.4 disciplines are the state of the art, and they are what mathlib
  itself does.

## 6. Audit checklist and task order for the lax logic repo

For Claude Code, working in the repo clone:

1. **Inventory the slime.** Grep every `inductive` for constructor return
   types whose indices contain function applications (`+`, `substTy`, context
   append `++`/`,,`, `weaken`, etc.). Also grep proofs for `▸`, `cast`,
   `Eq.mp`, `Eq.mpr`, `HEq`, `eq_rec`, and for `sorry`s adjacent to
   "motive is not type correct" comments. Produce a table: definition →
   offending index expression → downstream lemmas blocked.
2. **Classify each site:**
   a. index arithmetic removable by re-choosing recursion structure (§4.1);
   b. removable by fording (§4.1);
   c. symptomatic of intrinsic typing where extrinsic/hybrid would serve (§4.2);
   d. irreducible → needs the cast API (§4.4).
3. **Decide the architecture question first** (it dominates everything): if
   the blocked theorems are substitution/weakening commutation lemmas feeding
   normalisation, seriously cost out the well-scoped + extrinsic-typing +
   parallel-substitution refactor (§4.2) before investing in casts. It is a
   larger diff but each proof becomes near-mechanical.
4. **If staying intrinsic:** implement `Tm.cast` (and casts for any other
   indexed family) with the full simp set of §4.4; restate blocked lemmas in
   cast normal form (the `Functor.ext` trick); re-attempt the normalisation
   theorems with `simp [Tm.cast_*]` + `omega` discharging index goals.
5. **Sequencing:** land the cast API + simp set as one PR with zero behaviour
   change; then migrate one blocked normalisation lemma end-to-end as the
   pilot; only then batch the rest.
6. **Regression guard:** add a lint/test file asserting the simp set
   normalises representative nested-cast expressions to cast-free form.

## 7. Pointers

- McBride, *green slime* discussions (types.pl, 2024) and the fording idiom
  from *Eliminating Dependent Pattern Matching* / "Ornaments" lineage.
- Mathlib: `Mathlib.CategoryTheory.EqToHom` (read the module docstring — it is
  a design document for exactly this problem); `Fin.cast`; `Functor.ext`.
- Carneiro & Riehl et al., *Formalizing colimits in Cat* (arXiv:2503.20704) —
  a frank account of `eqToHom` engineering under heavy object-equality load.
- *Trocq: Proof Transfer for Free, Beyond Equivalence and Univalence*
  (arXiv:2310.14022, TOPLAS 2025).
- Agda CwF formalisation report (yeejian.dev M1 report, 2024) — surveys
  transport-hell escape routes: less-indexed definitions, REWRITE, OTT.
- Autosubst / σ-calculus papers for the parallel-substitution simp set.
