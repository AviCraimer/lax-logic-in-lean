# A Lean 4 design for category-partition test generation

This is a design, not an implementation: Lean declarations below are meant
to typecheck in spirit and to fix the exact shape of the port, but nothing
here has been run through `lake build`. It is written against the reading
of the original ML tool recorded in `docs/catpart-archaeology.md`; every
claim about what the original does or guarantees is cited back to that
document rather than re-derived here.

The governing idea, stated once up front because everything else follows
from it: **the original's `Choice.maybe_property : string list Option`
field types a property name as a bare string** (`catpart-lean-design.md`
cites `catpart_absyn_val.sml:23-29`, discussed at length in
`catpart-archaeology.md` §5). Nothing connects a name used in `[property
foo]` to the same name used in `[if foo]`; they are checked for equality at
run time (`member s V`, `PermList.member`), so a typo or a renamed property
is invisible until you notice a guard is never satisfied. That is exactly
the gap Matthew's own grammar comment (quoted in full in
`catpart-archaeology.md` §5) was reaching for and, on the evidence of the
surviving source, never closed. The port's central move is to make
properties (and choices, and categories) **types**, generated from the
spec, so that this class of error is a compile error.

---

## 1. Data types

### 1.1 Properties as a type

For a *given* spec, properties are an enumerated type, not strings:

```lean
inductive FindProperty : Type where
  | empty | nonempty | quoted | match
  deriving DecidableEq, Fintype, Repr
```

(Names taken from `find.tsl`'s `[property ...]` declarations —
`empty`/`nonempty`/`quoted`/`match`; verified against
`catpart-archaeology.md` §2.3, §6.3 example table.) A guard that mentions
`FindProperty.quotedd` (typo) is a Lean elaboration error at the point the
spec is written, not a silently-always-false runtime predicate. This
directly closes the gap identified in `catpart-archaeology.md` §5.

### 1.2 Conditions

The condition language is exactly the four-shape grammar read out of
`catpart_val.grm:122-126` (`catpart-archaeology.md` §2.4) — a property, a
negation, or a conjunction/disjunction of two conditions — with no
implicit associativity or n-ary forms, matching the original's strict
"both operands individually bracketed" discipline:

```lean
inductive Cond (Prop : Type) : Type where
  | prop (p : Prop)
  | not (c : Cond Prop)
  | and (c₁ c₂ : Cond Prop)
  | or (c₁ c₂ : Cond Prop)
  deriving DecidableEq, Repr

/-- Satisfaction of a condition against a finite set of properties already
    "in scope" (selected by the other choices in a frame). This is a plain
    recursive `Bool`, so it is decidable for free and evaluated by
    `decide`/`native_decide`, not interpreted through a separate
    evaluator. -/
def Cond.sat {Prop : Type} [DecidableEq Prop] (V : Finset Prop) :
    Cond Prop → Bool
  | .prop p   => p ∈ V
  | .not c    => ! c.sat V
  | .and c₁ c₂ => c₁.sat V && c₂.sat V
  | .or c₁ c₂  => c₁.sat V || c₂.sat V
```

This is parametric in the property type `Prop` on purpose: `Cond` and
`Cond.sat` are shared, spec-independent library code; only the property
type and the concrete conditions built from it are per-spec.

### 1.3 Flags

```lean
inductive Flag : Type where
  | error | single
  deriving DecidableEq, Repr
```

`catpart-archaeology.md` §1's "theorems worth proving" note (and §3 below)
records the important, checked fact about the original: the frame
generator (`catpart0.2_frame.sml`) never once pattern-matches `Error`
against `Single` — the only place the two are told apart at all is
`catpart_absyn_val.sml`'s pretty-printer (`string_of_Flag`). Both flags
mean exactly one thing to the generator: "isolate this choice into its own
singleton frame, never combine it with anything." The Lean design keeps
`Flag` as a two-constructor type (so the port can still print `error`
vs. `single` faithfully, and so a future extension *could* give them
different generation semantics) but the generator itself, like the
original, only ever asks "is there a flag at all", never which one — see
§2.

### 1.4 Categories and choices

Categories are a per-spec enumerated type. Each category's choices are
also a per-spec enumerated type, indexed by category — a genuinely
dependent family, tighter than the original's one flat `Choice` datatype
shared across all categories (`catpart_absyn_val.sml:28-29`):

```lean
inductive FindCategory : Type where
  | patternSize | quoting | embeddedBlanks | embeddedQuotes
  | fileName | numOccurrences | occurrencesOnLine
  deriving DecidableEq, Fintype, Repr

inductive PatternSizeChoice : Type where
  | empty | singleChar | manyChars | tooLong
  deriving DecidableEq, Fintype, Repr

inductive QuotingChoice : Type where
  | quoted | notQuoted | improperlyQuoted
  deriving DecidableEq, Fintype, Repr

-- ... one such inductive per category ...

def FindCategory.Choice : FindCategory → Type
  | .patternSize      => PatternSizeChoice
  | .quoting           => QuotingChoice
  | .embeddedBlanks    => EmbeddedBlanksChoice
  | .embeddedQuotes    => EmbeddedQuotesChoice
  | .fileName          => FileNameChoice
  | .numOccurrences    => NumOccurrencesChoice
  | .occurrencesOnLine => OccurrencesOnLineChoice

instance (c : FindCategory) : DecidableEq (c.Choice) := by cases c <;> infer_instance
instance (c : FindCategory) : Fintype (c.Choice)      := by cases c <;> infer_instance
```

Per-choice metadata — the analogue of `Modifiers`
(`catpart_absyn_val.sml:23-26`) — is a function out of each choice type,
not a field bundled into a shared record:

```lean
structure Modifiers (Prop : Type) : Type where
  cond  : Option (Cond Prop) := none
  props : List Prop := []
  flag  : Option Flag := none

def PatternSizeChoice.mods : PatternSizeChoice → Modifiers FindProperty
  | .empty      => { props := [.empty] }
  | .singleChar => { props := [.nonempty] }
  | .manyChars  => { props := [.nonempty] }
  | .tooLong    => { flag := some .error }
```

This reads directly off `find.tsl:3-7`
(`catpart-archaeology.md` §2.3 for the `[property ...]`/`[if ...]`/`[flag]`
syntax it is transcribing).

**Why per-category choice types rather than one flat `Choice`:** a flat
type would let a spec accidentally combine `PatternSizeChoice.empty` where
a `QuotingChoice` was meant — a category-mismatch bug the original's
grammar prevents only by *construction* (a `one_categ` production always
NEWLINE-groups a category's own choice lines) but that a hand-edited flat
ML `Choice list` per category does not protect once category and choice
lists have been separated in memory. The dependent-family encoding makes
that mismatch a type error instead of a spec bug to notice by eye.

---

## 2. Constraints as decidable propositions, admissibility as a type

Fix a spec: `Category : Type`, `[Fintype Category] [DecidableEq Category]`,
a family `Choice : Category → Type` with `[∀ c, Fintype (Choice c)]
[∀ c, DecidableEq (Choice c)]`, a property type `Prop` with
`[Fintype Prop] [DecidableEq Prop]`, and per-choice metadata
`mods : (c : Category) → Choice c → Modifiers Prop`.

The **unflagged domain** — one choice per category, restricted to choices
that carry no flag, exactly `partition_flags`'s "unflagged" half
(`catpart0.2_frame.sml:40-58`, `catpart-archaeology.md` §3.1):

```lean
def Unflagged (c : Category) : Type :=
  {ch : Choice c // (mods c ch).flag = none}

def UnflaggedFrame : Type := (c : Category) → Unflagged c
```

`UnflaggedFrame` is the Lean image of the raw cross-product
`∏_i Choices_unflagged(category i)` from `catpart-archaeology.md` §3.3 —
and, because `Category` and every `Unflagged c` are `Fintype`s, so is
`UnflaggedFrame` (a dependent-function type over a finite domain with
finite, decidably-equal codomains is automatically a `Fintype` in
Mathlib). This is the "termination for free" point developed in §4.

**Admissibility**, transcribing `setup_cond`/`valid`
(`catpart0.2_frame.sml:130-184`, `catpart-archaeology.md` §3.3) exactly,
including the detail that a guard is checked against the properties
contributed by *every other* selected choice, not just earlier ones:

```lean
def otherProps (f : UnflaggedFrame) (c : Category) : Finset Prop :=
  (Finset.univ.erase c).biUnion (fun c' => ((mods c' (f c').1).props).toFinset)

def satisfied (f : UnflaggedFrame) (c : Category) : Prop :=
  match (mods c (f c).1).cond with
  | none      => True
  | some cond => cond.sat (otherProps f c) = true

instance (f : UnflaggedFrame) (c : Category) : Decidable (satisfied f c) := by
  unfold satisfied; split <;> infer_instance

def Admissible (f : UnflaggedFrame) : Prop := ∀ c, satisfied f c

instance : DecidablePred Admissible := fun f =>
  Fintype.decidableForallFintype
```

This is the "constraints as decidable propositions" requirement:
`Admissible` is a `Prop`, but it comes with a `Decidable` instance built
entirely from `Cond.sat`'s structural recursion (§1.2) and finite
quantification over `Fintype`s — no interpreter, no separate `valid`
function to trust; `decide`/`native_decide` discharges `Admissible f`
directly, and so does ordinary pattern-matching-driven `Decidable`
resolution when `Admissible` appears as a hypothesis in a proof.

---

## 3. Frames carrying proofs

```lean
/-- An admissible (unflagged) frame: a full choice assignment together with
    a proof it satisfies every guard, evaluated against the properties
    the *other* categories' choices contribute. This is the Lean image of
    one row among `find.frm`'s frames 8–40. -/
def AdmissibleFrame : Type := {f : UnflaggedFrame // Admissible f}

/-- A flagged frame: one category, one flagged choice, nothing else — the
    Lean image of `flagged_combs`/`isolate`
    (`catpart0.2_frame.sml:285-293`), one row among `find.frm`'s frames
    1–7. The sigma type *is* the "never combined with anything else"
    guarantee: there is no field anywhere else to put another category's
    choice. -/
def FlaggedFrame : Type := Σ c : Category, {ch : Choice c // (mods c ch).flag ≠ none}

/-- The full frame set the tool emits for a spec — the Lean image of
    `find.frm` as a mathematical object, not as printed text. -/
def Frame : Type := FlaggedFrame ⊕ AdmissibleFrame
```

`AdmissibleFrame` and `FlaggedFrame` are both `Fintype`s (a `Subtype` of a
`Fintype` with a `DecidablePred`, and a `Sigma` of `Fintype`s,
respectively), hence so is `Frame`. **The generator is**:

```lean
def generate : Finset Frame := Finset.univ
```

There is no separate "generation algorithm" to get right independently of
the type: `Finset.univ` over `Frame` already *is* exactly the flagged
singleton frames plus the guard-admissible unflagged frames, because that
is what the type `Frame` was built to contain and nothing else — the
type-level restriction (`Unflagged`, `Admissible`, the sigma's own
subtype) does the filtering that the original does by an explicit runtime
`filter`/`valid` pass (`catpart0.2_frame.sml:176-184, 256-281`). This
answers the brief directly: admissibility gating is a property of the
*type* `AdmissibleFrame` inhabits, not a post-hoc filter applied to a
`List Frame` after generation — see also §5 for how this same idea extends
to the constraint-as-a-category proposal for `t`-way selection.

---

## 4. Theorems worth proving

All four are stated for a fixed spec (`Category`, `Choice`, `Prop`, `mods`,
with the `Fintype`/`DecidableEq` instances from §2); a real port would
state and prove them once, generically over any spec satisfying those
instances, and get every concrete spec's instance for free by
specialization.

**Soundness** — every frame the generator emits is admissible. For
`AdmissibleFrame` this is not an external property to prove after the
fact, it is carried by the value:

```lean
theorem admissible_frame_sound (f : AdmissibleFrame) : Admissible f.1 := f.2
```

and the flagged-choice analogue — no flagged choice's category is ever
combined with any other category's choice in a generated `AdmissibleFrame`
— follows from `Unflagged`'s definition, not from a separate argument:

```lean
theorem flagged_not_in_admissible_frame
    (f : AdmissibleFrame) (c : Category) : (mods c (f.1 c).1).flag = none :=
  (f.1 c).2
```

**Completeness / coverage.** The exact coverage notion the original
achieves, established by reading `generate_unflagged`
(`catpart-archaeology.md` §3.3), is: *every* point of the unflagged
cross-product that satisfies every guard appears, exactly once, as a
generated frame — **not** pairwise coverage, **not** any bounded-degree
combinatorial coverage, the full constrained cross-product. The Lean
statement of "the generator misses nothing admissible" is again close to
definitional given the subtype construction, which is itself evidence the
construction is the right one — a construction that required a separate,
nontrivial completeness *proof* would be evidence of an accidentally
narrower generator:

```lean
theorem admissible_frame_complete (f : UnflaggedFrame) (h : Admissible f) :
    ∃ f' : AdmissibleFrame, f'.1 = f := ⟨⟨f, h⟩, rfl⟩

theorem flagged_frame_complete (c : Category) (ch : Choice c)
    (h : (mods c ch).flag ≠ none) :
    ∃ ff : FlaggedFrame, ff = ⟨c, ⟨ch, h⟩⟩ := ⟨⟨c, ⟨ch, h⟩⟩, rfl⟩
```

Cardinality version, useful for checking a port against a specific
original `.frm` file (§6):

```lean
theorem frame_count_eq_flagged_plus_admissible :
    Fintype.card Frame = Fintype.card FlaggedFrame + Fintype.card AdmissibleFrame := by
  simp [Frame, Fintype.card_sum]
```

**Termination.** The original's search (`next`/`step`/`iterate`,
`catpart0.2_frame.sml:190-281`) is a hand-written odometer walk whose
termination argument is "eventually the walk returns to its own starting
combination", checked by list equality at every step
(`catpart-archaeology.md` §3.3) — correct, but not visibly structural, and
not accompanied by a termination proof anywhere in the source. In the Lean
port termination is not a separate concern to prove: `AdmissibleFrame`,
`FlaggedFrame`, and `Frame` are `Fintype`s by construction (finite
`Category`, finite `Choice c` for every `c`, `DecidablePred Admissible`),
so `Finset.univ : Finset Frame` is total by the ordinary meaning of
`Fintype` — the closest thing to a "termination theorem" worth writing
down is the instance declaration itself:

```lean
instance : Fintype AdmissibleFrame := Subtype.fintype _
instance : Fintype FlaggedFrame     := Sigma.fintype
instance : Fintype Frame            := instFintypeSum
```

**The `[single]`/`[error]` disciplines.** Two separate claims, both
checked against the source in `catpart-archaeology.md` §1.4 above and §3
of the archaeology document:

1. *Isolation*: a flagged choice never appears jointly with any other
   category's choice — proved above
   (`flagged_not_in_admissible_frame`; and, dually, nothing in
   `FlaggedFrame`'s definition allows a second category's choice to be
   attached, so isolation for the flagged side is enforced by the type
   itself, not by a lemma).
2. *No distinction between `error` and `single` at generation time* — the
   original genuinely does not distinguish them (`catpart-archaeology.md`
   §1.4, §3.2; `is_flagged` tests `maybe_flag=Some _`, never
   `Some Error` vs `Some Single`). The port should state this as an
   explicit, checkable claim about `FlaggedFrame`, precisely so that a
   *future* change that wants to treat them differently (for instance,
   `single` choices participating in `t`-way coverage while `error`
   choices remain permanently isolated — a defensible product decision the
   original never made) is a visible, deliberate deviation rather than an
   accidental port bug:

   ```lean
   theorem flag_kind_irrelevant_to_isolation
       (c : Category) (ch₁ ch₂ : Choice c)
       (h₁ : (mods c ch₁).flag = some .error)
       (h₂ : (mods c ch₂).flag = some .single) :
       -- both are equally excluded from Unflagged c, by the same test
       (Unflagged c → False) ↔ True := by
     -- `Unflagged c` is nonempty in general (other choices may be
     -- unflagged); the point of this theorem is that ch₁, ch₂ are excluded
     -- from it for exactly the same reason, i.e. `(mods c ch).flag = none`
     -- fails for both, with no further case split on *which* flag.
     sorry -- statement sketch; the real content is that no lemma anywhere
           -- needs to case on `Flag`, matching the source finding above
   ```

   (This last theorem is included to make the *shape* of the claim
   precise — that no downstream lemma about `Unflagged`/`Admissible`/
   `AdmissibleFrame` ever needs to pattern-match on `Flag`'s two
   constructors — rather than as a polished statement; a real port would
   more likely express it as "`Unflagged c` factors through
   `(mods c ch).flag = none`, a single `Bool`-valued test, with `Flag`'s
   internal structure never inspected downstream", which is visibly true
   by reading §1.3/§2's definitions rather than needing its own proof.)

---

## 5. The extension actually needed: `t`-way coverage over the admissible frame set

`fileinfo.tsl`'s 735-frame `fileinfo.frm` (`catpart-archaeology.md` §3.3,
§6) is the concrete argument against ever wanting `Finset.univ :
Finset AdmissibleFrame` as the thing you actually run: full constrained
cross-product coverage grows as the product of (roughly) each category's
choice count, guard-pruning notwithstanding, and 735 generated test cases
for one function's spec is already impractical to execute, let alone read.
What is wanted instead is standard combinatorial-testing `t`-way
(covering-array) coverage: a *subset* of `AdmissibleFrame`, small relative
to its full cardinality, such that every combination of choices across any
`t` categories that *could* occur together in some admissible frame does
occur together in at least one selected frame.

**Coverability**, relative to the admissibility constraint (this is the
"admissibility gating expressed as a constraint category rather than a
post-hoc filter" requirement: a `t`-way selection must only be asked to
cover combinations the constraints actually allow, never combinations the
guards forbid — asking for uncoverable combinations, the way a naive
"cross every pair of categories" pairwise generator would, wastes the
whole exercise on combinations `generate` (§3) could never have produced
in the first place):

```lean
/-- A partial assignment over a finite set of categories `T`. -/
def PartialFrame (T : Finset Category) : Type :=
  (c : T) → Unflagged c.1

/-- `σ` (over categories `T`) is coverable iff some admissible frame agrees
    with it on every category in `T`. -/
def Coverable {T : Finset Category} (σ : PartialFrame T) : Prop :=
  ∃ f : AdmissibleFrame, ∀ c : T, f.1 c.1 = σ c
```

**A `t`-way selection and its coverage theorem:**

```lean
def IsTWaySelection (t : ℕ) (S : Finset AdmissibleFrame) : Prop :=
  ∀ T : Finset Category, T.card = t →
    ∀ σ : PartialFrame T, Coverable σ →
      ∃ f ∈ S, ∀ c : T, f.1 c.1 = σ c
```

A `t`-way selection's *coverage theorem* is exactly `IsTWaySelection t S`
for the `S` a concrete selection procedure produces; its *soundness*
theorem is `S ⊆ Finset.univ` (free, since `S : Finset AdmissibleFrame`
already only contains admissible frames — again the type is doing the
work); and a good selection procedure additionally has a *size* theorem
bounding `S.card` well below `Fintype.card AdmissibleFrame` — for
unconstrained specs, standard covering-array bounds are around
`v^t · log n` for `n` categories of at most `v` choices each, dramatically
below the `v^n`-shaped growth `fileinfo.frm` exhibits; the constrained
case (guards pruning the space `AdmissibleFrame` before the covering-array
step even starts) can only shrink that further, but does not have a clean
closed form and would need to be established per selection algorithm.

**On the selection procedure itself**: constructing a `t`-way selection
that is simultaneously small and satisfies `IsTWaySelection` in general is
the same combinatorial problem industrial category-partition/combinatorial
testing tools solve (IPOG and its relatives); a first Lean port should not
try to reprove state-of-the-art covering-array constructions. Two
pragmatically different postures are available and should be decided
explicitly, not by default:

1. **Verified-output, unverified-construction**: build `S` by an ordinary
   (possibly greedy, possibly randomized) Lean or meta-program search over
   `AdmissibleFrame`, then *check* `IsTWaySelection t S` for the produced
   `S` via `decide`/`native_decide` (both `Coverable` and the coverage
   predicate are decidable by the same `Fintype`/`Decidable` machinery as
   §2–§4, since `T`, `PartialFrame T`, and `S` are all finite). This is the
   "discover-then-pin" pattern already used elsewhere in this project's
   proof-search tooling (untrusted search, trusted, kernel-checked
   certificate) — recommended as the default, because it needs no new
   proof-engineering technique, only the `Decidable` instances already
   built in §2.
2. **Verified construction**: prove a specific greedy algorithm always
   produces an `IsTWaySelection t S`. Strictly stronger, and standard
   greedy covering-array constructions do have known correctness
   arguments, but this is genuine, open-ended proof work with no existing
   Mathlib support to lean on, and should not be scheduled before posture
   1 is working and has been useful in practice.

---

## 6. Worked example: `find.tsl`, end to end

Rendered in the Lean types above (`FindCategory`, `FindProperty`, one
choice inductive per category as sketched in §1.4), transcribing
`find.tsl:1-35` (`catpart-archaeology.md` §2.1–2.4 for the grammar this is
read against):

```lean
inductive FindProperty : Type
  | empty | nonempty | quoted | match
  deriving DecidableEq, Fintype, Repr

inductive PatternSizeChoice   : Type | empty | singleChar | manyChars | tooLong
  deriving DecidableEq, Fintype, Repr
inductive QuotingChoice        : Type | quoted | notQuoted | improperlyQuoted
  deriving DecidableEq, Fintype, Repr
inductive EmbeddedBlanksChoice : Type
  | none | oneBlank | severalBlanks | notApplicable
  deriving DecidableEq, Fintype, Repr
inductive EmbeddedQuotesChoice : Type
  | none | oneQuote | severalQuotes | notApplicable
  deriving DecidableEq, Fintype, Repr
inductive FileNameChoice : Type | good | noFile | omitted
  deriving DecidableEq, Fintype, Repr
inductive NumOccurrencesChoice : Type
  | none | exactlyOne | moreThanOne | notApplicable
  deriving DecidableEq, Fintype, Repr
inductive OccurrencesOnLineChoice : Type | one | moreThanOne | notApplicable
  deriving DecidableEq, Fintype, Repr

inductive FindCategory : Type
  | patternSize | quoting | embeddedBlanks | embeddedQuotes
  | fileName | numOccurrences | occurrencesOnLine
  deriving DecidableEq, Fintype, Repr

-- mods definitions elided; each is a direct transcription of one line of
-- find.tsl, e.g.:
def PatternSizeChoice.mods : PatternSizeChoice → Modifiers FindProperty
  | .empty      => { props := [.empty] }
  | .singleChar => { props := [.nonempty] }
  | .manyChars  => { props := [.nonempty] }
  | .tooLong    => { flag := some .error }

def OccurrencesOnLineChoice.mods : OccurrencesOnLineChoice → Modifiers FindProperty
  | .one           => { cond := some (.prop .match) }
  | .moreThanOne   => { cond := some (.prop .match), flag := some .single }
  | .notApplicable => { cond := some (.not (.prop .match)) }
```

**Expected frame count**, computed by the theorems of §4 rather than by
running a generator: `catpart-archaeology.md` §3.3 counts `find.tsl`'s
seven flagged choices and its unflagged cross-product bases `[3,2,4,3,1,3,2]`
(raw product 432), and reports the actual original output
(`find.frm`, 40 frames, 9.5 KB) is exactly `7` flagged singleton frames
plus `33` guard-admissible unflagged frames. The Lean port's obligation is:

```lean
example : Fintype.card FlaggedFrame = 7 := by decide
example : Fintype.card AdmissibleFrame = 33 := by decide
example : Fintype.card Frame = 40 := by
  rw [frame_count_eq_flagged_plus_admissible]; decide
```

If these three `decide`s go through once the spec is transcribed, the port
matches the original's own `find.frm` output exactly, on the original's
own example — the strongest evidence available that the port has not
silently narrowed or widened the coverage notion of §4. (These are stated
as expectations to check once the transcription exists; they have not been
run — no `.lean` file was created as part of this design.)

---

## 7. Staged implementation plan

The project's own tracked observation (`memory/effort-estimates.md`:
*"my refactor estimates here run ~4x pessimistic; mechanical restructuring
in this Lean development takes hours, not days"*) applies most strongly to
stages that are mechanical once the pattern is fixed (§7.1, §7.5) and least
to the genuinely open-ended one (§7.4). Both a naive estimate and the
4x-corrected one are given; treat the corrected number as the working
planning number, and the naive one as a ceiling if the pattern turns out
not to be as mechanical as expected.

**Recommendation on the parser question, asked for explicitly in the
brief**: skip a TSL text parser for the first version and specify test
specs directly as Lean `inductive`/`structure` declarations (§1, §6). Three
reasons, all following from §5's grammar comment: (1) the whole point of
the port is that undeclared-property and category/choice-mismatch errors
should be *compile* errors — a text parser reading external `.tsl` files
would have to re-implement its own validation pass to get the same
guarantee at parse time, duplicating work the Lean elaborator already does
for free on a structure literal; (2) `catpart-archaeology.md` §4 catalogues
how much of the original's actual difficulty was tooling (ML-Yacc/ML-Lex
version drift, `%header` mismatches, CM file format) rather than the
frame-generation mathematics itself — building a bespoke Lean parser
front-end re-opens exactly that class of maintenance risk for a part of
the system that is not where this project's value is; (3) a parser is
addable later, non-destructively, as a macro/elaborator that expands `.tsl`
syntax into the same `inductive`/`Modifiers` declarations §1/§6 already
produce by hand — so deferring it costs nothing structural now.

1. **Core library types** (§1–§2: `Cond`, `Cond.sat`, `Modifiers`,
   `Unflagged`, `otherProps`, `satisfied`, `Admissible`, and their
   `Decidable`/`Fintype` instances), written generically over
   `(Category, Choice, Prop)` once. Naive estimate: 1 day. Corrected
   (×0.25): **2–3 hours.** This is the highest-leverage stage: everything
   else specializes it.

2. **Frame types and the soundness/completeness theorems** (§3–§4, the
   `AdmissibleFrame`/`FlaggedFrame`/`Frame` definitions and their proofs,
   which are close to definitional given stage 1). Naive: 1 day. Corrected:
   **2–4 hours.**

3. **Worked example** (§6: `find.tsl` transcribed, the three `decide`
   checks against the original's own `find.frm` count). Naive: half a day.
   Corrected: **1–2 hours**, assuming stage 1–2 are solid; this stage is
   also the fastest way to discover if they are not.

4. **`t`-way selection** (§5): the `Coverable`/`IsTWaySelection`
   definitions and the "verified-output, unverified-construction" posture
   (build a candidate `S` by ordinary search, `decide` its coverage). This
   is the least mechanical stage — a real selection *procedure* (even a
   simple greedy one) is new code with its own design space, not a
   transcription of existing ML. Naive: 3–5 days. Corrected, with real
   uncertainty about whether the 4x factor holds for genuinely novel work
   rather than restructuring: **1–2 days**, and this is the stage most
   likely to blow its estimate; budget it separately from the others and
   check in after a fixed time-box rather than after a fixed deliverable.

5. **Integration with the existing sampler/search apparatus** (per
   `memory/probe-strategy-reach-vs-completeness.md` and
   `memory/search-tooling-preference.md`: the project already has a
   certificate-carrying, frontier-stratified sampling method for proof
   search; a `t`-way-selected `Finset AdmissibleFrame` is structurally the
   same kind of object — a small, coverage-justified sample of a large
   combinatorial space — so this stage is mostly plumbing a `Frame`
   generator into that existing harness as a source of test cases, rather
   than new theory). Concrete categories/choices for *this* project's own
   use (test frames for tactic behaviour, decision-procedure edge cases,
   or countermodel search parameters, rather than `find`'s file-search
   semantics) are not designed here and are the natural next step once
   stages 1–4 exist. Naive: 1–2 days. Corrected: **half a day to a day**,
   dominated by deciding *what* the categories should be for a specific
   proof-engineering target, which is a design question, not an
   engineering one, and cannot usefully be estimated in the abstract.

**Total corrected estimate, stages 1–3 (the part with no open design
question)**: on the order of a working day. Stage 4 and 5 depend on
decisions (which selection algorithm; which part of the proof-engineering
workflow to target first) that are better made after stages 1–3 exist and
have been tried on a second worked example beyond `find.tsl`, not
committed to in advance.
