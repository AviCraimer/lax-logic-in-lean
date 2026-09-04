import LaxLogic.PLLSemUILayered

/-!
# The witnessing-triple amalgam for PLL (Lemma 5.4 scaffold)

The PLL form of the Litak–Visser/Visser amalgamation construction,
with the finite canonical model `canonFin cl` in the role of the
pre-Henkin model.  Everything structural is PROVED here — the depth
function and its strict drop, the witnessing triples, the amalgam
model with all frame legality, the assembly of the amalgamation
theorem from its two claims, with the root pair admissible and
forcing at the root converted through the descriptions functor.  The
two claims that carry the mathematics are stated as named `sorry`s:

* `wit_pbisim` (their Claim 1): the projection ⟨Δ, m⟩ ↦ m is an
  unbounded bisimulation off p — the zigzags maintain witnessing
  triples by the two-case budget argument (same theory: reuse the
  triple, transported along the move; strictly larger theory: the
  depth drops, so the spare budget 2·d(Δ′)+1 ≤ 2·d(Δ)−1 finances a
  fresh triple).  The Henkin-side moves are supplied by the PROVED
  functor clauses `trace_iforth` and `trace_mforth` — the promise
  component moves along Rₘ exactly as required.
* `wit_force` (their Claim 2): a pair forces φ ∈ cl iff φ ∈ Δ.val —
  induction on the adequate set with the same budget bookkeeping; the
  ⊃-case spends one i-zigzag, the ◯-case an i-zigzag and an m-zigzag
  (hence ◯'s crank of 2); fallible escapes absorb as in
  `descGraft_force_iff`.

Budget calibration: depth is measured by missing `val`-cardinality
(`canonDepth`), so the entry budget is `2·cl.card + 1` — coarser than
Litak–Visser's count of variables/implications/arrows, sound for the
same reason (every strict theory-extension adds a closure formula to
`val`).

## Design ledger (from the Lemma 5.4 mechanics, 2026-07-20)

Their induction finances every truth-lemma move by STRICT theory
growth: the ⊃-case grows the theory because the refuting world forces
the antecedent the theory lacked (`imp_unval_cases` — this ports
unchanged), and their Lewis-arrow case grows it by choosing the
refuting world <-maximal, so it *forces* the refuted arrow — a trick
that needs the converse well-foundedness of their modal relation.
PLL's `Rᵢ` is reflexive and `Rₘ` reflexive-transitive, so the
maximality trick is unavailable: a world refuting `◯χ` can NEVER force
it, and the ◯-case has genuine same-theory moves.  The witnessing
triple's primed pair `(k′, m′)` is their reservoir for same-theory
moves — but it only finances moves whose M-side is GIVEN (the zag of
their Claim 1); same-theory moves that start on the K-side (which only
PLL's ◯-case has) would need a fresh unprimed link at level `2d`, and
spending any link yields only `2d − 1`.

The canonical LEGO below replaces the maximality trick in both
directions where that is possible tonight:

* backward (`canon_box_dichotomy`): if `◯χ ∈ val` then either
  `χ ∈ val` — and reflexivity of `Rₘ` makes the pair its own
  row-witness, no move at all — or the canonical row-witness strictly
  grows the theory and the depth drop finances the move exactly as in
  their strict case;
* forward (`trace_box_refuter` + `promise_blocks_row`): a world
  refuting `◯χ` has an `Rᵢ`-successor whose description PROMISES `χ`
  (`χ ∈ mfal`), and promised formulas are refuted along the entire
  canonical `Rₘ`-row — so the amalgam refutes `◯χ` through the promise
  component of the canonical coordinate alone, with no `Rₘ`-move in
  `M`;
* the fallible escape (`traceT_mfal_empty_of_fallible`, `canonTop`,
  `rm_canonTop_iff`): a fallible row-member erases all promises, so
  escape rows land on the canonical top, which is reached along the
  canonical `Rₘ` precisely from promise-free worlds.

THE REMAINING WALL (open): the forward ◯-case when the promising
successor `v ≽ᵢ k` has the SAME `val`-trace as `k`.  The promise pair
`⟨trace v, m₂⟩` then has unchanged depth `d`, its admissibility needs
an unprimed link at `2d`, and all spends yield `2d − 1`.  The two
rescues that work elsewhere fail here: reflexivity gives nothing (the
promise is genuinely new), and the transitivity rescue (`m₂ := m`,
reusing `k`'s own link for `v`) would need closure-trace-equality to
imply rank-`2d` fragment-agreement between `v` and `k`, which is false
in general — the closure is `Sub φ`, the fragment is everything of
bounded rank.  The candidate missing clause was the SAME-TRACE
NO-DESCENT property of the concrete agreement relation: if `k` agrees
with `m` at rank `n`, and `v ≽ᵢ k` has the same closure-description as
`k`, then some `m₂ ≽ᵢ m` agrees with `v` at rank `n` (not `n − 1`).

PROBE VERDICT (`wip/samval_probe.lean`, 2026-07-20): REFUTED at the
list-agreement surrogate level.  Variable-free pass: clean (0
failures; nontrivial same-trace moves vanish as the closure grows:
109/5/0 over the three closures).  One-atom pass (650 decorated
models, 2,377,307 agreeing pairs): 499/44/12 failures over the
closures `[⊥,q]` / `[⊥,q,◯q]` / `Sub(◯q⊃q)∪{⊥}` — the gap row's own
adequate set included.  Decoded shape: the moved world is a RIGID
DEAD-END (`q ∧ ¬◯⊥`, crank 3); the partner model has no dead-end
above `w′`; the roots still agree at low rank because the absence of
a dead-end registers only one rank higher (`¬¬◯⊥`, crank 4).  So the
one-level descent of `agree_iforth` is semantically sharp even under
closure-trace-equality, and the same-theory ◯-forward case cannot be
financed by level preservation.  The open design question is what
replaces the unprimed `2d`-link at promise pairs; the decoded failures
all involve dead-end successors (the rigid postponement points of the
residue-probe decodings), which may admit a dedicated clause.
-/

open PLLFormula

namespace PLLND
namespace SemUI

open FinComp

/-! ## Depth in the finite canonical model -/

/-- Depth of a canonical theory: how many closure formulas its `val`
is still missing.  The budget financier: strict extensions strictly
drop it. -/
def canonDepth (cl : Finset PLLFormula) (T : (canonFin cl).W) : Nat :=
  cl.card - T.1.val.card

theorem canonDepth_le (cl : Finset PLLFormula) (T : (canonFin cl).W) :
    canonDepth cl T ≤ cl.card :=
  Nat.sub_le _ _

/-- **Strict extensions strictly drop the depth**: a proper
`val`-inclusion between canonical theories loses at least one unit of
budget. -/
theorem canonDepth_lt {cl : Finset PLLFormula} {T T' : (canonFin cl).W}
    (hsub : T.1.val ⊆ T'.1.val) (hne : T.1.val ≠ T'.1.val) :
    canonDepth cl T' < canonDepth cl T := by
  have hlt : T.1.val.card < T'.1.val.card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
  have hle : T'.1.val.card ≤ cl.card :=
    Finset.card_le_card T'.2.2.1.1
  unfold canonDepth
  omega

/-! ## Canonical LEGO for the ◯-case (all PROVED)

The pieces that replace Litak–Visser's strictness tricks in the
◯-induction, per the design ledger above. -/

/-- **Promises block the canonical row**: a formula promised by a
canonical world is validated by none of its `Rₘ`-successors — the
forward ◯-case refutes through the promise component alone. -/
theorem promise_blocks_row {cl : Finset PLLFormula} {χ : PLLFormula}
    {Δ Δ₂ : (canonFin cl).W} (hχ : χ ∈ Δ.1.mfal)
    (hRm : (canonFin cl).Rm Δ Δ₂) : χ ∉ Δ₂.1.val :=
  fun hv => Δ₂.2.not_mem_fal_of_mem_val hv (Δ₂.2.mfal_sub_fal (hRm.2 hχ))

/-- **The forward refuter promises**: a world refuting `◯χ` has an
`Rᵢ`-successor whose description promises `χ`. -/
theorem trace_box_refuter {C : ConstraintModel} {cl : Finset PLLFormula}
    {χ : PLLFormula} (hχcl : χ ∈ cl) {k : C.W}
    (h : ¬ C.force k χ.somehow) :
    ∃ v, C.Ri k v ∧ χ ∈ (traceT C cl v).mfal := by
  by_contra hc
  apply h
  intro v hkv
  by_contra hno
  exact hc ⟨v, hkv, mem_traceT_mfal.mpr
    ⟨hχcl, fun u hu hf => hno ⟨u, hu, hf⟩⟩⟩

/-- **The backward dichotomy (reflexivity rescue)**: a validated `◯χ`
has a canonical row-witness that either is the world itself (`χ`
already validated — `Rₘ` is reflexive, so no bisimulation move is
spent) or strictly grows the theory, so the move is financed by the
depth drop exactly as in the Litak–Visser strict case.  This replaces
their <-maximality trick, which needs converse well-foundedness. -/
theorem canon_box_dichotomy {cl : Finset PLLFormula} (hcl : SubClosed cl)
    {χ : PLLFormula} (hbox : χ.somehow ∈ cl) (hχ : χ ∈ cl)
    (T : (canonFin cl).W) (h : χ.somehow ∈ T.1.val) :
    χ ∈ T.1.val ∨
      ∃ S : (canonFin cl).W, (canonFin cl).Rm T S ∧ χ ∈ S.1.val ∧
        canonDepth cl S < canonDepth cl T := by
  by_cases hself : χ ∈ T.1.val
  · exact .inl hself
  · have hf : (canonFin cl).force T χ.somehow :=
      (FinComp.truth_lemma hcl _ hbox T).1 h
    obtain ⟨S, hRm, hSχ⟩ := hf T ((canonFin cl).refl_i T)
    have hSval : χ ∈ S.1.val := (canonFin_force_iff hcl hχ S).mp hSχ
    refine .inr ⟨S, hRm, hSval, canonDepth_lt hRm.1 ?_⟩
    intro hEq
    exact hself (by rw [hEq]; exact hSval)

/-- Validated consequents validate their implications (deductive
closure by the K-combinator): half of the ⊃-case split. -/
theorem imp_val_of_val {cl : Finset PLLFormula} {ξ ζ : PLLFormula}
    (T : (canonFin cl).W) (himp : ξ.ifThen ζ ∈ cl) (hζ : ζ ∈ T.1.val) :
    ξ.ifThen ζ ∈ T.1.val :=
  T.2.ded_closed himp
    (SetDeriv.deduct (SetDeriv.of_mem (Set.mem_insert_of_mem _
      (Finset.mem_coe.mpr hζ))))

/-- **The ⊃-case split, exhaustive with guaranteed strictness**: an
unvalidated implication either fails at the world itself (antecedent
validated, consequent falsified — refute in place, no move) or its
antecedent is unvalidated, and then any refuting witness forces a
formula the theory lacks — the strict-growth trick that ports from
Litak–Visser unchanged. -/
theorem imp_unval_cases {cl : Finset PLLFormula} (hcl : SubClosed cl)
    {ξ ζ : PLLFormula} (T : (canonFin cl).W) (himp : ξ.ifThen ζ ∈ cl)
    (h : ξ.ifThen ζ ∉ T.1.val) :
    (ξ ∈ T.1.val ∧ ζ ∈ T.1.fal) ∨ ξ ∉ T.1.val := by
  by_cases hξ : ξ ∈ T.1.val
  · rcases T.2.2.2 ζ (hcl.imp_right himp) with hv | hf
    · exact absurd (imp_val_of_val T himp hv) h
    · exact .inl ⟨hξ, hf⟩
  · exact .inr hξ

/-- **Strict growth of descriptions**: a witness above `k` forcing a
tracked formula the description of `k` lacks strictly extends the
`val`-trace — the depth financier for all forward strict cases. -/
theorem traceT_val_ssubset {C : ConstraintModel} {cl : Finset PLLFormula}
    {k v : C.W} (hkv : C.Ri k v) {ξ : PLLFormula} (hξcl : ξ ∈ cl)
    (hforce : C.force v ξ) (hnew : ξ ∉ (traceT C cl k).val) :
    (traceT C cl k).val ⊂ (traceT C cl v).val := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro φ hφ
    obtain ⟨hφcl, hf⟩ := mem_traceT_val.mp hφ
    exact mem_traceT_val.mpr ⟨hφcl, C.force_hered hkv hf⟩
  · intro hEq
    exact hnew (by rw [hEq]; exact mem_traceT_val.mpr ⟨hξcl, hforce⟩)

/-- **Fallible row-members erase promises**: descriptions of worlds
whose row hits the fallible set promise nothing (fallible worlds force
everything). -/
theorem traceT_mfal_empty_of_fallible {C : ConstraintModel}
    {cl : Finset PLLFormula} {k u : C.W} (hu : C.Rm k u) (hF : u ∈ C.F) :
    (traceT C cl k).mfal = ∅ :=
  Finset.eq_empty_iff_forall_notMem.mpr fun _χ hχ =>
    (mem_traceT_mfal.mp hχ).2 u hu (C.force_of_fallible hF)

/-- The canonical top: everything validated, nothing falsified,
nothing promised.  Consistent outright, fallible once `⊥ ∈ cl`. -/
def canonTop (cl : Finset PLLFormula) : (canonFin cl).W :=
  ⟨⟨cl, ∅, ∅⟩, cons_of_empty_falm rfl rfl,
    ⟨subset_rfl, Finset.empty_subset _, Finset.empty_subset _⟩,
    fun _φ hφ => .inl hφ⟩

theorem canonTop_fallible {cl : Finset PLLFormula} (hcl : SubClosed cl) :
    canonTop cl ∈ (canonFin cl).F := hcl.bot

/-- A canonical world reaches the top along `Rₘ` exactly when it
promises nothing — where the fallible escapes of the m-zigzag land. -/
theorem rm_canonTop_iff {cl : Finset PLLFormula} (Δ : (canonFin cl).W) :
    (canonFin cl).Rm Δ (canonTop cl) ↔ Δ.1.mfal = ∅ := by
  constructor
  · intro h
    exact Finset.subset_empty.mp h.2
  · intro h
    refine ⟨Δ.2.2.1.1, ?_⟩
    rw [h]
    exact Finset.empty_subset _

/-! ## Witnessing triples -/

variable {p : String} {K M : ConstraintModel}

/-- **Witnessing triple** for a pair ⟨Δ, m⟩ (Litak–Visser Lemma 5.4):
worlds k′ ≼ k of K both describing Δ, a shadow m′ ≼ m, with the
layered links k′ Z_{2d+1} m′ and k Z_{2d} m, d the canonical depth of
Δ. -/
structure WitTriple (cl : Finset PLLFormula)
    (B : LayeredBisimE (fun a => a ≠ p) K M)
    (Δ : (canonFin cl).W) (m : M.W) where
  k' : K.W
  k : K.W
  m' : M.W
  hΔk : (traceT K cl k) = Δ.1
  hΔk' : (traceT K cl k') = Δ.1
  hik : K.Ri k' k
  him : M.Ri m' m
  hZ' : B.Z (2 * canonDepth cl Δ + 1) k' m'
  hZ : B.Z (2 * canonDepth cl Δ) k m

/-! ## The amalgam model -/

variable (cl : Finset PLLFormula) (B : LayeredBisimE (fun a => a ≠ p) K M)

/-- The amalgam: admissible pairs ⟨Δ, m⟩, relations componentwise
(the canonical side carries the promise-aware `Rₘ`).  Valuation in
the `descGraft` discipline rather than Litak–Visser's union clause:
atoms other than `p` and fallibility read the M-COORDINATE (the
canonical model forces every out-of-closure atom — the filtration
convention — so a union valuation would break the p-variant claim on
untracked atoms); `p` reads the theory coordinate, with the
M-fallibility disjunct restoring fullness on F. -/
def witAmalgam : ConstraintModel where
  W := {q : (canonFin cl).W × M.W // Nonempty (WitTriple cl B q.1 q.2)}
  Ri := fun a b => (canonFin cl).Ri a.1.1 b.1.1 ∧ M.Ri a.1.2 b.1.2
  Rm := fun a b => (canonFin cl).Rm a.1.1 b.1.1 ∧ M.Rm a.1.2 b.1.2
  F := fun a => a.1.2 ∈ M.F
  V := fun x a =>
    if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
    else a.1.2 ∈ M.V x
  refl_i := fun a => ⟨(canonFin cl).refl_i _, M.refl_i _⟩
  trans_i := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_i h₁.1 h₂.1, M.trans_i h₁.2 h₂.2⟩
  refl_m := fun a => ⟨(canonFin cl).refl_m _, M.refl_m _⟩
  trans_m := fun h₁ h₂ =>
    ⟨(canonFin cl).trans_m h₁.1 h₂.1, M.trans_m h₁.2 h₂.2⟩
  sub_mi := fun h => ⟨(canonFin cl).sub_mi h.1, M.sub_mi h.2⟩
  hered_F := fun h hF => M.hered_F h.2 hF
  hered_V := by
    intro x a b h hv
    have hv' : (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x) := hv
    show (if x = p then b.1.1 ∈ (canonFin cl).V x ∨ b.1.2 ∈ M.F
        else b.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx] at hv' ⊢
      rcases hv' with hΔ | hm
      · exact Or.inl ((canonFin cl).hered_V h.1 hΔ)
      · exact Or.inr (M.hered_F h.2 hm)
    · rw [if_neg hx] at hv' ⊢
      exact M.hered_V h.2 hv'
  full_F := by
    intro x a hF
    show (if x = p then a.1.1 ∈ (canonFin cl).V x ∨ a.1.2 ∈ M.F
        else a.1.2 ∈ M.V x)
    by_cases hx : x = p
    · rw [if_pos hx]
      exact Or.inr hF
    · rw [if_neg hx]
      exact M.full_F hF

/-! ## The two claims (the open mathematics) -/

/-- **Claim 1 (their proof of Lemma 5.4; OPEN)**: the projection to
the M-coordinate is an unbounded bisimulation off p — the amalgam is
a p-variant of M.  Proof shape: Z := graph of the projection; zig is
componentwise; zag maintains a witnessing triple for the moved pair
by the two-case budget argument, with the Henkin-side move supplied
by `trace_iforth` (Rᵢ) resp. `trace_mforth` (Rₘ, promises included)
and the depth drop `canonDepth_lt` paying for the fresh triple in the
strictly-up case.  Atoms off p: for a ≠ p tracked in the pair, the
theory coordinate and the M-coordinate agree through the triple's
links (their displayed "Δ ⊩ p ⇔ k ⊩ p ⇔ m ⊩ p"); fallibility: the
links match fallibility at every level. -/
theorem wit_pbisim :
    ∃ C : PBisim p M (witAmalgam cl B),
      ∀ (q : (witAmalgam cl B).W), C.Z q.1.2 q := by
  sorry

/-- **Claim 2 (their proof of Lemma 5.4; OPEN)**: a pair forces a
closure formula iff its theory coordinate contains it.  Induction on
the adequate set; ⊃ spends one i-zigzag, ◯ an i-zigzag and an
m-zigzag; the truth-lemma infrastructure of `canonFin` bridges
membership and canonical forcing; fallible escapes absorb as in
`descGraft_force_iff`. -/
theorem wit_force (hcl : SubClosed cl) :
    ∀ (q : (witAmalgam cl B).W) (φ : PLLFormula), φ ∈ cl →
      ((witAmalgam cl B).force q φ ↔ φ ∈ q.1.1.1.val) := by
  sorry

/-! ## The assembly (PROVED modulo the claims) -/

/-- **The amalgamation theorem, assembled**: from a layered link of
budget `2·cl.card + 1` between k₀ and m₀, a p-variant of M whose
distinguished world agrees with k₀ on the whole closure.  The root
pair is ⟨description of k₀, m₀⟩, admissible by the degenerate
witnessing triple (k₀, k₀, m₀) after stepping the budget down to the
root theory's depth; forcing at the root converts through the
descriptions functor. -/
theorem amalgamation_assembled (hcl : SubClosed cl)
    (k₀ : K.W) (m₀ : M.W)
    (hB : B.Z (2 * cl.card + 1) k₀ m₀) :
    ∃ (N : ConstraintModel) (C : PBisim p M N) (n₀ : N.W),
      C.Z m₀ n₀ ∧ ∀ φ ∈ cl, (N.force n₀ φ ↔ K.force k₀ φ) := by
  classical
  -- the root theory and its admissibility
  set Δ₀ : (canonFin cl).W := trace K cl k₀ with hΔ₀
  have hbudget : 2 * canonDepth cl Δ₀ + 1 ≤ 2 * cl.card + 1 := by
    have := canonDepth_le cl Δ₀; omega
  have htrip : Nonempty (WitTriple cl B Δ₀ m₀) := by
    refine ⟨⟨k₀, k₀, m₀, rfl, rfl, K.refl_i _, M.refl_i _, ?_, ?_⟩⟩
    · exact B.mono_le hbudget hB
    · exact B.mono_le (by omega) hB
  obtain ⟨C, hC⟩ := wit_pbisim cl B
  refine ⟨witAmalgam cl B, C, ⟨(Δ₀, m₀), htrip⟩,
    hC ⟨(Δ₀, m₀), htrip⟩, ?_⟩
  intro φ hφ
  rw [wit_force cl B hcl _ φ hφ]
  -- membership in the root theory is forcing at k₀, by the functor
  constructor
  · intro h
    exact (mem_traceT_val.mp h).2
  · intro h
    exact mem_traceT_val.mpr ⟨hφ, h⟩

/-! ## Axiom audit (assembly only; the claims are sorried) -/

/--
info: 'PLLND.SemUI.canonDepth_lt' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canonDepth_lt

/--
info: 'PLLND.SemUI.promise_blocks_row' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms promise_blocks_row

/--
info: 'PLLND.SemUI.trace_box_refuter' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms trace_box_refuter

/--
info: 'PLLND.SemUI.canon_box_dichotomy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canon_box_dichotomy

/--
info: 'PLLND.SemUI.imp_unval_cases' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms imp_unval_cases

/--
info: 'PLLND.SemUI.traceT_val_ssubset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms traceT_val_ssubset

/--
info: 'PLLND.SemUI.traceT_mfal_empty_of_fallible' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms traceT_mfal_empty_of_fallible

/--
info: 'PLLND.SemUI.rm_canonTop_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms rm_canonTop_iff

end SemUI
end PLLND
