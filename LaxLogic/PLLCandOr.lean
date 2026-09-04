import LaxLogic.PLLCandidate

/-!
# The attack on `cl_orL`: the consequence candidate

`PLLCandidate.lean` extracted the closure clauses and located the load on
`cl_orL`, the join clause. This file builds the first concrete candidate and
pushes it through all thirteen clauses, join first, to find out exactly what
breaks — the discipline of `docs/lax-interpolation-candidates-strategy.md`:
drive forward rule by rule, and let each non-closing step name its condition.

## The candidate

For a fixed **budget** `θ : PLLFormula` (intended: `p`-free), let

    Cθ θ Γ Ω j N  :=  Nonempty (LaxND (θ :: ⌜Γ⌝ ++ ⌜Ω⌝) (wrap j ⌜N⌝))

— derivability of the (wrapped) conclusion from the budget together with the
erased hypotheses, in the REFERENCE system `LaxND`. The focused calculus is the
*source* of the clauses only; nothing here depends on focused derivations.

The point: for this candidate the join clause is ∨-left, a theorem. If all
thirteen clauses hold, candidacy is nonvacuous, and the open question becomes
extremality in `θ` — the ∃p/∀p asymmetry in candidate form.
-/

namespace PLLND
namespace CandOr

open Polar Focused Candidate

/-- Hypotheses of an inversion sequent, erased. -/
def hyps (Γ : List Neg) (Ω : List Pos) : List PLLFormula :=
  Γ.map eraseNeg ++ Ω.map erasePos

/-- The consequence candidate at budget `θ`. -/
def Cθ (θ : PLLFormula) (Γ : List Neg) (Ω : List Pos) (j : JD) (N : Neg) : Prop :=
  Nonempty (LaxND (θ :: hyps Γ Ω) (wrap j (eraseNeg N)))

/-! ## Context plumbing -/

theorem mem_hyps_neg {Γ : List Neg} {Ω : List Pos} {M : Neg} (h : M ∈ Γ) :
    eraseNeg M ∈ hyps Γ Ω :=
  List.mem_append_left _ (List.mem_map_of_mem h)

theorem mem_hyps_pos {Γ : List Neg} {Ω : List Pos} {Q : Pos} (h : Q ∈ Ω) :
    erasePos Q ∈ hyps Γ Ω :=
  List.mem_append_right _ (List.mem_map_of_mem h)

/-- Membership in `hyps` with a positive at the head of `Ω`, unpacked. -/
theorem mem_hyps_cons {Γ : List Neg} {Ω : List Pos} {Q : Pos} {ψ : PLLFormula}
    (h : ψ ∈ hyps Γ (Q :: Ω)) : ψ = erasePos Q ∨ ψ ∈ hyps Γ Ω := by
  simp only [hyps, List.map_cons, List.mem_append, List.mem_cons] at h ⊢
  tauto

/-- Rebuild membership in `hyps` with a positive at the head of `Ω`. -/
theorem hyps_cons_of {Γ : List Neg} {Ω : List Pos} {Q : Pos} {ψ : PLLFormula}
    (h : ψ ∈ hyps Γ Ω) : ψ ∈ hyps Γ (Q :: Ω) := by
  simp only [hyps, List.map_cons, List.mem_append, List.mem_cons] at h ⊢
  tauto

/-! ## The thirteen clauses for `Cθ`

Join first, since it is the one under attack. -/

/-- **`cl_orL` HOLDS for `Cθ`** — the join clause is ∨-elimination.  This is
the clause the whole difficulty was traced to, and for the consequence
candidate it is a theorem. -/
theorem cθ_orL {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {P Q : Pos}
    {j : JD} {N : Neg} (h₁ : Cθ θ Γ (P :: Ω) j N) (h₂ : Cθ θ Γ (Q :: Ω) j N) :
    Cθ θ Γ (.or P Q :: Ω) j N := by
  obtain ⟨d₁⟩ := h₁
  obtain ⟨d₂⟩ := h₂
  -- the disjunction is among the hypotheses
  have hor : (erasePos P).or (erasePos Q) ∈ θ :: hyps Γ (.or P Q :: Ω) :=
    List.mem_cons_of_mem _ (mem_hyps_pos (List.mem_cons_self ..))
  refine ⟨.orElim (φ := erasePos P) (ψ := erasePos Q) (.iden hor) ?_ ?_⟩
  · -- branch context: erasePos P :: θ :: hyps Γ (P∨Q :: Ω); transport d₁
    refine d₁.rename ?_
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases mem_hyps_cons hψ with rfl | hψ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hyps_cons_of hψ))
  · refine d₂.rename ?_
    intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases mem_hyps_cons hψ with rfl | hψ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hyps_cons_of hψ))

/-! ## The remaining twelve clauses -/

/-- A general context-transport for `Cθ` statements. -/
theorem cθ_rename {θ : PLLFormula} {Γ Γ' : List Neg} {Ω Ω' : List Pos}
    {j : JD} {N : Neg}
    (H : ∀ ψ ∈ θ :: hyps Γ Ω, ψ ∈ θ :: hyps Γ' Ω')
    (h : Cθ θ Γ Ω j N) : Cθ θ Γ' Ω' j N := by
  obtain ⟨d⟩ := h; exact ⟨d.rename H⟩

/-- `cl_impR`: `⊃`-introduction. -/
theorem cθ_impR {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {Q : Pos}
    {N : Neg} (h : Cθ θ Γ (Q :: Ω) .tru N) : Cθ θ Γ Ω .tru (.imp Q N) := by
  obtain ⟨d⟩ := h
  exact ⟨.impIntro (d.rename (fun ψ hψ => by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · rcases mem_hyps_cons hψ with rfl | hψ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ)))⟩

/-- `cl_andR`: `∧`-introduction. -/
theorem cθ_andR {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {M N : Neg}
    (h₁ : Cθ θ Γ Ω .tru M) (h₂ : Cθ θ Γ Ω .tru N) :
    Cθ θ Γ Ω .tru (.and M N) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  exact ⟨.andIntro d₁ d₂⟩

/-- `cl_circR`: `wrap`-introduction — `◯P true` and `◯P lax` from `P lax`. -/
theorem cθ_circR {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {j : JD}
    {P : Pos} (h : Cθ θ Γ Ω .lax (.up P)) : Cθ θ Γ Ω j (.circ P) := by
  obtain ⟨d⟩ := h
  exact ⟨wrapIn (j := j) d⟩

/-- `cl_fls`: absurdity. -/
theorem cθ_fls {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {j : JD}
    {N : Neg} : Cθ θ Γ (.fls :: Ω) j N :=
  ⟨.falsoElim _ (.iden (List.mem_cons_of_mem _
    (mem_hyps_pos (List.mem_cons_self ..))))⟩

/-- `cl_downL`: the same hypothesis set, re-filed. -/
theorem cθ_downL {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {M : Neg}
    {j : JD} {N : Neg} (h : Cθ θ (M :: Γ) Ω j N) :
    Cθ θ Γ (.down M :: Ω) j N := by
  refine cθ_rename (fun ψ hψ => ?_) h
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map, erasePos] at hψ ⊢
  aesop

/-- `cl_atomL`: likewise. -/
theorem cθ_atomL {θ : PLLFormula} {Γ : List Neg} {Ω : List Pos} {a : String}
    {j : JD} {N : Neg} (h : Cθ θ (.up (.atom a) :: Γ) Ω j N) :
    Cθ θ Γ (.atom a :: Ω) j N := by
  refine cθ_rename (fun ψ hψ => ?_) h
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map, eraseNeg, erasePos] at hψ ⊢
  aesop

/-- `cl_init`: identity, at either flag. -/
theorem cθ_init {θ : PLLFormula} {Γ : List Neg} {j : JD} {a : String}
    (h : Neg.up (Pos.atom a) ∈ Γ) : Cθ θ Γ [] j (.up (.atom a)) :=
  ⟨wrapIn (.iden (List.mem_cons_of_mem _ (mem_hyps_neg h)))⟩

/-- `cl_orR` (and symmetrically `or2`): disjunct choice under the wrap. -/
theorem cθ_orR {θ : PLLFormula} {Γ : List Neg} {j : JD} {P Q : Pos}
    (h : Cθ θ Γ [] j (.up P)) : Cθ θ Γ [] j (.up (.or P Q)) := by
  obtain ⟨d⟩ := h
  exact ⟨wrapOr1 d⟩

theorem cθ_orR2 {θ : PLLFormula} {Γ : List Neg} {j : JD} {P Q : Pos}
    (h : Cθ θ Γ [] j (.up Q)) : Cθ θ Γ [] j (.up (.or P Q)) := by
  obtain ⟨d⟩ := h
  exact ⟨wrapOr2 d⟩

/-- `cl_rel`: `⌜↑↓N⌝ = ⌜N⌝` definitionally. -/
theorem cθ_rel {θ : PLLFormula} {Γ : List Neg} {j : JD} {N : Neg}
    (h : Cθ θ Γ [] j N) : Cθ θ Γ [] j (.up (.down N)) := h

/-- `cl_impL`: modus ponens into the continuation, via cut. -/
theorem cθ_impL {θ : PLLFormula} {Γ : List Neg} {j : JD} {Q : Pos} {N : Neg}
    {P : Pos} (hm : Neg.imp Q N ∈ Γ) (h₁ : Cθ θ Γ [] .tru (.up Q))
    (h₂ : Cθ θ (N :: Γ) [] j (.up P)) : Cθ θ Γ [] j (.up P) := by
  obtain ⟨d₁⟩ := h₁; obtain ⟨d₂⟩ := h₂
  -- from the implication hypothesis and d₁, get eraseNeg N
  have dN : LaxND (θ :: hyps Γ ([] : List Pos)) (eraseNeg N) :=
    .impElim (.iden (List.mem_cons_of_mem _ (mem_hyps_neg hm))) d₁
  -- cut it into d₂
  refine ⟨.impElim (.impIntro (d₂.rename (fun ψ hψ => ?_))) dN⟩
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map] at hψ ⊢
  aesop

/-- `cl_andL`: projection into the continuation. -/
theorem cθ_andL {θ : PLLFormula} {Γ : List Neg} {j : JD} {M N : Neg} {P : Pos}
    (hm : Neg.and M N ∈ Γ) (h : Cθ θ (M :: Γ) [] j (.up P)) :
    Cθ θ Γ [] j (.up P) := by
  obtain ⟨d⟩ := h
  have dM : LaxND (θ :: hyps Γ ([] : List Pos)) (eraseNeg M) :=
    .andElim1 (.iden (List.mem_cons_of_mem _ (mem_hyps_neg hm)))
  refine ⟨.impElim (.impIntro (d.rename (fun ψ hψ => ?_))) dM⟩
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map] at hψ ⊢
  aesop

theorem cθ_andL' {θ : PLLFormula} {Γ : List Neg} {j : JD} {M N : Neg} {P : Pos}
    (hm : Neg.and M N ∈ Γ) (h : Cθ θ (N :: Γ) [] j (.up P)) :
    Cθ θ Γ [] j (.up P) := by
  obtain ⟨d⟩ := h
  have dN : LaxND (θ :: hyps Γ ([] : List Pos)) (eraseNeg N) :=
    .andElim2 (.iden (List.mem_cons_of_mem _ (mem_hyps_neg hm)))
  refine ⟨.impElim (.impIntro (d.rename (fun ψ hψ => ?_))) dN⟩
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map] at hψ ⊢
  aesop

/-- `cl_circL` — **the contraction clause, and it holds by `laxElim` with the
`◯`-hypothesis RETAINED**.  `Q` enters `Ω` while `◯Q` stays in `Γ`: this is
exactly the retention discipline of the `G4c` repairs, now a theorem about the
candidate rather than a rule design. -/
theorem cθ_circL {θ : PLLFormula} {Γ : List Neg} {Q : Pos} {P : Pos}
    (hm : Neg.circ Q ∈ Γ) (h : Cθ θ Γ [Q] .lax (.up P)) :
    Cθ θ Γ [] .lax (.up P) := by
  obtain ⟨d⟩ := h
  -- d : LaxND (θ :: hyps Γ [Q]) ◯⌜P⌝;  goal the same without Q, using ◯⌜Q⌝ ∈ Γ
  refine ⟨.laxElim (φ := erasePos Q)
    (.iden (List.mem_cons_of_mem _ (mem_hyps_neg hm)))
    (d.rename (fun ψ hψ => ?_))⟩
  simp only [hyps, List.map_cons, List.mem_cons, List.mem_append,
    List.mem_map] at hψ ⊢
  aesop

/-! ## The instance: every budget yields a candidate -/

/-- **Every `p`-free budget `θ` yields an interpolation candidate.**  All
thirteen clauses hold for `Cθ`; the `p`-freeness of `θ` is not even needed for
the closure clauses (only `cl_init`'s side condition mentions `p`, and `Cθ`
satisfies the unconditional strengthening).  So candidacy is NONVACUOUS, and
the entire remaining content of uniform interpolation is EXTREMALITY: for a
given antecedent, a least budget among those whose candidate holds.  That is
the ∃p question, and the ∀p question is its dual — exactly the split of
`docs/ui-two-routes.md` §1, reached this time through the candidate method. -/
def candOf (p : String) (θ : PLLFormula) : Candidate.Cand p where
  C := Cθ θ
  cl_impR := cθ_impR
  cl_andR := cθ_andR
  cl_circR := cθ_circR
  cl_orL := cθ_orL
  cl_fls := cθ_fls
  cl_downL := cθ_downL
  cl_atomL := cθ_atomL
  cl_init := fun h _ => cθ_init h
  cl_orR := cθ_orR
  cl_rel := cθ_rel
  cl_impL := cθ_impL
  cl_andL := cθ_andL
  cl_andL' := cθ_andL'
  cl_circL := cθ_circL

/-! ## What remains: extremality

`candOf` says every budget is a candidate — candidacy is cheap.  The whole of
uniform interpolation is now the EXTREMALITY of the budget, stated here as the
target, not proved. -/

/-- Budgets are closed under strengthening: a stronger budget serves. -/
theorem cθ_strengthen {θ θ' : PLLFormula} {Γ : List Neg} {Ω : List Pos}
    {j : JD} {N : Neg} (hs : Nonempty (LaxND [θ'] θ))
    (h : Cθ θ Γ Ω j N) : Cθ θ' Γ Ω j N := by
  obtain ⟨ds⟩ := hs; obtain ⟨d⟩ := h
  -- derive θ in the θ'-context, then cut it into d
  have dθ : LaxND (θ' :: hyps Γ Ω) θ :=
    ds.rename (fun ψ hψ => by
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self ..
      · exact absurd hψ (List.not_mem_nil))
  refine ⟨.impElim (.impIntro (d.rename (fun ψ hψ => ?_))) dθ⟩
  rcases List.mem_cons.mp hψ with rfl | hψ
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hψ)

/-- **The extremality target** (`∃p`, candidate form): a `p`-free budget for
the sequent that is entailed by every other `p`-free budget — the weakest
`p`-free formula whose candidate accepts the sequent.  Uniform interpolation
for the sequent IS the inhabitation of this type for every sequent.  Stated,
not proved; this is where the ∃p/∀p asymmetry of `docs/ui-two-routes.md` §1
re-enters, and the directedness criterion is what inhabitation will need. -/
def ExtremalBudget (p : String) (Γ : List Neg) (Ω : List Pos) (j : JD)
    (N : Neg) : Type :=
  { θ : PLLFormula //
      Candidate.PFreeNeg p (polNeg θ) ∧ Cθ θ Γ Ω j N ∧
      ∀ θ' : PLLFormula, Candidate.PFreeNeg p (polNeg θ') → Cθ θ' Γ Ω j N →
        Nonempty (LaxND [θ'] θ) }

/-! ## The convergence theorem: extremality IS `∀p` of the sequent formula

`Cθ` curries: acceptance of a sequent by the budget `θ` is exactly entailment
of the sequent's one formula.  So the candidate route and the algebraic route
meet: `ExtremalBudget` is the greatest `p`-free formula below the sequent
formula — the propositional quantifier `∀p` itself. -/

/-- The sequent as one formula: hypotheses curried into the wrapped conclusion. -/
def seqFml (Γ : List Neg) (Ω : List Pos) (j : JD) (N : Neg) : PLLFormula :=
  (hyps Γ Ω).foldr .ifThen (wrap j (eraseNeg N))

/-- Currying: discharge a hypothesis block into the goal. -/
def curry : ∀ (L : List PLLFormula) {Δ : List PLLFormula} {g : PLLFormula},
    LaxND (L ++ Δ) g → LaxND Δ (L.foldr .ifThen g)
  | [], _, _, d => d
  | A :: L, Δ, g, d =>
      .impIntro (curry L (d.rename (fun ψ hψ => by
        simp only [List.mem_cons, List.mem_append] at hψ ⊢
        tauto)))

/-- Uncurrying: reinstate a hypothesis block from the goal. -/
def uncurry : ∀ (L : List PLLFormula) {Δ : List PLLFormula} {g : PLLFormula},
    LaxND Δ (L.foldr .ifThen g) → LaxND (L ++ Δ) g
  | [], _, _, d => d
  | A :: L, Δ, g, d => by
      have step : LaxND (A :: Δ) (L.foldr .ifThen g) :=
        .impElim (d.rename (fun ψ hψ => List.mem_cons_of_mem _ hψ))
          (.iden (List.mem_cons_self ..))
      exact (uncurry L step).rename (fun ψ hψ => by
        simp only [List.mem_cons, List.mem_append] at hψ ⊢
        tauto)

/-- **Acceptance is entailment**: `Cθ θ S ↔ θ ⊢ ⌜S⌝`. -/
theorem cθ_iff_entails (θ : PLLFormula) (Γ : List Neg) (Ω : List Pos)
    (j : JD) (N : Neg) :
    Cθ θ Γ Ω j N ↔ Nonempty (LaxND [θ] (seqFml Γ Ω j N)) := by
  constructor
  · rintro ⟨d⟩
    exact ⟨curry (hyps Γ Ω) (d.rename (fun ψ hψ => by
      simp only [List.mem_cons, List.mem_append] at hψ ⊢; tauto))⟩
  · rintro ⟨d⟩
    exact ⟨(uncurry (hyps Γ Ω) d).rename (fun ψ hψ => by
      simp only [List.mem_cons, List.mem_append] at hψ ⊢; tauto)⟩

/-- **The convergence theorem.**  `ExtremalBudget p S` is precisely the
propositional quantifier `∀p ⌜S⌝`: a greatest `p`-free formula entailing the
sequent formula.  The candidate method, run to completion, lands on the same
object the algebraic route (`docs/ui-two-routes.md` §1) identified as the hard
half — and `∃p` never appears, because the closure clauses absorbed it.

Consequence, recorded in `PROGRESS-POLAR.md` §4: uniform interpolation for PLL
holds iff for every sequent formula `φ` the ideal
`T = {ψ p-free : ψ ⊢ φ}` is principal.  `T` is an ideal (downward closed, and
`∨`-closed since `ψ₁ ⊢ φ` and `ψ₂ ⊢ φ` give `ψ₁∨ψ₂ ⊢ φ`); principality can
fail only through an infinite strictly ascending chain of `p`-free formulas
below `φ`, and at one variable "p-free" means CLOSED, where the repository has
a mechanised strictly ascending chain — the boxed odd rungs
(`chain_step_strict`).  The refutation hunt is therefore: a one-variable `φ`
whose closed lower ideal is generated by that chain. -/
theorem extremal_iff_forallp (p : String) (Γ : List Neg) (Ω : List Pos)
    (j : JD) (N : Neg) (θ : PLLFormula) :
    (Candidate.PFreeNeg p (polNeg θ) ∧ Cθ θ Γ Ω j N ∧
      ∀ θ' : PLLFormula, Candidate.PFreeNeg p (polNeg θ') → Cθ θ' Γ Ω j N →
        Nonempty (LaxND [θ'] θ))
    ↔ (Candidate.PFreeNeg p (polNeg θ) ∧
        Nonempty (LaxND [θ] (seqFml Γ Ω j N)) ∧
      ∀ θ' : PLLFormula, Candidate.PFreeNeg p (polNeg θ') →
        Nonempty (LaxND [θ'] (seqFml Γ Ω j N)) → Nonempty (LaxND [θ'] θ)) := by
  constructor
  · rintro ⟨hf, hc, hm⟩
    exact ⟨hf, (cθ_iff_entails ..).mp hc,
      fun θ' hf' hd => hm θ' hf' ((cθ_iff_entails ..).mpr hd)⟩
  · rintro ⟨hf, hd, hm⟩
    exact ⟨hf, (cθ_iff_entails ..).mpr hd,
      fun θ' hf' hc => hm θ' hf' ((cθ_iff_entails ..).mp hc)⟩

/-- **The degenerate case, inhabited**: when the sequent formula is itself
`p`-free, it is its own extremal budget — self-acceptance is the identity
axiom curried, and minimality is currying of the acceptance.  Minimality here
does not even use `p`-freeness of the competitor. -/
def extremalOfPFree (p : String) (Γ : List Neg) (Ω : List Pos) (j : JD)
    (N : Neg) (hf : Candidate.PFreeNeg p (polNeg (seqFml Γ Ω j N))) :
    ExtremalBudget p Γ Ω j N :=
  ⟨seqFml Γ Ω j N,
   hf,
   (cθ_iff_entails ..).mpr ⟨.iden (List.mem_cons_self ..)⟩,
   fun _ _ hc => (cθ_iff_entails ..).mp hc⟩

end CandOr
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.CandOr.cθ_orL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.cθ_orL

/-- info: 'PLLND.CandOr.cθ_circL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.cθ_circL

/-- info: 'PLLND.CandOr.candOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.candOf

/-- info: 'PLLND.CandOr.cθ_strengthen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PLLND.CandOr.cθ_strengthen

/-- info: 'PLLND.CandOr.cθ_iff_entails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.cθ_iff_entails

/-- info: 'PLLND.CandOr.extremal_iff_forallp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.extremal_iff_forallp

/-- info: 'PLLND.CandOr.extremalOfPFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.CandOr.extremalOfPFree
