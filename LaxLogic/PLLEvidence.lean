import LaxLogic.PLLCountermodelEmit

/-!
# Evidence, presented-strategy realisability, and the decoration theorems

The `⊩ᵖ` layer of the Route B programme (design: `docs/route-b-model.md`;
the uniform/strategy clauses `⊩ᵘ`/`⊩ˢ`, the separation triptych, and the
machine-checked obstruction that forces the presented clause live in
`LaxLogic/BeliefRealisability.lean`, which imports this file).

Contents:

* `Pca`, `Evidence` — a partial applicative structure with total pairing
  and tag decoding, and hereditary evidence for atoms over a constraint
  model;
* `realP` (`x ⊩ᵖ[Ev, κ, w] φ`) — **presented-strategy realisability**: the
  `⊃`-clause applies the realiser to the pair of the presented world-code
  and the argument, exactly as the `◯`-clause presents the future to the
  strategy.  The obstruction theorem `realS_fullness_obstruction`
  (`LaxLogic/BeliefRealisability.lean`) shows this presentation is *necessary*:
  without it no evidence assignment on a three-world frame is both
  atom-adequate and full, for any PCA with finite tables;
* `tokenEvidence`, `realP_adequate_and_full` — over any finite frame
  validated by the verified countermodel checker (`PLLCountermodelEmit`),
  token evidence makes `⊩ᵖ` **adequate** (realised implies forced) and
  **full** (forced formulas have explicit table-built realisers);
* `realP_refutes_sequent` — the squeeze: every checked countermodel is a
  `⊩ᵖ`-refutation, hypotheses realised and conclusion unrealisable;
* `Tbl`, `tblPca` — an explicit table algebra witnessing every hypothesis,
  so the closed capstones `realP_refutes_sequent_tbl` and
  `somehow_p_not_p_realP_tbl` assume nothing.

Together with `emitter_completeness` (`PLLFinComp.lean`) this yields the
completeness of PLL for `⊩ᵖ`-realisability — `PLLRealCompleteness.lean`.
-/

open PLLFormula

namespace PLLND
namespace BeliefReal

/-- A partial applicative structure with total pairing and tag decoding.
Application is partial (`Option`); `untag` is **total** — every element decodes
as a tagged value (as in Kleene's first algebra under Cantor pairing).  No
combinatory laws are required at this stage. -/
structure Pca where
  Carrier : Type
  app : Carrier → Carrier → Option Carrier
  pair : Carrier → Carrier → Carrier
  fst : Carrier → Carrier
  snd : Carrier → Carrier
  tag : Bool → Carrier → Carrier
  untag : Carrier → Bool × Carrier
  fst_pair : ∀ a b, fst (pair a b) = a
  snd_pair : ∀ a b, snd (pair a b) = b
  untag_tag : ∀ i a, untag (tag i a) = (i, a)

/-- Evidence over a constraint frame: for each atom and world, the set of
elements evidencing that atom there — hereditary along `Rᵢ` and full on the
fallible worlds. -/
structure Evidence (P : Pca) (C : ConstraintModel) where
  E : String → C.W → Set P.Carrier
  hered_E : ∀ {s : String} {w v : C.W}, C.Ri w v → E s w ⊆ E s v
  full_E : ∀ {s : String} {w : C.W}, w ∈ C.F → ∀ x : P.Carrier, x ∈ E s w

/-! ## `⊩ᵖ` — the presented clause family, and completeness by decoration

The obstruction (`realS_fullness_obstruction`, `LaxLogic/BeliefRealisability.lean`)
shows the `⊃`-clause must, like the `◯`-clause, receive
the code of the evaluation world: strategies exist, carry no world-marks, and
so an implication realiser fed the same strategy at two incomparable futures
cannot answer both.  `realP` makes that single change — the `⊃`-clause
applies the realiser to the *pair* of the presented world-code and the
argument; every other clause is exactly `realS`.

The payoff is the two-way bridge that `⊩ˢ` provably lacks, over any finite
checked frame decorated with *token evidence* (one token per atom, exactly
where the atom holds):

* **adequacy** — whatever is `⊩ᵖ`-realised is truth-forced;
* **fullness** — whatever is truth-forced has an explicit realiser, built by
  finite tables against the world-coding: the `∨`-witness *decides* the
  branch with the executable `forceB`, the `◯`-witness searches the finite
  frame for its constraint-witness, the `⊃`-witness looks up the consequent's
  witness at the presented world.

Consequently every countermodel validated by the verified checker is a
`⊩ᵖ`-refutation: at the refuting world all hypotheses are realised and the
conclusion is unrealisable (`realP_refutes_sequent`).  Combined with the
emitter this turns failed proof search into realisability countermodels; the
table hypotheses `htab`/`htabP` are met in Kleene's first algebra (finite
lookup tables are computable), and the development below is deliberately
free of `Classical.choice` — the branch decisions are made by `forceB`. -/

section PresentedClause

/-- `⊩ᵖ` — **presented-strategy** realisability: `realS` with the one
repair the obstruction demands.  In the `⊃`-clause the realiser is applied
to `pair (κ v) b` — the presented future together with the argument — just
as the `◯`-clause already presents `κ v` to the strategy. -/
def realP (P : Pca) {C : ConstraintModel} (Ev : Evidence P C) (κ : C.W → P.Carrier) :
    PLLFormula → P.Carrier → C.W → Prop
  | .prop s, x, w => w ∈ C.F ∨ x ∈ Ev.E s w
  | .falsePLL, _x, w => w ∈ C.F
  | .and φ ψ, x, w =>
      w ∈ C.F ∨ (realP P Ev κ φ (P.fst x) w ∧ realP P Ev κ ψ (P.snd x) w)
  | .or φ ψ, x, w =>
      w ∈ C.F ∨ ((P.untag x).1 = false ∧ realP P Ev κ φ (P.untag x).2 w)
             ∨ ((P.untag x).1 = true ∧ realP P Ev κ ψ (P.untag x).2 w)
  | .ifThen φ ψ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨
        (∀ b, realP P Ev κ φ b v →
          ∃ y, P.app x (P.pair (κ v) b) = some y ∧ realP P Ev κ ψ y v)
  | .somehow φ, x, w =>
      ∀ v, C.Ri w v → v ∈ C.F ∨
        (∃ y, P.app x (κ v) = some y ∧
          ∃ u, C.Rm v u ∧ P.fst y = κ u ∧ realP P Ev κ φ (P.snd y) u)

/-- `x ⊩ᵖ[Ev, κ, w] φ` — `x` presented-strategy-realises `φ` at `w`. -/
scoped notation:50 x:51 " ⊩ᵖ[" Ev ", " κ ", " w "] " φ:51 => realP _ Ev κ φ x w

variable {P : Pca} {M : FinCM}

/-- **Token evidence** on a checked frame: one token per atom, exactly where
the atom holds (fallible worlds evidence everything, as required). -/
def tokenEvidence (P : Pca) (M : FinCM) (h : M.WellFormed)
    (tok : String → P.Carrier) : Evidence P (M.toModel h) where
  E s w := {x | M.fallB w.1 = true ∨ (M.valB w.1 s = true ∧ x = tok s)}
  hered_E := by
    intro s w v hri x hx
    rcases hx with hf | ⟨hval, rfl⟩
    · exact .inl (h.2.2.2.1 _ w.2 _ v.2 hri hf)
    · rcases Bool.or_eq_true .. |>.mp hval with hmem | hf
      · exact .inr ⟨h.2.2.2.2 (w.1, s) (of_decide_eq_true hmem) _ v.2 hri, rfl⟩
      · exact .inl (h.2.2.2.1 _ w.2 _ v.2 hri hf)
  full_E := by
    intro s w hf x
    exact .inl hf

/-- **Adequacy and fullness for `⊩ᵖ`**, jointly, over any checked frame with
token evidence: realised implies forced, and forced formulas have explicit
realisers given by a per-world witness function.  The construction is
choice-free: all branch decisions are made by the executable `forceB`, and
the `◯`-witness is found by searching the finite frame. -/
theorem realP_adequate_and_full (h : M.WellFormed) (tok : String → P.Carrier)
    (κ : Fin M.n → P.Carrier)
    (htab : ∀ g : Fin M.n → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i))
    (htabP : ∀ g : Fin M.n → P.Carrier,
      ∃ s, ∀ i b, P.app s (P.pair (κ i) b) = some (g i)) :
    ∀ φ : PLLFormula,
      (∀ (w : Fin M.n) (x : P.Carrier),
        (x ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ) → (M.toModel h).force w φ) ∧
      (∃ wit : Fin M.n → P.Carrier, ∀ w : Fin M.n,
        (M.toModel h).force w φ →
          (wit w) ⊩ᵖ[tokenEvidence P M h tok, κ, w] φ) := by
  intro φ
  induction φ with
  | prop s =>
      constructor
      · intro w x hx
        rcases hx with hf | hx
        · show FinCM.valB M w.1 s = true
          simp only [FinCM.valB, Bool.or_eq_true]
          exact .inr hf
        · rcases hx with hf | ⟨hval, _⟩
          · show FinCM.valB M w.1 s = true
            simp only [FinCM.valB, Bool.or_eq_true]
            exact .inr hf
          · exact hval
      · refine ⟨fun _ => tok s, fun w hw => ?_⟩
        exact .inr (.inr ⟨hw, rfl⟩)
  | falsePLL =>
      constructor
      · intro w x hx
        exact hx
      · exact ⟨fun _ => tok "", fun w hw => hw⟩
  | and φ ψ ihφ ihψ =>
      obtain ⟨witφ, hwitφ⟩ := ihφ.2
      obtain ⟨witψ, hwitψ⟩ := ihψ.2
      constructor
      · intro w x hx
        rcases hx with hf | ⟨h₁, h₂⟩
        · exact (M.toModel h).force_of_fallible hf
        · exact ⟨ihφ.1 w _ h₁, ihψ.1 w _ h₂⟩
      · refine ⟨fun w => P.pair (witφ w) (witψ w), fun w hw => ?_⟩
        dsimp only
        refine .inr ⟨?_, ?_⟩
        · rw [P.fst_pair]; exact hwitφ w hw.1
        · rw [P.snd_pair]; exact hwitψ w hw.2
  | or φ ψ ihφ ihψ =>
      obtain ⟨witφ, hwitφ⟩ := ihφ.2
      obtain ⟨witψ, hwitψ⟩ := ihψ.2
      constructor
      · intro w x hx
        rcases hx with hf | ⟨_, hr⟩ | ⟨_, hr⟩
        · exact (M.toModel h).force_of_fallible hf
        · exact .inl (ihφ.1 w _ hr)
        · exact .inr (ihψ.1 w _ hr)
      · refine ⟨fun w =>
          if M.forceB w.1 φ = true then P.tag false (witφ w)
          else P.tag true (witψ w), fun w hw => ?_⟩
        dsimp only
        by_cases hb : M.forceB w.1 φ = true
        · rw [if_pos hb]
          refine .inr (.inl ?_)
          rw [P.untag_tag]
          exact ⟨rfl, hwitφ w ((M.force_iff h φ w).mpr hb)⟩
        · rw [if_neg hb]
          refine .inr (.inr ?_)
          rw [P.untag_tag]
          rcases hw with hφ | hψ
          · exact absurd ((M.force_iff h φ w).mp hφ) hb
          · exact ⟨rfl, hwitψ w hψ⟩
  | ifThen φ ψ ihφ ihψ =>
      obtain ⟨witψ, hwitψ⟩ := ihψ.2
      constructor
      · intro w x hx v hri hφv
        by_cases hf : v ∈ (M.toModel h).F
        · exact (M.toModel h).force_of_fallible hf
        · obtain ⟨witφ, hwitφ⟩ := ihφ.2
          obtain ⟨y, _, hy⟩ :=
            (hx v hri).resolve_left hf (witφ v) (hwitφ v hφv)
          exact ihψ.1 v y hy
      · obtain ⟨s, hs⟩ := htabP witψ
        refine ⟨fun _ => s, fun w hw v hri => ?_⟩
        by_cases hf : v ∈ (M.toModel h).F
        · exact .inl hf
        · refine .inr fun b hb => ⟨witψ v, hs v b, ?_⟩
          exact hwitψ v (hw v hri (ihφ.1 v b hb))
  | somehow φ ih =>
      obtain ⟨witφ, hwitφ⟩ := ih.2
      constructor
      · intro w x hx v hri
        by_cases hf : v ∈ (M.toModel h).F
        · exact ⟨v, (M.toModel h).refl_m v,
            (M.toModel h).force_of_fallible hf⟩
        · obtain ⟨y, _, u, hrm, _, hy⟩ := (hx v hri).resolve_left hf
          exact ⟨u, hrm, ih.1 u _ hy⟩
      · obtain ⟨s, hs⟩ := htab fun v =>
          match (List.finRange M.n).find?
              (fun u => M.rmB v.1 u.1 && M.forceB u.1 φ) with
          | some u => P.pair (κ u) (witφ u)
          | none => P.pair (κ v) (witφ v)
        refine ⟨fun _ => s, fun w hw v hri => ?_⟩
        by_cases hf : v ∈ (M.toModel h).F
        · exact .inl hf
        · obtain ⟨u₀, hrm₀, hu₀⟩ := hw v hri
          have hfind : ∃ u, (List.finRange M.n).find?
              (fun u => M.rmB v.1 u.1 && M.forceB u.1 φ) = some u := by
            cases hcase : (List.finRange M.n).find?
                (fun u => M.rmB v.1 u.1 && M.forceB u.1 φ) with
            | some u => exact ⟨u, rfl⟩
            | none =>
                exfalso
                have := List.find?_eq_none.mp hcase u₀ (List.mem_finRange u₀)
                rw [Bool.and_eq_true] at this
                exact this ⟨hrm₀, (M.force_iff h φ u₀).mp hu₀⟩
          obtain ⟨u, hu⟩ := hfind
          have hpred := List.find?_some hu
          rw [Bool.and_eq_true] at hpred
          refine .inr ⟨P.pair (κ u) (witφ u), ?_, u, hpred.1, P.fst_pair ..,
            ?_⟩
          · simp only [hs v, hu]
          · rw [P.snd_pair]
            exact hwitφ u ((M.force_iff h φ u).mpr hpred.2)

/-- **The completeness squeeze**: every countermodel validated by the
verified checker is a `⊩ᵖ`-refutation of its sequent — at the refuting
world every hypothesis is realised, and the conclusion is unrealisable. -/
theorem realP_refutes_sequent {w : Nat} {Γ : List PLLFormula}
    {C : PLLFormula} (hcheck : FinCM.checkB M w Γ C = true)
    (tok : String → P.Carrier) (κ : Fin M.n → P.Carrier)
    (htab : ∀ g : Fin M.n → P.Carrier, ∃ s, ∀ i, P.app s (κ i) = some (g i))
    (htabP : ∀ g : Fin M.n → P.Carrier,
      ∃ s, ∀ i b, P.app s (P.pair (κ i) b) = some (g i)) :
    ∃ hwf : M.WellFormed, ∃ hlt : w < M.n,
      (∀ ψ ∈ Γ, ∃ x, x ⊩ᵖ[tokenEvidence P M hwf tok, κ, ⟨w, hlt⟩] ψ) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence P M hwf tok, κ, ⟨w, hlt⟩] C := by
  simp only [FinCM.checkB, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true'] at hcheck
  obtain ⟨⟨⟨hwb, hlt⟩, hΓ⟩, hC⟩ := hcheck
  have hwf := FinCM.wellFormed_of_wellB hwb
  refine ⟨hwf, hlt, fun ψ hψ => ?_, fun ⟨x, hx⟩ => ?_⟩
  · obtain ⟨wit, hwit⟩ := (realP_adequate_and_full hwf tok κ htab htabP ψ).2
    exact ⟨wit ⟨w, hlt⟩,
      hwit _ ((M.force_iff hwf ψ ⟨w, hlt⟩).mpr (hΓ ψ hψ))⟩
  · have := (realP_adequate_and_full hwf tok κ htab htabP C).1 ⟨w, hlt⟩ x hx
    rw [M.force_iff hwf C ⟨w, hlt⟩, hC] at this
    exact Bool.false_ne_true this

/-- **Flagship instance**: at the pinned emitted countermodel for
`◯p ⊢ p` (`demoM`, `PLLCountermodelEmit.lean`), the hypothesis `◯p` is
`⊩ᵖ`-realised at the refuting world while `p` is unrealisable — the sequent
is realisability-refuted, not merely truth-refuted.  The checker certificate
discharges by `decide`. -/
theorem somehow_p_not_p_realP (P : Pca) (tok : String → P.Carrier)
    (κ : Fin demoM.n → P.Carrier)
    (htab : ∀ g : Fin demoM.n → P.Carrier,
      ∃ s, ∀ i, P.app s (κ i) = some (g i))
    (htabP : ∀ g : Fin demoM.n → P.Carrier,
      ∃ s, ∀ i b, P.app s (P.pair (κ i) b) = some (g i)) :
    ∃ hwf : demoM.WellFormed, ∃ hlt : 2 < demoM.n,
      (∃ x, x ⊩ᵖ[tokenEvidence P demoM hwf tok, κ, ⟨2, hlt⟩]
        (prop "p").somehow) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence P demoM hwf tok, κ, ⟨2, hlt⟩] (prop "p") := by
  obtain ⟨hwf, hlt, hΓ, hC⟩ := realP_refutes_sequent
    (M := demoM) (w := 2) (Γ := [(prop "p").somehow]) (C := prop "p")
    (by decide) tok κ htab htabP
  exact ⟨hwf, hlt, hΓ _ (List.mem_singleton_self _), hC⟩

end PresentedClause

/-! ## An explicit witness algebra — the table hypotheses are consistent

Everything above is hypothesis-style over an abstract `Pca` with tables
against the world-coding.  Here is an **explicit applicative structure**
meeting every assumed law, so the whole `⊩ᵖ` chain closes with *nothing*
assumed: elements are formal pairs, tags, base codes, and two kinds of
finite lookup tables — `tbl` answering on a world-code, `ptbl` answering on
the first component of a pair (the presented world), ignoring the second.
Application is the (decidable) lookup; the world-coding sends `i` to
`base i`.  Both table hypotheses hold by construction, choice-free.

(This algebra is not combinatorially complete — no `k`, `s` — and makes no
claim to be `K₁`; it is the *existence* witness.  The Kleene-algebra
instantiation, where tables are computable functions, is the classical
upgrade and remains open.) -/

section TableAlgebra

/-- Elements of the table algebra. -/
inductive Tbl where
  | base (n : ℕ)
  | pair (a b : Tbl)
  | tag (i : Bool) (a : Tbl)
  | tbl (l : List (ℕ × Tbl))
  | ptbl (l : List (ℕ × Tbl))

/-- Finite association lookup on `ℕ` keys. -/
def assoc : List (ℕ × Tbl) → ℕ → Option Tbl
  | [], _ => none
  | (k, r) :: l, x => if x = k then some r else assoc l x

/-- Application: tables look up world-codes; pair-tables look up the first
component of a pair (the presented world) and ignore the second. -/
def tapp : Tbl → Tbl → Option Tbl
  | .tbl l, .base k => assoc l k
  | .ptbl l, .pair (.base k) _ => assoc l k
  | _, _ => none

def tfst : Tbl → Tbl | .pair a _ => a | x => x
def tsnd : Tbl → Tbl | .pair _ b => b | x => x
def tuntag : Tbl → Bool × Tbl | .tag i a => (i, a) | x => (false, x)

/-- The table algebra as a `Pca`. -/
def tblPca : Pca where
  Carrier := Tbl
  app := tapp
  pair := .pair
  fst := tfst
  snd := tsnd
  tag := .tag
  untag := tuntag
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  untag_tag _ _ := rfl

/-- The world-coding: `i ↦ base i`. -/
def tblκ {n : ℕ} : Fin n → Tbl := fun i => .base i.1

theorem assoc_map {n : ℕ} (val : Fin n → Tbl) :
    ∀ (l : List (Fin n)) {i : Fin n}, i ∈ l →
      assoc (l.map fun j => (j.1, val j)) i.1 = some (val i) := by
  intro l
  induction l with
  | nil => intro i h; cases h
  | cons a l ih =>
      intro i h
      simp only [List.map_cons, assoc]
      by_cases he : i.1 = a.1
      · have hia : i = a := Fin.ext he
        subst hia
        rw [if_pos rfl]
      · rw [if_neg he]
        exact ih ((List.mem_cons.mp h).resolve_left
          fun hia => he (congrArg Fin.val hia))

/-- The table algebra meets the `◯`-witness table hypothesis. -/
theorem tbl_htab {n : ℕ} (g : Fin n → Tbl) :
    ∃ s, ∀ i, tblPca.app s (tblκ i) = some (g i) := by
  refine ⟨.tbl ((List.finRange n).map fun j => (j.1, g j)), fun i => ?_⟩
  show assoc ((List.finRange n).map fun j => (j.1, g j)) i.1 = some (g i)
  exact assoc_map g (List.finRange n) (List.mem_finRange i)

/-- …and the `⊃`-witness pair-table hypothesis. -/
theorem tbl_htabP {n : ℕ} (g : Fin n → Tbl) :
    ∃ s, ∀ i b, tblPca.app s (tblPca.pair (tblκ i) b) = some (g i) := by
  refine ⟨.ptbl ((List.finRange n).map fun j => (j.1, g j)), fun i _ => ?_⟩
  show assoc ((List.finRange n).map fun j => (j.1, g j)) i.1 = some (g i)
  exact assoc_map g (List.finRange n) (List.mem_finRange i)

/-- **The squeeze over the explicit algebra — nothing assumed**: every
countermodel validated by the verified checker is `⊩ᵖ`-refuted over
`tblPca`. -/
theorem realP_refutes_sequent_tbl {M : FinCM} {w : Nat}
    {Γ : List PLLFormula} {C : PLLFormula}
    (hcheck : FinCM.checkB M w Γ C = true) :
    ∃ hwf : M.WellFormed, ∃ hlt : w < M.n,
      (∀ ψ ∈ Γ, ∃ x,
        x ⊩ᵖ[tokenEvidence tblPca M hwf (fun _ => Tbl.base 0), tblκ,
          ⟨w, hlt⟩] ψ) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca M hwf (fun _ => Tbl.base 0), tblκ,
          ⟨w, hlt⟩] C :=
  realP_refutes_sequent (P := tblPca) hcheck (fun _ => Tbl.base 0) tblκ
    tbl_htab tbl_htabP

/-- **Fully closed flagship**: `◯p ⊢ p` is realisability-refuted — explicit
finite model, explicit evidence, explicit algebra; no hypotheses. -/
theorem somehow_p_not_p_realP_tbl :
    ∃ hwf : demoM.WellFormed, ∃ hlt : 2 < demoM.n,
      (∃ x, x ⊩ᵖ[tokenEvidence tblPca demoM hwf (fun _ => Tbl.base 0), tblκ,
        ⟨2, hlt⟩] (prop "p").somehow) ∧
      ¬ ∃ x, x ⊩ᵖ[tokenEvidence tblPca demoM hwf (fun _ => Tbl.base 0), tblκ,
        ⟨2, hlt⟩] (prop "p") :=
  somehow_p_not_p_realP tblPca (fun _ => Tbl.base 0) tblκ tbl_htab tbl_htabP

end TableAlgebra

end BeliefReal
end PLLND

#print axioms PLLND.BeliefReal.realP_adequate_and_full
#print axioms PLLND.BeliefReal.realP_refutes_sequent
#print axioms PLLND.BeliefReal.tbl_htab
#print axioms PLLND.BeliefReal.realP_refutes_sequent_tbl
#print axioms PLLND.BeliefReal.somehow_p_not_p_realP_tbl
