import LaxLogic.PLLG4Dec

/-!
# Uniform interpolation, phase 2: the Pitts quantifiers

`interE p fuel Γ` — the ∃-quantifier for contexts (strongest p-free
consequence of `Γ`, to fuel depth), conjunction-shaped; and
`interA p fuel Γ C` — the ∀-quantifier for sequents (weakest p-free
antecedent `X` with `X, Γ ⊢ C`), disjunction-shaped.  Both by **plain
fuel recursion** — no termination order on sequents, the ingredient
Iemhoff's method lacks for retention calculi: adequacy will instead
ride `height_bound`, the pigeonhole bound extracted from the decider.

The clause sets follow the rules of the cumulative calculus `G4s`,
including the three *lax* clauses this development contributes:

* `◯ E_p(χ :: Γ)` for each box `◯χ ∈ Γ` (opening);
* `A_p(Γ ⇒ A) → E_p(B :: Γ)` for each `◯A→B ∈ Γ` (`R◯→″`-firing);
* `A_p(X :: Γ ⇒ ◯A) → E_p(B :: Γ)` for each such pair with a witness
  box `◯X ∈ Γ` (`L◯→″`-firing);

and their `interA`-side analogues.
-/

open PLLFormula

namespace PLLND

/-- Big conjunction; `[]` is `⊤ = ⊥→⊥`. -/
def andAll : List PLLFormula → PLLFormula
  | [] => truePLL
  | φ :: l => φ.and (andAll l)

/-- Big disjunction; `[]` is `⊥`. -/
def orAll : List PLLFormula → PLLFormula
  | [] => falsePLL
  | φ :: l => φ.or (orAll l)

namespace G4c

theorem truePLL_intro (Γ : List PLLFormula) : G4c Γ truePLL :=
  impR (botL (List.Mem.head _))

theorem andAll_intro : ∀ {l : List PLLFormula} {Γ : List PLLFormula},
    (∀ φ ∈ l, G4c Γ φ) → G4c Γ (andAll l) := by
  intro l
  induction l with
  | nil => intro Γ _; exact truePLL_intro Γ
  | cons φ l ih =>
      intro Γ h
      exact andR (h φ (.head _)) (ih fun ψ hψ => h ψ (.tail _ hψ))

theorem andAll_elim : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Δ : List PLLFormula} {D : PLLFormula},
    G4c (φ :: Δ) D → G4c (andAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Δ D h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · -- φ is the head: expose it with andL
        exact andL (List.Perm.refl _)
          ((h.weaken (andAll l)).perm
            ((List.Perm.swap _ _ _).trans (List.Perm.refl _)))
      · -- φ is in the tail
        refine andL (List.Perm.refl _) ?_
        have := ih hmem' (Δ := x :: Δ) (D := D)
          ((h.weaken x).perm (List.Perm.swap _ _ _))
        exact (this.perm (List.Perm.swap _ _ _))

theorem orAll_intro : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Γ : List PLLFormula}, G4c Γ φ → G4c Γ (orAll l) := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Γ h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact orR1 h
      · exact orR2 (ih hmem' h)

theorem orAll_elim : ∀ {l : List PLLFormula} {Δ : List PLLFormula}
    {D : PLLFormula}, (∀ φ ∈ l, G4c (φ :: Δ) D) →
    G4c (orAll l :: Δ) D := by
  intro l
  induction l with
  | nil => intro Δ D _; exact botL (.head _)
  | cons x l ih =>
      intro Δ D h
      exact orL (List.Perm.refl _) (h x (.head _))
        (ih fun ψ hψ => h ψ (.tail _ hψ))

end G4c

/-! ### `G4s`-level toolkit

The soundness and adequacy properties of the quantifiers live at the
cumulative set calculus `G4s`, whose rules match the clause contexts
verbatim (`(A :: Γ).toFinset = insert A Γ.toFinset`); everything is
packaged back to `G4c` at the end via `G4c.iff_set`.  First the
height-erased rule lifters (two-premise rules take a `max`), then the
big-operator introduction/elimination lemmas.
-/

namespace G4s

theorem weaken_subset {Γ Γ' : Finset PLLFormula} {C : PLLFormula}
    (d : G4s Γ C) (h : Γ ⊆ Γ') : G4s Γ' C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n, d.weaken_subset h⟩

theorem init {Γ : Finset PLLFormula} {a : String} (h : prop a ∈ Γ) :
    G4s Γ (prop a) := ⟨0, .init h⟩

theorem botL {Γ : Finset PLLFormula} {C : PLLFormula}
    (h : falsePLL ∈ Γ) : G4s Γ C := ⟨0, .botL h⟩

theorem andR {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d₁ : G4s Γ A) (d₂ : G4s Γ B) : G4s Γ (A.and B) := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .andR (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem orR1 {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s Γ A) : G4s Γ (A.or B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .orR1 d⟩

theorem orR2 {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s Γ B) : G4s Γ (A.or B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .orR2 d⟩

theorem impR {Γ : Finset PLLFormula} {A B : PLLFormula}
    (d : G4s (insert A Γ) B) : G4s Γ (A.ifThen B) := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impR d⟩

theorem laxR {Γ : Finset PLLFormula} {A : PLLFormula}
    (d : G4s Γ A) : G4s Γ A.somehow := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .laxR d⟩

theorem laxL {Γ : Finset PLLFormula} {A B : PLLFormula}
    (h : A.somehow ∈ Γ) (d : G4s (insert A Γ) B.somehow) :
    G4s Γ B.somehow := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .laxL h d⟩

theorem andL {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.and B ∈ Γ) (d : G4s (insert A (insert B Γ)) C) :
    G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .andL h d⟩

theorem orL {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.or B ∈ Γ) (d₁ : G4s (insert A Γ) C)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .orL h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLProp {Γ : Finset PLLFormula} {a : String} {B C : PLLFormula}
    (h : (prop a).ifThen B ∈ Γ) (ha : prop a ∈ Γ)
    (d : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLProp h ha d⟩

theorem impLAnd {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.and B).ifThen D ∈ Γ)
    (d : G4s (insert (A.ifThen (B.ifThen D)) Γ) C) : G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLAnd h d⟩

theorem impLOr {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.or B).ifThen D ∈ Γ)
    (d : G4s (insert (A.ifThen D) (insert (B.ifThen D) Γ)) C) :
    G4s Γ C := by
  obtain ⟨n, d⟩ := d
  exact ⟨n + 1, .impLOr h d⟩

theorem impLImp {Γ : Finset PLLFormula} {A B D C : PLLFormula}
    (h : (A.ifThen B).ifThen D ∈ Γ)
    (d₁ : G4s (insert (B.ifThen D) Γ) (A.ifThen B))
    (d₂ : G4s (insert D Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLImp h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLLax {Γ : Finset PLLFormula} {A B C : PLLFormula}
    (h : A.somehow.ifThen B ∈ Γ) (d₁ : G4s Γ A)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLLax h (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem impLLaxLax {Γ : Finset PLLFormula} {A B X C : PLLFormula}
    (h : A.somehow.ifThen B ∈ Γ) (hX : X.somehow ∈ Γ)
    (d₁ : G4s (insert X Γ) A.somehow)
    (d₂ : G4s (insert B Γ) C) : G4s Γ C := by
  obtain ⟨n, d₁⟩ := d₁
  obtain ⟨m, d₂⟩ := d₂
  exact ⟨max n m + 1, .impLLaxLax h hX (d₁.mono (Nat.le_max_left n m))
    (d₂.mono (Nat.le_max_right n m))⟩

theorem truePLL_intro (Γ : Finset PLLFormula) : G4s Γ truePLL :=
  impR (botL (Finset.mem_insert_self _ _))

theorem andAll_intro : ∀ {l : List PLLFormula} {Γ : Finset PLLFormula},
    (∀ φ ∈ l, G4s Γ φ) → G4s Γ (andAll l) := by
  intro l
  induction l with
  | nil => intro Γ _; exact truePLL_intro Γ
  | cons φ l ih =>
      intro Γ h
      exact andR (h φ (.head _)) (ih fun ψ hψ => h ψ (.tail _ hψ))

theorem orAll_intro : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Γ : Finset PLLFormula}, G4s Γ φ → G4s Γ (orAll l) := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Γ h
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact orR1 h
      · exact orR2 (ih hmem' h)

/-- Split a conjunction at the head of the context (cumulatively). -/
theorem andL_ins {X₁ X₂ : PLLFormula} {Δ : Finset PLLFormula}
    {C : PLLFormula} (d : G4s (insert X₁ (insert X₂ Δ)) C) :
    G4s (insert (X₁.and X₂) Δ) C :=
  andL (Finset.mem_insert_self _ _)
    (d.weaken_subset (Finset.insert_subset_insert _
      (Finset.insert_subset_insert _ (Finset.subset_insert _ _))))

theorem andAll_elim : ∀ {l : List PLLFormula} {φ : PLLFormula}, φ ∈ l →
    ∀ {Δ : Finset PLLFormula} {D : PLLFormula},
    G4s (insert φ Δ) D → G4s (insert (andAll l) Δ) D := by
  intro l
  induction l with
  | nil => intro φ h; cases h
  | cons x l ih =>
      intro φ hmem Δ D h
      simp only [andAll]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact andL_ins (h.weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
      · refine andL_ins ?_
        have h' : G4s (insert φ (insert x Δ)) D :=
          h.weaken_subset (by
            intro y hy
            simp only [Finset.mem_insert] at hy ⊢
            tauto)
        exact (ih hmem' h').weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)

theorem orAll_elim : ∀ {l : List PLLFormula} {Δ : Finset PLLFormula}
    {C : PLLFormula}, (∀ φ ∈ l, G4s (insert φ Δ) C) →
    G4s (insert (orAll l) Δ) C := by
  intro l
  induction l with
  | nil => intro Δ C _; exact botL (Finset.mem_insert_self _ _)
  | cons x l ih =>
      intro Δ C h
      simp only [orAll]
      refine orL (Finset.mem_insert_self _ _) ?_ ?_
      · exact (h x (.head _)).weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))
      · exact (ih fun ψ hψ => h ψ (.tail _ hψ)).weaken_subset
          (Finset.insert_subset_insert _ (Finset.subset_insert _ _))

/-- `andAll_elim`, keeping the bundle in context (retention pays:
`insert_idem` merges the duplicate). -/
theorem andAll_elim_keep {l : List PLLFormula} {φ : PLLFormula}
    (hmem : φ ∈ l) {Δ : Finset PLLFormula} {D : PLLFormula}
    (d : G4s (insert φ (insert (andAll l) Δ)) D) :
    G4s (insert (andAll l) Δ) D := by
  have h := andAll_elim hmem (Δ := insert (andAll l) Δ) d
  rwa [Finset.insert_idem] at h

/-- **Cut, transported to the set calculus** through `G4c.iff_set`. -/
theorem cut_adm {Δ : Finset PLLFormula} {A E : PLLFormula}
    (d₁ : G4s Δ A) (d₂ : G4s (insert A Δ) E) : G4s Δ E := by
  have e₁ : Δ.toList.toFinset = Δ := Finset.toList_toFinset _
  have d₁' : G4c Δ.toList A := G4c.iff_set.mpr (by rwa [e₁])
  have d₂' : G4c (A :: Δ.toList) E := G4c.iff_set.mpr (by
    rw [List.toFinset_cons, e₁]
    exact d₂)
  have d₃ := G4c.iff_set.mp (G4c.cut d₁' d₂')
  rwa [e₁] at d₃

/-- **Modus ponens against a context implication** (set level): the
consumer of the `(E ⇢ A)`-guarded clauses. -/
theorem mp_adm {Δ : Finset PLLFormula} {X Y E : PLLFormula}
    (hK : X.ifThen Y ∈ Δ) (hX : G4s Δ X)
    (hY : G4s (insert Y Δ) E) : G4s Δ E := by
  refine cut_adm ?_ hY
  have e₁ : Δ.toList.toFinset = Δ := Finset.toList_toFinset _
  have hX' : G4c Δ.toList X := G4c.iff_set.mpr (by rwa [e₁])
  have hKl : X.ifThen Y ∈ Δ.toList := Finset.mem_toList.mpr hK
  have hq := List.perm_cons_erase hKl
  have hmp : G4c (X :: Δ.toList) Y :=
    (G4c.mp X Y (Δ.toList.erase (X.ifThen Y))).perm (hq.symm.cons X)
  have hYc := G4c.iff_set.mp (G4c.cut hX' hmp)
  rwa [e₁] at hYc

end G4s

namespace G4sh

/-- **Height-preserving `impR`-inversion** for the cumulative calculus:
an implication goal can always be unfolded first.  (The other right
rules are not invertible: `◯A` via `laxR` does not imply `A`, and a
disjunction goal proved by `orL` splits.) -/
theorem impR_inv : ∀ {n : Nat} {Γ : Finset PLLFormula} {C : PLLFormula},
    G4sh n Γ C → ∀ {A B : PLLFormula}, C = A.ifThen B →
    G4sh n (insert A Γ) B := by
  intro n Γ C d
  induction d with
  | init h => intro A B hC; cases hC
  | botL h => intro A B hC; exact .botL (Finset.mem_insert_of_mem h)
  | andR _ _ _ _ => intro A B hC; cases hC
  | orR1 _ _ => intro A B hC; cases hC
  | orR2 _ _ => intro A B hC; cases hC
  | laxR _ _ => intro A B hC; cases hC
  | laxL _ _ _ => intro A B hC; cases hC
  | @impR _ _ A₀ B₀ d _ =>
      intro A B hC
      injection hC with h₁ h₂
      subst h₁; subst h₂
      exact d.succ_mono
  | @andL _ Γ₀ A₀ B₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .andL (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @orL _ Γ₀ A₀ B₀ C₀ h _ _ ih₁ ih₂ =>
      intro A B hC
      subst hC
      refine .orL (Finset.mem_insert_of_mem h) ?_ ?_
      · exact (ih₁ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
  | @impLProp _ Γ₀ a B₀ C₀ h ha _ ih =>
      intro A B hC
      subst hC
      refine .impLProp (Finset.mem_insert_of_mem h)
        (Finset.mem_insert_of_mem ha) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLAnd _ Γ₀ A₀ B₀ D₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .impLAnd (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLOr _ Γ₀ A₀ B₀ D₀ C₀ h _ ih =>
      intro A B hC
      subst hC
      refine .impLOr (Finset.mem_insert_of_mem h) ?_
      exact (ih rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLImp _ Γ₀ A₀ B₀ D₀ C₀ h d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLImp (Finset.mem_insert_of_mem h) ?_ ?_
      · exact d₁.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
  | @impLLax _ Γ₀ A₀ B₀ C₀ h d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLLax (Finset.mem_insert_of_mem h)
        (d₁.weaken_subset (Finset.subset_insert _ _)) ?_
      exact (ih₂ rfl).weaken_subset (by
        intro y hy
        simp only [Finset.mem_insert] at hy ⊢
        tauto)
  | @impLLaxLax _ Γ₀ A₀ B₀ X₀ C₀ h hX d₁ _ _ ih₂ =>
      intro A B hC
      subst hC
      refine .impLLaxLax (Finset.mem_insert_of_mem h)
        (Finset.mem_insert_of_mem hX) ?_ ?_
      · exact d₁.weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)
      · exact (ih₂ rfl).weaken_subset (by
          intro y hy
          simp only [Finset.mem_insert] at hy ⊢
          tauto)

end G4sh

/-! ### The Pitts quantifiers -/

mutual

/-- ∃-quantifier for contexts: strongest p-free consequence, to fuel
depth.  Clause table v2, following Pitts 1992 (E0–E8), the UIML Coq
artifact (IJCAR 2024) and Iemhoff's §8.6.6 lax assignment, adapted to
the retention calculus: recursive `interA`-occurrences at a *grown*
context are relativised by an `interE`-guard, and the lax witness
clauses take the ◯(E ⇢ A)-form — the guard formula is designed to be
its own `L◯→″`-witness. -/
def interE (p : String) : Nat → List PLLFormula → PLLFormula
  | 0, _ => truePLL
  | fuel + 1, Γ =>
      andAll (
        -- E0: ⊥ in the context
        (if falsePLL ∈ Γ then [falsePLL] else [])
        -- E1: atoms other than p
        ++ Γ.filterMap (fun F => match F with
            | .prop q => if q = p then none else some (prop q)
            | _ => none)
        ++ Γ.flatMap (fun F => match F with
            -- E2 (andL)
            | .and A B => [interE p fuel (A :: B :: Γ)]
            -- E3 (orL)
            | .or A B =>
                [(interE p fuel (A :: Γ)).or (interE p fuel (B :: Γ))]
            -- E4/E5 (impLProp, Coq-merged form)
            | .ifThen (.prop q) B =>
                if PLLFormula.prop q ∈ Γ then [interE p fuel (B :: Γ)]
                else if q = p then []
                else [(prop q).ifThen (interE p fuel (B :: Γ))]
            -- E6 (impLAnd)
            | .ifThen (.and A B) D =>
                [interE p fuel (A.ifThen (B.ifThen D) :: Γ)]
            -- E7 (impLOr)
            | .ifThen (.or A B) D =>
                [interE p fuel (A.ifThen D :: B.ifThen D :: Γ)]
            -- E8 (impLImp): (E ⇢ A)-guarded side premise
            | .ifThen (.ifThen A B) D =>
                [((interE p fuel (B.ifThen D :: Γ)).ifThen
                    (interA p fuel (B.ifThen D :: Γ) (A.ifThen B))).ifThen
                  (interE p fuel (D :: Γ))]
            -- impLLax (R◯→″): head clause (context unchanged, bare A),
            -- then the γ-form (witness expected on the p-free side),
            -- then one witness clause per Γ-side box (L◯→″)
            | .ifThen (.somehow A) B =>
                ((interA p fuel Γ A).ifThen (interE p fuel (B :: Γ)))
                :: (((interE p fuel Γ).ifThen
                      (interA p fuel Γ A.somehow)).somehow.ifThen
                    (interE p fuel (B :: Γ)))
                :: Γ.filterMap (fun X => match X with
                    | .somehow x =>
                        some ((((interE p fuel (x :: Γ)).ifThen
                            (interA p fuel (x :: Γ) A.somehow)).somehow).ifThen
                          (interE p fuel (B :: Γ)))
                    | _ => none)
            -- laxL (opening): doubles as Iemhoff's witness-anticipation
            | .somehow χ => [(interE p fuel (χ :: Γ)).somehow]
            | _ => []))

/-- ∀-quantifier for sequents, to fuel depth.  NOTE (Pitts Remark 5 /
IJCAR Remark 3): `interA` is *not* itself the weakest p-free
antecedent — that is `interE Γ → interA (Γ⇒C)`; adequacy carries the
`interE`-hypothesis on the consumer side.  Clause table v2: goal- and
context-atom reflection (A9/A4/A10), E-guards on grown-context
recursions (A3/A8/A13), and the ◯(E ⇢ A)-shaped disjuncts for ◯-goals
and the lax rules (basic + self-referential + per-witness forms). -/
def interA (p : String) : Nat → List PLLFormula → PLLFormula → PLLFormula
  | 0, _, _ => falsePLL
  | fuel + 1, Γ, C =>
      orAll (
        -- a_form: goal-directed disjuncts
        (match C with
            -- A9: goal-atom reflection
            | .prop q => if q = p then [] else [prop q]
            | .falsePLL => []
            -- A11
            | .and C₁ C₂ =>
                [(interA p fuel Γ C₁).and (interA p fuel Γ C₂)]
            -- A12 (as two disjuncts)
            | .or C₁ C₂ => [interA p fuel Γ C₁, interA p fuel Γ C₂]
            -- A13: E-guarded implication reflection
            | .ifThen C₁ C₂ =>
                [(interE p fuel (C₁ :: Γ)).ifThen
                  (interA p fuel (C₁ :: Γ) C₂)]
            -- ◯-goal: basic ◯(E ⇢ A)-disjunct (laxR) and the
            -- self-referential variant (Δ-side laxL commute)
            | .somehow D =>
                [((interE p fuel Γ).ifThen (interA p fuel Γ D)).somehow,
                 ((interE p fuel Γ).ifThen
                   (interA p fuel Γ D.somehow)).somehow])
        -- a_env: context-directed disjuncts
        ++ Γ.flatMap (fun F => match F with
            -- A10: only the quantified atom reflects as ⊤ (a p-free
            -- context atom is carried by the E-side)
            | .prop q =>
                if q = p ∧ C = PLLFormula.prop p then [truePLL] else []
            -- A2
            | .and A B => [interA p fuel (A :: B :: Γ) C]
            -- A3: both branches E-guarded (context grew)
            | .or A B =>
                [((interE p fuel (A :: Γ)).ifThen
                    (interA p fuel (A :: Γ) C)).and
                 ((interE p fuel (B :: Γ)).ifThen
                    (interA p fuel (B :: Γ) C))]
            -- A4/A5: context-atom reflection
            | .ifThen (.prop q) B =>
                if PLLFormula.prop q ∈ Γ then [interA p fuel (B :: Γ) C]
                else if q = p then []
                else [(prop q).and (interA p fuel (B :: Γ) C)]
            -- A6
            | .ifThen (.and A B) D =>
                [interA p fuel (A.ifThen (B.ifThen D) :: Γ) C]
            -- A7
            | .ifThen (.or A B) D =>
                [interA p fuel (A.ifThen D :: B.ifThen D :: Γ) C]
            -- A8: E-guarded side premise, bare second component
            | .ifThen (.ifThen A B) D =>
                [(((interE p fuel (B.ifThen D :: Γ)).ifThen
                    (interA p fuel (B.ifThen D :: Γ) (A.ifThen B)))).and
                  (interA p fuel (D :: Γ) C)]
            -- impLLax (∀-side): head, γ-form, and per-witness clauses
            | .ifThen (.somehow A) B =>
                ((interA p fuel Γ A).and (interA p fuel (B :: Γ) C))
                :: ((((interE p fuel Γ).ifThen
                      (interA p fuel Γ A.somehow)).somehow).and
                    (interA p fuel (B :: Γ) C))
                :: Γ.filterMap (fun X => match X with
                    | .somehow x =>
                        some (((((interE p fuel (x :: Γ)).ifThen
                            (interA p fuel (x :: Γ) A.somehow)).somehow)).and
                          (interA p fuel (B :: Γ) C))
                    | _ => none)
            -- ∀^{L◯}: only for a ◯-shaped goal (laxL needs it)
            | .somehow χ =>
                (match C with
                  | .somehow _ =>
                      [((interE p fuel (χ :: Γ)).ifThen
                          (interA p fuel (χ :: Γ) C)).somehow]
                  | _ => [])
            | _ => []))

end

/-! ### p-freeness -/

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

/-- **The quantifiers are p-free.** -/
theorem inter_pfree (p : String) : ∀ (fuel : Nat),
    (∀ Γ, p ∉ (interE p fuel Γ).atoms) ∧
    (∀ Γ C, p ∉ (interA p fuel Γ C).atoms) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ h; simp [interE, truePLL] at h
      · intro Γ C h; simp [interA] at h
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · intro Γ hmem
        simp only [interE] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_andAll hmem
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
              rcases List.mem_singleton.mp hin with rfl
              exact ihE _ hx
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_or, Finset.mem_union] at hx
              rcases hx with hx | hx
              · exact ihE _ hx
              · exact ihE _ hx
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_somehow] at hx
              exact ihE _ hx
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  · rcases List.mem_singleton.mp hin with rfl
                    exact ihE _ hx
                  · split at hin
                    · cases hin
                    · rcases List.mem_singleton.mp hin with rfl
                      rw [atoms_ifThen, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · rw [atoms_prop, Finset.mem_singleton] at hx
                        subst hx
                        simp_all
                      · exact ihE _ hx
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihE _ hx
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihE _ hx
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  rw [atoms_ifThen, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · rw [atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihE _ hx
                    · exact ihA _ _ hx
                  · exact ihE _ hx
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · rw [atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihA _ _ hx
                    · exact ihE _ hx
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · rw [atoms_ifThen, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · rw [atoms_somehow, atoms_ifThen,
                          Finset.mem_union] at hx
                        rcases hx with hx | hx
                        · exact ihE _ hx
                        · exact ihA _ _ hx
                      · exact ihE _ hx
                    · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          rw [atoms_ifThen, Finset.mem_union] at hx
                          rcases hx with hx | hx
                          · rw [atoms_somehow, atoms_ifThen,
                              Finset.mem_union] at hx
                            rcases hx with hx | hx
                            · exact ihE _ hx
                            · exact ihA _ _ hx
                          · exact ihE _ hx
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
      · intro Γ C hmem
        simp only [interA] at hmem
        obtain ⟨φ, hφ, hx⟩ := mem_atoms_orAll hmem
        rcases List.mem_append.mp hφ with hφ | hφ
        · -- the goal clauses
          cases C with
          | prop q =>
              simp only at hφ
              split at hφ
              · cases hφ
              · rcases List.mem_singleton.mp hφ with rfl
                rw [atoms_prop, Finset.mem_singleton] at hx
                subst hx
                simp_all
          | falsePLL => cases hφ
          | and C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              rw [atoms_and, Finset.mem_union] at hx
              rcases hx with hx | hx
              · exact ihA _ _ hx
              · exact ihA _ _ hx
          | or C₁ C₂ =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact ihA _ _ hx
              · rcases List.mem_singleton.mp hφ' with rfl
                exact ihA _ _ hx
          | ifThen C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              rw [atoms_ifThen, Finset.mem_union] at hx
              rcases hx with hx | hx
              · exact ihE _ hx
              · exact ihA _ _ hx
          | somehow D =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihE _ hx
                · exact ihA _ _ hx
              · rcases List.mem_singleton.mp hφ' with rfl
                rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihE _ hx
                · exact ihA _ _ hx
        · -- the context clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              · rcases List.mem_singleton.mp hin with rfl
                simp [truePLL] at hx
              · cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              exact ihA _ _ hx
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              rw [atoms_and, Finset.mem_union] at hx
              rcases hx with hx | hx
              · rw [atoms_ifThen, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihE _ hx
                · exact ihA _ _ hx
              · rw [atoms_ifThen, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihE _ hx
                · exact ihA _ _ hx
          | somehow χ =>
              simp only at hin
              split at hin
              · rcases List.mem_singleton.mp hin with rfl
                rw [atoms_somehow, atoms_ifThen, Finset.mem_union] at hx
                rcases hx with hx | hx
                · exact ihE _ hx
                · exact ihA _ _ hx
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  · rcases List.mem_singleton.mp hin with rfl
                    exact ihA _ _ hx
                  · split at hin
                    · cases hin
                    · rcases List.mem_singleton.mp hin with rfl
                      rw [atoms_and, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · rw [atoms_prop, Finset.mem_singleton] at hx
                        subst hx
                        simp_all
                      · exact ihA _ _ hx
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihA _ _ hx
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  exact ihA _ _ hx
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  rw [atoms_and, Finset.mem_union] at hx
                  rcases hx with hx | hx
                  · rw [atoms_ifThen, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihE _ hx
                    · exact ihA _ _ hx
                  · exact ihA _ _ hx
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · rw [atoms_and, Finset.mem_union] at hx
                    rcases hx with hx | hx
                    · exact ihA _ _ hx
                    · exact ihA _ _ hx
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · rw [atoms_and, Finset.mem_union] at hx
                      rcases hx with hx | hx
                      · rw [atoms_somehow, atoms_ifThen,
                          Finset.mem_union] at hx
                        rcases hx with hx | hx
                        · exact ihE _ hx
                        · exact ihA _ _ hx
                      · exact ihA _ _ hx
                    · obtain ⟨X, _, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          rw [atoms_and, Finset.mem_union] at hx
                          rcases hx with hx | hx
                          · rw [atoms_somehow, atoms_ifThen,
                              Finset.mem_union] at hx
                            rcases hx with hx | hx
                            · exact ihE _ hx
                            · exact ihA _ _ hx
                          · exact ihA _ _ hx
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq

theorem interE_pfree (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    p ∉ (interE p fuel Γ).atoms := (inter_pfree p fuel).1 Γ

theorem interA_pfree (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : p ∉ (interA p fuel Γ C).atoms :=
  (inter_pfree p fuel).2 Γ C

/-! ### Soundness of the quantifiers (Pitts E1/A1)

`interE p fuel Γ` is a consequence of `Γ`, and `interA p fuel Γ C`
suffices for `C` alongside `Γ` — at every fuel.  Both by one mutual
fuel induction at the `G4s` level, where each clause is discharged by
firing the cumulative rule it mirrors; the `impLImp` / `impLLax` /
`impLLaxLax` clauses consume the `interA` induction hypothesis as
their side premise (the sequent-shaped ingredient of the recursion).
-/

private theorem memF {F : PLLFormula} {Γ : List PLLFormula} (h : F ∈ Γ) :
    F ∈ Γ.toFinset := List.mem_toFinset.mpr h

theorem inter_sound (p : String) : ∀ (fuel : Nat),
    (∀ Γ, G4s Γ.toFinset (interE p fuel Γ)) ∧
    (∀ Γ C, G4s (insert (interA p fuel Γ C) Γ.toFinset) C) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ
        simp only [interE]
        exact G4s.truePLL_intro _
      · intro Γ C
        simp only [interA]
        exact G4s.botL (Finset.mem_insert_self _ _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- E1: Γ ⊢ interE p (fuel+1) Γ
        intro Γ
        simp only [interE]
        refine G4s.andAll_intro ?_
        intro φ hφ
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
              rcases List.mem_singleton.mp hin with rfl
              have ih' := ihE (A :: B :: Γ)
              rw [List.toFinset_cons, List.toFinset_cons] at ih'
              exact G4s.andL (memF hFΓ) ih'
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              have ih₁ := ihE (A :: Γ)
              rw [List.toFinset_cons] at ih₁
              have ih₂ := ihE (B :: Γ)
              rw [List.toFinset_cons] at ih₂
              exact G4s.orL (memF hFΓ) (G4s.orR1 ih₁) (G4s.orR2 ih₂)
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              have ih' := ihE (χ :: Γ)
              rw [List.toFinset_cons] at ih'
              exact G4s.laxL (memF hFΓ) (G4s.laxR ih')
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hq =>
                    rcases List.mem_singleton.mp hin with rfl
                    have ih' := ihE (B :: Γ)
                    rw [List.toFinset_cons] at ih'
                    exact G4s.impLProp (memF hFΓ) (memF hq) ih'
                  next =>
                    split at hin
                    next => cases hin
                    next =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4s.impR ?_
                      have ih' := ihE (B :: Γ)
                      rw [List.toFinset_cons] at ih'
                      refine G4s.impLProp
                        (Finset.mem_insert_of_mem (memF hFΓ))
                        (Finset.mem_insert_self _ _) ?_
                      exact ih'.weaken_subset
                        (Finset.insert_subset_insert _
                          (Finset.subset_insert _ _))
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih' := ihE (A₁.ifThen (B₁.ifThen B) :: Γ)
                  rw [List.toFinset_cons] at ih'
                  exact G4s.impLAnd (memF hFΓ) ih'
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have ih' := ihE (A₁.ifThen B :: B₁.ifThen B :: Γ)
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact G4s.impLOr (memF hFΓ) ih'
              | ifThen A₁ B₁ =>
                  -- E8: ((E' ⇢ A') ⇢ E'')
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impR ?_
                  have ihe' := ihE (B₁.ifThen B :: Γ)
                  rw [List.toFinset_cons] at ihe'
                  have iha' := ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)
                  rw [List.toFinset_cons] at iha'
                  have ihd := ihE (B :: Γ)
                  rw [List.toFinset_cons] at ihd
                  refine G4s.impLImp
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_ ?_
                  · refine G4s.mp_adm
                      (X := interE p fuel (B₁.ifThen B :: Γ))
                      (Y := interA p fuel (B₁.ifThen B :: Γ) (A₁.ifThen B₁))
                      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                      ?_ ?_
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
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · -- head clause: bare A(Γ ⇒ A₁) antecedent
                    refine G4s.impR ?_
                    have ihe := ihE (B :: Γ)
                    rw [List.toFinset_cons] at ihe
                    refine G4s.impLLax
                      (Finset.mem_insert_of_mem (memF hFΓ)) (ihA Γ A₁) ?_
                    exact ihe.weaken_subset
                      (Finset.insert_subset_insert _
                        (Finset.subset_insert _ _))
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · -- γ-clause: the guard is its own witness
                      refine G4s.impR ?_
                      have ihe := ihE (B :: Γ)
                      rw [List.toFinset_cons] at ihe
                      refine G4s.impLLaxLax
                        (Finset.mem_insert_of_mem (memF hFΓ))
                        (Finset.mem_insert_self _ _) ?_ ?_
                      · refine G4s.mp_adm (X := interE p fuel Γ)
                          (Y := interA p fuel Γ A₁.somehow)
                          (Finset.mem_insert_self _ _) ?_ ?_
                        · exact (ihE Γ).weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                        · exact (ihA Γ A₁.somehow).weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                      · exact ihe.weaken_subset
                          (Finset.insert_subset_insert _
                            (Finset.subset_insert _ _))
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          refine G4s.impR ?_
                          have ihe := ihE (B :: Γ)
                          rw [List.toFinset_cons] at ihe
                          refine G4s.impLLaxLax
                            (Finset.mem_insert_of_mem (memF hFΓ))
                            (Finset.mem_insert_self _ _) ?_ ?_
                          · -- open the Γ-side witness box, then MP
                            refine G4s.laxL
                              (Finset.mem_insert_of_mem
                                (Finset.mem_insert_of_mem (memF hXΓ))) ?_
                            have ihe' := ihE (x :: Γ)
                            rw [List.toFinset_cons] at ihe'
                            have iha' := ihA (x :: Γ) A₁.somehow
                            rw [List.toFinset_cons] at iha'
                            refine G4s.mp_adm
                              (X := interE p fuel (x :: Γ))
                              (Y := interA p fuel (x :: Γ) A₁.somehow)
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
      · -- A1: interA p (fuel+1) Γ C, Γ ⊢ C
        intro Γ C
        simp only [interA]
        refine G4s.orAll_elim ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · -- the goal clauses
          cases C with
          | prop q =>
              simp only at hφ
              split at hφ
              · cases hφ
              · rcases List.mem_singleton.mp hφ with rfl
                exact G4s.init (Finset.mem_insert_self _ _)
          | falsePLL => cases hφ
          | and C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4s.andL_ins ?_
              refine G4s.andR ?_ ?_
              · exact (ihA Γ C₁).weaken_subset
                  (Finset.insert_subset_insert _
                    (Finset.subset_insert _ _))
              · exact (ihA Γ C₂).weaken_subset (Finset.subset_insert _ _)
          | or C₁ C₂ =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · exact G4s.orR1 (ihA Γ C₁)
              · rcases List.mem_singleton.mp hφ' with rfl
                exact G4s.orR2 (ihA Γ C₂)
          | ifThen C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4s.impR ?_
              have ihe := ihE (C₁ :: Γ)
              rw [List.toFinset_cons] at ihe
              have iha := ihA (C₁ :: Γ) C₂
              rw [List.toFinset_cons] at iha
              refine G4s.mp_adm (X := interE p fuel (C₁ :: Γ))
                (Y := interA p fuel (C₁ :: Γ) C₂)
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
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · -- basic ◯(E ⇢ A(Γ⇒D))
                refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                refine G4s.mp_adm (X := interE p fuel Γ)
                  (Y := interA p fuel Γ D)
                  (Finset.mem_insert_self _ _) ?_ ?_
                · exact (ihE Γ).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (G4s.laxR (ihA Γ D)).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              · rcases List.mem_singleton.mp hφ' with rfl
                -- self-referential ◯(E ⇢ A(Γ⇒◯D))
                refine G4s.laxL (Finset.mem_insert_self _ _) ?_
                refine G4s.mp_adm (X := interE p fuel Γ)
                  (Y := interA p fuel Γ D.somehow)
                  (Finset.mem_insert_self _ _) ?_ ?_
                · exact (ihE Γ).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
                · exact (ihA Γ D.somehow).weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
        · -- the context clauses
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
              rcases List.mem_singleton.mp hin with rfl
              refine G4s.andL (Finset.mem_insert_of_mem (memF hFΓ)) ?_
              have ih' := ihA (A :: B :: Γ) C
              rw [List.toFinset_cons, List.toFinset_cons] at ih'
              exact ih'.weaken_subset (by
                intro y hy
                simp only [Finset.mem_insert] at hy ⊢
                tauto)
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4s.andL_ins ?_
              refine G4s.orL (Finset.mem_insert_of_mem
                (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
              · have ihe := ihE (A :: Γ)
                rw [List.toFinset_cons] at ihe
                have iha := ihA (A :: Γ) C
                rw [List.toFinset_cons] at iha
                refine G4s.mp_adm (X := interE p fuel (A :: Γ))
                  (Y := interA p fuel (A :: Γ) C)
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
              · have ihe := ihE (B :: Γ)
                rw [List.toFinset_cons] at ihe
                have iha := ihA (B :: Γ) C
                rw [List.toFinset_cons] at iha
                refine G4s.mp_adm (X := interE p fuel (B :: Γ))
                  (Y := interA p fuel (B :: Γ) C)
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
          | somehow χ =>
              simp only at hin
              split at hin
              · rcases List.mem_singleton.mp hin with rfl
                -- ∀^{L◯}: goal is ◯-shaped; open ◯χ, then the guard box
                refine G4s.laxL
                  (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                refine G4s.laxL
                  (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) ?_
                have ihe := ihE (χ :: Γ)
                rw [List.toFinset_cons] at ihe
                exact G4s.mp_adm (Finset.mem_insert_self _ _)
                  (ihe.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto))
                  ((ihA (χ :: Γ) _).weaken_subset (by
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
                  next hg =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4s.impLProp
                      (Finset.mem_insert_of_mem (memF hFΓ))
                      (Finset.mem_insert_of_mem (memF hg)) ?_
                    have ih' := ihA (B :: Γ) C
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
                      have ih' := ihA (B :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impLAnd
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  have ih' := ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C
                  rw [List.toFinset_cons] at ih'
                  exact ih'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.impLOr
                    (Finset.mem_insert_of_mem (memF hFΓ)) ?_
                  have ih' := ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C
                  rw [List.toFinset_cons, List.toFinset_cons] at ih'
                  exact ih'.weaken_subset (by
                    intro y hy
                    simp only [Finset.mem_insert] at hy ⊢
                    tauto)
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4s.andL_ins ?_
                  refine G4s.impLImp
                    (Finset.mem_insert_of_mem
                      (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                  · have ihe := ihE (B₁.ifThen B :: Γ)
                    rw [List.toFinset_cons] at ihe
                    have iha := ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)
                    rw [List.toFinset_cons] at iha
                    refine G4s.mp_adm
                      (X := interE p fuel (B₁.ifThen B :: Γ))
                      (Y := interA p fuel (B₁.ifThen B :: Γ) (A₁.ifThen B₁))
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
                  · have ih' := ihA (B :: Γ) C
                    rw [List.toFinset_cons] at ih'
                    exact ih'.weaken_subset (by
                      intro y hy
                      simp only [Finset.mem_insert] at hy ⊢
                      tauto)
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · -- head: A(Γ⇒A₁) ∧ A(B::Γ⇒C)
                    refine G4s.andL_ins ?_
                    refine G4s.impLLax
                      (Finset.mem_insert_of_mem
                        (Finset.mem_insert_of_mem (memF hFΓ))) ?_ ?_
                    · exact (ihA Γ A₁).weaken_subset
                        (Finset.insert_subset_insert _
                          (Finset.subset_insert _ _))
                    · have ih' := ihA (B :: Γ) C
                      rw [List.toFinset_cons] at ih'
                      exact ih'.weaken_subset (by
                        intro y hy
                        simp only [Finset.mem_insert] at hy ⊢
                        tauto)
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · -- γ-form: the ◯-guard is its own witness
                      refine G4s.andL_ins ?_
                      refine G4s.impLLaxLax
                        (Finset.mem_insert_of_mem
                          (Finset.mem_insert_of_mem (memF hFΓ)))
                        (Finset.mem_insert_self _ _) ?_ ?_
                      · refine G4s.mp_adm (X := interE p fuel Γ)
                          (Y := interA p fuel Γ A₁.somehow)
                          (Finset.mem_insert_self _ _) ?_ ?_
                        · exact (ihE Γ).weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                        · exact (ihA Γ A₁.somehow).weaken_subset (by
                            intro y hy
                            simp only [Finset.mem_insert] at hy ⊢
                            tauto)
                      · have ih' := ihA (B :: Γ) C
                        rw [List.toFinset_cons] at ih'
                        exact ih'.weaken_subset (by
                          intro y hy
                          simp only [Finset.mem_insert] at hy ⊢
                          tauto)
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
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
                                  (Finset.mem_insert_of_mem (memF hXΓ)))) ?_
                            have ihe := ihE (x :: Γ)
                            rw [List.toFinset_cons] at ihe
                            have iha := ihA (x :: Γ) A₁.somehow
                            rw [List.toFinset_cons] at iha
                            refine G4s.mp_adm
                              (X := interE p fuel (x :: Γ))
                              (Y := interA p fuel (x :: Γ) A₁.somehow)
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
                          · have ih' := ihA (B :: Γ) C
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

/-- **E1** (set level): the ∃-quantifier is a consequence of `Γ`. -/
theorem interE_sound (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    G4s Γ.toFinset (interE p fuel Γ) := (inter_sound p fuel).1 Γ

/-- **A1** (set level): the ∀-quantifier suffices for `C` alongside
`Γ`. -/
theorem interA_sound (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : G4s (insert (interA p fuel Γ C) Γ.toFinset) C :=
  (inter_sound p fuel).2 Γ C

/-- E1 at the list calculus. -/
theorem interE_sound_g4c (p : String) (fuel : Nat) (Γ : List PLLFormula) :
    G4c Γ (interE p fuel Γ) :=
  G4c.iff_set.mpr (interE_sound p fuel Γ)

/-- A1 at the list calculus. -/
theorem interA_sound_g4c (p : String) (fuel : Nat) (Γ : List PLLFormula)
    (C : PLLFormula) : G4c (interA p fuel Γ C :: Γ) C := by
  refine G4c.iff_set.mpr ?_
  rw [List.toFinset_cons]
  exact interA_sound p fuel Γ C

/-! ### Fuel monotonicity

More fuel means a *stronger* ∃-quantifier and a *weaker* ∀-quantifier:
`interE p 0 Γ = ⊤` is the weakest approximant and each unfolding
sharpens it; dually `interA p 0 Γ C = ⊥`.  The implication-shaped
clauses flip variance, which is exactly why the two directions are
proved together.  Everything at the list calculus, where `cut` and
`impL_adm` compose the per-clause implications.
-/

/-- Identity is admissible in `G4c` (via completeness from `SC`). -/
theorem G4c.iden {A : PLLFormula} {Γ : List PLLFormula} (h : A ∈ Γ) :
    G4c Γ A := G4c.completeness (SC.iden _ h)

theorem imp_mono {X X' Y Y' : PLLFormula}
    (hX : G4c [X] X') (hY : G4c [Y'] Y) :
    G4c [X'.ifThen Y'] (X.ifThen Y) := by
  refine G4c.impR ?_
  refine G4c.impL_adm (l₀ := [X]) (List.Perm.swap _ _ _) ?_ ?_
  · exact (hX.weaken (X'.ifThen Y')).perm (List.Perm.swap _ _ _)
  · exact (hY.weaken X).perm (List.Perm.swap _ _ _)

theorem box_mono {Y Y' : PLLFormula} (hY : G4c [Y'] Y) :
    G4c [Y'.somehow] Y.somehow :=
  G4c.laxL (.head _)
    ((hY.laxR.weaken Y'.somehow).perm (List.Perm.swap _ _ _))

theorem and_mono {X X' Y Y' : PLLFormula}
    (h₁ : G4c [X] X') (h₂ : G4c [Y] Y') :
    G4c [X.and Y] (X'.and Y') := by
  refine G4c.andL (List.Perm.refl _) ?_
  exact G4c.andR ((h₁.weaken Y).perm (List.Perm.swap _ _ _)) (h₂.weaken X)

theorem or_mono {X X' Y Y' : PLLFormula}
    (h₁ : G4c [X] X') (h₂ : G4c [Y] Y') :
    G4c [X.or Y] (X'.or Y') := by
  refine G4c.orL (List.Perm.refl _) ?_ ?_
  · exact G4c.orR1 h₁
  · exact G4c.orR2 h₂

/-- **Fuel monotonicity**: `interE` strengthens and `interA` weakens
as fuel grows, one level at a time.  Per-clause composition with
`imp_mono`/`box_mono`/`and_mono`/`or_mono`; the double-contravariance
of the `(E ⇢ A)`-guards makes both induction hypotheses flow in the
right directions. -/
theorem inter_fuel_mono (p : String) : ∀ (fuel : Nat),
    (∀ Γ, G4c [interE p (fuel + 1) Γ] (interE p fuel Γ)) ∧
    (∀ Γ C, G4c [interA p fuel Γ C] (interA p (fuel + 1) Γ C)) := by
  intro fuel
  induction fuel with
  | zero =>
      constructor
      · intro Γ
        simp only [interE]
        exact G4c.truePLL_intro _
      · intro Γ C
        simp only [interA]
        exact G4c.botL (.head _)
  | succ fuel ih =>
      obtain ⟨ihE, ihA⟩ := ih
      constructor
      · -- [interE p (fuel+2) Γ] ⊢ interE p (fuel+1) Γ
        intro Γ
        simp only [interE]
        refine G4c.andAll_intro ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · rcases List.mem_append.mp hφ with hφ | hφ
          · -- the ⊥ clause: identical at both fuels
            split at hφ
            next hbot =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.andAll_elim ?_ (G4c.botL (.head _))
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
                  refine G4c.andAll_elim ?_ (G4c.init (.head _))
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
              rcases List.mem_singleton.mp hin with rfl
              have hE := ihE (A :: B :: Γ)
              simp only [interE] at hE
              refine G4c.andAll_elim ?_ hE
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.and B, hFΓ, .head _⟩))
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              have h₁ := ihE (A :: Γ)
              simp only [interE] at h₁
              have h₂ := ihE (B :: Γ)
              simp only [interE] at h₂
              refine G4c.andAll_elim ?_ (or_mono h₁ h₂)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.or B, hFΓ, .head _⟩))
          | somehow χ =>
              rcases List.mem_singleton.mp hin with rfl
              have hE := ihE (χ :: Γ)
              simp only [interE] at hE
              refine G4c.andAll_elim ?_ (box_mono hE)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨χ.somehow, hFΓ, .head _⟩))
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hg =>
                    rcases List.mem_singleton.mp hin with rfl
                    have hE := ihE (B :: Γ)
                    simp only [interE] at hE
                    refine G4c.andAll_elim ?_ hE
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                    simp only
                    rw [if_pos hg]
                    exact .head _
                  next hg =>
                    split at hin
                    next => cases hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      have hE := ihE (B :: Γ)
                      simp only [interE] at hE
                      refine G4c.andAll_elim ?_
                        (imp_mono (G4c.init (.head _)) hE)
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg hg, if_neg hq]
                      exact .head _
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have hE := ihE (A₁.ifThen (B₁.ifThen B) :: Γ)
                  simp only [interE] at hE
                  refine G4c.andAll_elim ?_ hE
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.and B₁).ifThen B, hFΓ, .head _⟩))
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have hE := ihE (A₁.ifThen B :: B₁.ifThen B :: Γ)
                  simp only [interE] at hE
                  refine G4c.andAll_elim ?_ hE
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.or B₁).ifThen B, hFΓ, .head _⟩))
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have hE := ihE (B :: Γ)
                  simp only [interE] at hE
                  have hE' := ihE (B₁.ifThen B :: Γ)
                  simp only [interE] at hE'
                  refine G4c.andAll_elim ?_
                    (imp_mono
                      (imp_mono hE' (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                      hE)
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.ifThen B₁).ifThen B, hFΓ, .head _⟩))
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · have hE := ihE (B :: Γ)
                    simp only [interE] at hE
                    refine G4c.andAll_elim ?_ (imp_mono (ihA Γ A₁) hE)
                    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A₁.somehow.ifThen B, hFΓ, .head _⟩))
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · have hE := ihE (B :: Γ)
                      simp only [interE] at hE
                      have hEΓ := ihE Γ
                      simp only [interE] at hEΓ
                      refine G4c.andAll_elim ?_
                        (imp_mono
                          (box_mono (imp_mono hEΓ (ihA Γ A₁.somehow))) hE)
                      exact List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr
                          ⟨A₁.somehow.ifThen B, hFΓ,
                            List.mem_cons.mpr (Or.inr (.head _))⟩))
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          have hE := ihE (B :: Γ)
                          simp only [interE] at hE
                          have hEx := ihE (x :: Γ)
                          simp only [interE] at hEx
                          refine G4c.andAll_elim ?_
                            (imp_mono
                              (box_mono
                                (imp_mono hEx (ihA (x :: Γ) A₁.somehow)))
                              hE)
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inr
                              (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, rfl⟩))))
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq
      · -- [interA p (fuel+1) Γ C] ⊢ interA p (fuel+2) Γ C
        intro Γ C
        simp only [interA]
        refine G4c.orAll_elim ?_
        intro φ hφ
        rcases List.mem_append.mp hφ with hφ | hφ
        · -- the goal clauses
          cases C with
          | prop q =>
              simp only at hφ
              split at hφ
              next => cases hφ
              next hq =>
                rcases List.mem_singleton.mp hφ with rfl
                refine G4c.orAll_intro ?_ (G4c.init (.head _))
                refine List.mem_append.mpr (Or.inl ?_)
                simp only
                rw [if_neg hq]
                exact .head _
          | falsePLL => cases hφ
          | and C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              refine G4c.orAll_intro ?_
                (and_mono (ihA Γ C₁) (ihA Γ C₂))
              exact List.mem_append.mpr (Or.inl (.head _))
          | or C₁ C₂ =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · refine G4c.orAll_intro ?_ (ihA Γ C₁)
                exact List.mem_append.mpr (Or.inl (.head _))
              · rcases List.mem_singleton.mp hφ' with rfl
                refine G4c.orAll_intro ?_ (ihA Γ C₂)
                exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))
          | ifThen C₁ C₂ =>
              rcases List.mem_singleton.mp hφ with rfl
              have hE := ihE (C₁ :: Γ)
              simp only [interE] at hE
              refine G4c.orAll_intro ?_ (imp_mono hE (ihA (C₁ :: Γ) C₂))
              exact List.mem_append.mpr (Or.inl (.head _))
          | somehow D =>
              rcases List.mem_cons.mp hφ with rfl | hφ'
              · have hE := ihE Γ
                simp only [interE] at hE
                refine G4c.orAll_intro ?_
                  (box_mono (imp_mono hE (ihA Γ D)))
                exact List.mem_append.mpr (Or.inl (.head _))
              · rcases List.mem_singleton.mp hφ' with rfl
                have hE := ihE Γ
                simp only [interE] at hE
                refine G4c.orAll_intro ?_
                  (box_mono (imp_mono hE (ihA Γ D.somehow)))
                exact List.mem_append.mpr (Or.inl (.tail _ (.head _)))
        · -- the context clauses
          obtain ⟨F, hFΓ, hin⟩ := List.mem_flatMap.mp hφ
          cases F with
          | prop q =>
              simp only at hin
              split at hin
              next hg =>
                rcases List.mem_singleton.mp hin with rfl
                refine G4c.orAll_intro ?_ (G4c.truePLL_intro _)
                refine List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨prop q, hFΓ, ?_⟩))
                simp only
                rw [if_pos hg]
                exact .head _
              next => cases hin
          | falsePLL => cases hin
          | and A B =>
              rcases List.mem_singleton.mp hin with rfl
              refine G4c.orAll_intro ?_ (ihA (A :: B :: Γ) C)
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.and B, hFΓ, .head _⟩))
          | or A B =>
              rcases List.mem_singleton.mp hin with rfl
              have hEA := ihE (A :: Γ)
              simp only [interE] at hEA
              have hEB := ihE (B :: Γ)
              simp only [interE] at hEB
              refine G4c.orAll_intro ?_
                (and_mono (imp_mono hEA (ihA (A :: Γ) C))
                  (imp_mono hEB (ihA (B :: Γ) C)))
              exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                ⟨A.or B, hFΓ, .head _⟩))
          | somehow χ =>
              simp only at hin
              split at hin
              · rcases List.mem_singleton.mp hin with rfl
                have hE := ihE (χ :: Γ)
                simp only [interE] at hE
                refine G4c.orAll_intro ?_
                  (box_mono (imp_mono hE (ihA (χ :: Γ) _)))
                refine List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨χ.somehow, hFΓ, ?_⟩))
                simp only
                exact .head _
              all_goals cases hin
          | ifThen A' B =>
              cases A' with
              | prop q =>
                  simp only at hin
                  split at hin
                  next hg =>
                    rcases List.mem_singleton.mp hin with rfl
                    refine G4c.orAll_intro ?_ (ihA (B :: Γ) C)
                    refine List.mem_append.mpr (Or.inr
                      (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                    simp only
                    rw [if_pos hg]
                    exact .head _
                  next hg =>
                    split at hin
                    next => cases hin
                    next hq =>
                      rcases List.mem_singleton.mp hin with rfl
                      refine G4c.orAll_intro ?_
                        (and_mono (G4c.init (.head _)) (ihA (B :: Γ) C))
                      refine List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨(prop q).ifThen B, hFΓ, ?_⟩))
                      simp only
                      rw [if_neg hg, if_neg hq]
                      exact .head _
              | falsePLL => cases hin
              | and A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro ?_
                    (ihA (A₁.ifThen (B₁.ifThen B) :: Γ) C)
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.and B₁).ifThen B, hFΓ, .head _⟩))
              | or A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  refine G4c.orAll_intro ?_
                    (ihA (A₁.ifThen B :: B₁.ifThen B :: Γ) C)
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.or B₁).ifThen B, hFΓ, .head _⟩))
              | ifThen A₁ B₁ =>
                  rcases List.mem_singleton.mp hin with rfl
                  have hE := ihE (B₁.ifThen B :: Γ)
                  simp only [interE] at hE
                  refine G4c.orAll_intro ?_
                    (and_mono
                      (imp_mono hE (ihA (B₁.ifThen B :: Γ) (A₁.ifThen B₁)))
                      (ihA (B :: Γ) C))
                  exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                    ⟨(A₁.ifThen B₁).ifThen B, hFΓ, .head _⟩))
              | somehow A₁ =>
                  rcases List.mem_cons.mp hin with rfl | hin'
                  · refine G4c.orAll_intro ?_
                      (and_mono (ihA Γ A₁) (ihA (B :: Γ) C))
                    exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
                      ⟨A₁.somehow.ifThen B, hFΓ, .head _⟩))
                  · rcases List.mem_cons.mp hin' with rfl | hin''
                    · have hE := ihE Γ
                      simp only [interE] at hE
                      refine G4c.orAll_intro ?_
                        (and_mono
                          (box_mono (imp_mono hE (ihA Γ A₁.somehow)))
                          (ihA (B :: Γ) C))
                      exact List.mem_append.mpr (Or.inr
                        (List.mem_flatMap.mpr ⟨A₁.somehow.ifThen B, hFΓ,
                          List.mem_cons.mpr (Or.inr (.head _))⟩))
                    · obtain ⟨X, hXΓ, heq⟩ := List.mem_filterMap.mp hin''
                      cases X with
                      | somehow x =>
                          injection heq with heq'
                          subst heq'
                          have hE := ihE (x :: Γ)
                          simp only [interE] at hE
                          refine G4c.orAll_intro ?_
                            (and_mono
                              (box_mono
                                (imp_mono hE (ihA (x :: Γ) A₁.somehow)))
                              (ihA (B :: Γ) C))
                          refine List.mem_append.mpr (Or.inr
                            (List.mem_flatMap.mpr
                              ⟨A₁.somehow.ifThen B, hFΓ, ?_⟩))
                          exact List.mem_cons.mpr (Or.inr
                            (List.mem_cons.mpr (Or.inr
                              (List.mem_filterMap.mpr ⟨x.somehow, hXΓ, rfl⟩))))
                      | prop _ => cases heq
                      | falsePLL => cases heq
                      | and _ _ => cases heq
                      | or _ _ => cases heq
                      | ifThen _ _ => cases heq

/-- Multi-step fuel monotonicity, ∃-side. -/
theorem interE_fuel_mono_le (p : String) {f f' : Nat} (h : f ≤ f')
    (Γ : List PLLFormula) : G4c [interE p f' Γ] (interE p f Γ) := by
  induction h with
  | refl => exact G4c.iden (.head _)
  | @step m _ ih =>
      exact G4c.cut ((inter_fuel_mono p m).1 Γ)
        ((ih.weaken _).perm (List.Perm.swap _ _ _))

/-- Multi-step fuel monotonicity, ∀-side. -/
theorem interA_fuel_mono_le (p : String) {f f' : Nat} (h : f ≤ f')
    (Γ : List PLLFormula) (C : PLLFormula) :
    G4c [interA p f Γ C] (interA p f' Γ C) := by
  induction h with
  | refl => exact G4c.iden (.head _)
  | @step m _ ih =>
      exact G4c.cut ih
        ((((inter_fuel_mono p m).2 Γ C).weaken _).perm (List.Perm.swap _ _ _))

end PLLND
