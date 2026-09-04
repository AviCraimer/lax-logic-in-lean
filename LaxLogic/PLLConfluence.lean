import LaxLogic.PLLTopTop

/-!
# Confluence of the proof-term reduction

Church–Rosser for the full reduction `Step` of `PLLTerms.lean` — β for
every connective together with `let`-β and `let`-assoc — by Newman's
lemma: the reduction is strongly normalising (`strong_normalisation`,
the ⊤⊤-lifting theorem of `PLLTopTop.lean`), so it suffices to prove
**local confluence**, the one-step diamond up to multi-step rejoining:

  `Step t u₁ → Step t u₂ → ∃ v, Steps u₁ v ∧ Steps u₂ v`.

Local confluence is a case analysis of how two redexes can overlap.
Steps in disjoint subterms commute in one step each; a step inside a
redex is chased by the substitution lemmas the strong-normalisation
development already proves (`Step.subst`, `Tm.subst1_steps_arg`,
`Step.rename`); and the genuine critical pairs are confined to `bind`:

* `let`-β under `let`-assoc, on `bind (bind (val s) t) u` — rejoined by
  `bind_subst1_merge`: instantiating a merged frame is binding the
  instance against the original frame;
* `let`-assoc under `let`-assoc, on `bind (bind (bind s t) u) v` — the
  associativity pentagon, rejoined by one further association on each
  side and the `skip1`/`skip1` renaming square.

Newman's lemma then gives **confluence** (`confluence`), by
well-founded induction along the reduction order, and with it:

* uniqueness of normal forms (`normal_form_unique`);
* **conversion** `Conv` (the equivalence closure of reduction) is
  exactly joinability (`conv_iff_joinable`), Church–Rosser in its
  classical formulation;
* conversion is decided by the total normaliser:
  `Conv t u ↔ t.normalize = u.normalize` (`conv_iff_normalize_eq`);
* convertible normal forms are equal (`conv_nf_eq`).

Downstream, `PLLIdempotency.lean` uses this to upgrade the
non-invertibility of the idempotence pair from "no reduction sequence"
to "no conversion at all".
-/

open PLLFormula

namespace PLLND

/-! ## Local confluence -/

/-- Joinability is symmetric. -/
private theorem sw {Γ : List PLLFormula} {φ : PLLFormula} {a b : Tm Γ φ}
    (h : ∃ v, Steps a v ∧ Steps b v) : ∃ v, Steps b v ∧ Steps a v :=
  let ⟨v, h₁, h₂⟩ := h
  ⟨v, h₂, h₁⟩

/-- Any second step out of a β-redex rejoins its contractum. -/
private theorem join_beta {Γ : List PLLFormula} {A B : PLLFormula}
    (b : Tm (A :: Γ) B) (s : Tm Γ A) {u₂ : Tm Γ B}
    (h : Step (.app (.lam b) s) u₂) :
    ∃ v, Steps (b.subst1 s) v ∧ Steps u₂ v := by
  cases h with
  | beta => exact ⟨_, .refl _, .refl _⟩
  | appCong₁ hf =>
    cases hf with
    | lamCong hb =>
      exact ⟨_, .head (Step.subst _ hb) (.refl _), .head (.beta _ _) (.refl _)⟩
  | appCong₂ hs =>
    exact ⟨_, Tm.subst1_steps_arg b hs, .head (.beta _ _) (.refl _)⟩

private theorem join_fstPair {Γ : List PLLFormula} {A B : PLLFormula}
    (a : Tm Γ A) (b : Tm Γ B) {u₂ : Tm Γ A}
    (h : Step (.fst (.pair a b)) u₂) :
    ∃ v, Steps a v ∧ Steps u₂ v := by
  cases h with
  | fstPair => exact ⟨_, .refl _, .refl _⟩
  | fstCong hp =>
    cases hp with
    | pairCong₁ ha => exact ⟨_, .head ha (.refl _), .head (.fstPair _ _) (.refl _)⟩
    | pairCong₂ hb => exact ⟨_, .refl _, .head (.fstPair _ _) (.refl _)⟩

private theorem join_sndPair {Γ : List PLLFormula} {A B : PLLFormula}
    (a : Tm Γ A) (b : Tm Γ B) {u₂ : Tm Γ B}
    (h : Step (.snd (.pair a b)) u₂) :
    ∃ v, Steps b v ∧ Steps u₂ v := by
  cases h with
  | sndPair => exact ⟨_, .refl _, .refl _⟩
  | sndCong hp =>
    cases hp with
    | pairCong₁ ha => exact ⟨_, .refl _, .head (.sndPair _ _) (.refl _)⟩
    | pairCong₂ hb => exact ⟨_, .head hb (.refl _), .head (.sndPair _ _) (.refl _)⟩

private theorem join_caseInl {Γ : List PLLFormula} {A B C : PLLFormula}
    (a : Tm Γ A) (c₁ : Tm (A :: Γ) C) (c₂ : Tm (B :: Γ) C) {u₂ : Tm Γ C}
    (h : Step (.case (.inl a) c₁ c₂) u₂) :
    ∃ v, Steps (c₁.subst1 a) v ∧ Steps u₂ v := by
  cases h with
  | caseInl => exact ⟨_, .refl _, .refl _⟩
  | caseCong₀ h =>
    cases h with
    | inlCong ha =>
      exact ⟨_, Tm.subst1_steps_arg c₁ ha, .head (.caseInl _ _ _) (.refl _)⟩
  | caseCong₁ h =>
    exact ⟨_, .head (Step.subst _ h) (.refl _), .head (.caseInl _ _ _) (.refl _)⟩
  | caseCong₂ h =>
    exact ⟨_, .refl _, .head (.caseInl _ _ _) (.refl _)⟩

private theorem join_caseInr {Γ : List PLLFormula} {A B C : PLLFormula}
    (a : Tm Γ B) (c₁ : Tm (A :: Γ) C) (c₂ : Tm (B :: Γ) C) {u₂ : Tm Γ C}
    (h : Step (.case (.inr a) c₁ c₂) u₂) :
    ∃ v, Steps (c₂.subst1 a) v ∧ Steps u₂ v := by
  cases h with
  | caseInr => exact ⟨_, .refl _, .refl _⟩
  | caseCong₀ h =>
    cases h with
    | inrCong ha =>
      exact ⟨_, Tm.subst1_steps_arg c₂ ha, .head (.caseInr _ _ _) (.refl _)⟩
  | caseCong₁ h =>
    exact ⟨_, .refl _, .head (.caseInr _ _ _) (.refl _)⟩
  | caseCong₂ h =>
    exact ⟨_, .head (Step.subst _ h) (.refl _), .head (.caseInr _ _ _) (.refl _)⟩

private theorem join_bindVal {Γ : List PLLFormula} {A B : PLLFormula}
    (a : Tm Γ A) (u₀ : Tm (A :: Γ) (somehow B)) {u₂ : Tm Γ (somehow B)}
    (h : Step (.bind (.val a) u₀) u₂) :
    ∃ v, Steps (u₀.subst1 a) v ∧ Steps u₂ v := by
  cases h with
  | bindVal => exact ⟨_, .refl _, .refl _⟩
  | bindCong₁ h =>
    cases h with
    | valCong ha =>
      exact ⟨_, Tm.subst1_steps_arg u₀ ha, .head (.bindVal _ _) (.refl _)⟩
  | bindCong₂ h =>
    exact ⟨_, .head (Step.subst _ h) (.refl _), .head (.bindVal _ _) (.refl _)⟩

/-- Any second step out of a `let`-assoc redex rejoins its contractum.
The two genuine critical pairs of the calculus live here: `let`-β and
`let`-assoc firing inside the scrutinee. -/
private theorem join_bindAssoc {Γ : List PLLFormula} {A B C : PLLFormula}
    (s₀ : Tm Γ (somehow A)) (t₀ : Tm (A :: Γ) (somehow B))
    (u₀ : Tm (B :: Γ) (somehow C)) {u₂ : Tm Γ (somehow C)}
    (h : Step (.bind (.bind s₀ t₀) u₀) u₂) :
    ∃ v, Steps (.bind s₀ (.bind t₀ (u₀.rename Ren.skip1))) v ∧ Steps u₂ v := by
  cases h with
  | bindAssoc => exact ⟨_, .refl _, .refl _⟩
  | bindCong₁ h =>
    cases h with
    | bindVal a₀ =>
      -- let-β under let-assoc: rejoined by the merged-frame equation.
      refine ⟨_, .head (.bindVal _ _) ?_, .refl _⟩
      rw [bind_subst1_merge]
      exact .refl _
    | @bindAssoc _ A₁ _ _ s₁ s₂ _ =>
      -- the associativity pentagon: one more association on the left,
      -- two on the right, meeting modulo the skip1/skip1 square.
      have sq : ((u₀.rename (Ren.skip1 (φ := A))).rename
            (Ren.lift (Ren.skip1 (φ := A₁))))
          = ((u₀.rename (Ren.skip1 (φ := A₁))).rename (Ren.skip1 (φ := A))) := by
        rw [Tm.rename_rename, Tm.rename_rename]
        exact u₀.rename_congr (by lift_cases)
      refine ⟨_, .head (.bindAssoc _ _ _) (.refl _),
        .head (.bindAssoc _ _ _) (.head (.bindCong₂ (.bindAssoc _ _ _)) ?_)⟩
      show Steps (.bind s₁ (.bind s₂ (.bind (t₀.rename Ren.skip1)
        ((u₀.rename (Ren.skip1 (φ := A₁))).rename (Ren.skip1 (φ := A)))))) _
      rw [← sq]
      exact .refl _
    | bindCong₁ ha =>
      exact ⟨_, .head (.bindCong₁ ha) (.refl _), .head (.bindAssoc _ _ _) (.refl _)⟩
    | bindCong₂ hb =>
      exact ⟨_, .head (.bindCong₂ (.bindCong₁ hb)) (.refl _),
        .head (.bindAssoc _ _ _) (.refl _)⟩
  | bindCong₂ h =>
    exact ⟨_, .head (.bindCong₂ (.bindCong₂ (Step.rename _ h))) (.refl _),
      .head (.bindAssoc _ _ _) (.refl _)⟩

/-- **Local confluence** of the full reduction: two one-step reducts of
one term have a common multi-step reduct. -/
theorem local_confluence {Γ : List PLLFormula} {φ : PLLFormula}
    {t u₁ u₂ : Tm Γ φ} (h₁ : Step t u₁) (h₂ : Step t u₂) :
    ∃ v, Steps u₁ v ∧ Steps u₂ v := by
  induction h₁ with
  | beta b s => exact join_beta b s h₂
  | fstPair a b => exact join_fstPair a b h₂
  | sndPair a b => exact join_sndPair a b h₂
  | caseInl a c₁ c₂ => exact join_caseInl a c₁ c₂ h₂
  | caseInr a c₁ c₂ => exact join_caseInr a c₁ c₂ h₂
  | bindVal a u₀ => exact join_bindVal a u₀ h₂
  | bindAssoc s₀ t₀ u₀ => exact join_bindAssoc s₀ t₀ u₀ h₂
  | abortCong h ih =>
    cases h₂ with
    | abortCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .abortCong hs) hv₁,
        Steps.cong (fun hs => .abortCong hs) hv₂⟩
  | lamCong h ih =>
    cases h₂ with
    | lamCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .lamCong hs) hv₁,
        Steps.cong (fun hs => .lamCong hs) hv₂⟩
  | appCong₁ h ih =>
    cases h₂ with
    | beta => exact sw (join_beta _ _ (.appCong₁ h))
    | appCong₁ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .appCong₁ hs) hv₁,
        Steps.cong (fun hs => .appCong₁ hs) hv₂⟩
    | appCong₂ h' =>
      exact ⟨_, .head (.appCong₂ h') (.refl _), .head (.appCong₁ h) (.refl _)⟩
  | appCong₂ h ih =>
    cases h₂ with
    | beta => exact sw (join_beta _ _ (.appCong₂ h))
    | appCong₁ h' =>
      exact ⟨_, .head (.appCong₁ h') (.refl _), .head (.appCong₂ h) (.refl _)⟩
    | appCong₂ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .appCong₂ hs) hv₁,
        Steps.cong (fun hs => .appCong₂ hs) hv₂⟩
  | pairCong₁ h ih =>
    cases h₂ with
    | pairCong₁ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .pairCong₁ hs) hv₁,
        Steps.cong (fun hs => .pairCong₁ hs) hv₂⟩
    | pairCong₂ h' =>
      exact ⟨_, .head (.pairCong₂ h') (.refl _), .head (.pairCong₁ h) (.refl _)⟩
  | pairCong₂ h ih =>
    cases h₂ with
    | pairCong₁ h' =>
      exact ⟨_, .head (.pairCong₁ h') (.refl _), .head (.pairCong₂ h) (.refl _)⟩
    | pairCong₂ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .pairCong₂ hs) hv₁,
        Steps.cong (fun hs => .pairCong₂ hs) hv₂⟩
  | fstCong h ih =>
    cases h₂ with
    | fstPair => exact sw (join_fstPair _ _ (.fstCong h))
    | fstCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .fstCong hs) hv₁,
        Steps.cong (fun hs => .fstCong hs) hv₂⟩
  | sndCong h ih =>
    cases h₂ with
    | sndPair => exact sw (join_sndPair _ _ (.sndCong h))
    | sndCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .sndCong hs) hv₁,
        Steps.cong (fun hs => .sndCong hs) hv₂⟩
  | inlCong h ih =>
    cases h₂ with
    | inlCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .inlCong hs) hv₁,
        Steps.cong (fun hs => .inlCong hs) hv₂⟩
  | inrCong h ih =>
    cases h₂ with
    | inrCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .inrCong hs) hv₁,
        Steps.cong (fun hs => .inrCong hs) hv₂⟩
  | caseCong₀ h ih =>
    cases h₂ with
    | caseInl a => exact sw (join_caseInl a _ _ (.caseCong₀ h))
    | caseInr a => exact sw (join_caseInr a _ _ (.caseCong₀ h))
    | caseCong₀ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .caseCong₀ hs) hv₁,
        Steps.cong (fun hs => .caseCong₀ hs) hv₂⟩
    | caseCong₁ h' =>
      exact ⟨_, .head (.caseCong₁ h') (.refl _), .head (.caseCong₀ h) (.refl _)⟩
    | caseCong₂ h' =>
      exact ⟨_, .head (.caseCong₂ h') (.refl _), .head (.caseCong₀ h) (.refl _)⟩
  | caseCong₁ h ih =>
    cases h₂ with
    | caseInl a => exact sw (join_caseInl a _ _ (.caseCong₁ h))
    | caseInr a => exact sw (join_caseInr a _ _ (.caseCong₁ h))
    | caseCong₀ h' =>
      exact ⟨_, .head (.caseCong₀ h') (.refl _), .head (.caseCong₁ h) (.refl _)⟩
    | caseCong₁ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .caseCong₁ hs) hv₁,
        Steps.cong (fun hs => .caseCong₁ hs) hv₂⟩
    | caseCong₂ h' =>
      exact ⟨_, .head (.caseCong₂ h') (.refl _), .head (.caseCong₁ h) (.refl _)⟩
  | caseCong₂ h ih =>
    cases h₂ with
    | caseInl a => exact sw (join_caseInl a _ _ (.caseCong₂ h))
    | caseInr a => exact sw (join_caseInr a _ _ (.caseCong₂ h))
    | caseCong₀ h' =>
      exact ⟨_, .head (.caseCong₀ h') (.refl _), .head (.caseCong₂ h) (.refl _)⟩
    | caseCong₁ h' =>
      exact ⟨_, .head (.caseCong₁ h') (.refl _), .head (.caseCong₂ h) (.refl _)⟩
    | caseCong₂ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .caseCong₂ hs) hv₁,
        Steps.cong (fun hs => .caseCong₂ hs) hv₂⟩
  | valCong h ih =>
    cases h₂ with
    | valCong h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .valCong hs) hv₁,
        Steps.cong (fun hs => .valCong hs) hv₂⟩
  | bindCong₁ h ih =>
    cases h₂ with
    | bindVal a => exact sw (join_bindVal a _ (.bindCong₁ h))
    | bindAssoc s₀ t₀ => exact sw (join_bindAssoc s₀ t₀ _ (.bindCong₁ h))
    | bindCong₁ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .bindCong₁ hs) hv₁,
        Steps.cong (fun hs => .bindCong₁ hs) hv₂⟩
    | bindCong₂ h' =>
      exact ⟨_, .head (.bindCong₂ h') (.refl _), .head (.bindCong₁ h) (.refl _)⟩
  | bindCong₂ h ih =>
    cases h₂ with
    | bindVal a => exact sw (join_bindVal a _ (.bindCong₂ h))
    | bindAssoc s₀ t₀ => exact sw (join_bindAssoc s₀ t₀ _ (.bindCong₂ h))
    | bindCong₁ h' =>
      exact ⟨_, .head (.bindCong₁ h') (.refl _), .head (.bindCong₂ h) (.refl _)⟩
    | bindCong₂ h' =>
      obtain ⟨v, hv₁, hv₂⟩ := ih h'
      exact ⟨_, Steps.cong (fun hs => .bindCong₂ hs) hv₁,
        Steps.cong (fun hs => .bindCong₂ hs) hv₂⟩

/-! ## Newman's lemma -/

/-- **Confluence** (Church–Rosser): two multi-step reducts of one term
have a common reduct.  By Newman's lemma — well-founded induction along
the reduction order supplied by `strong_normalisation`, rejoining the
first diverging steps with `local_confluence`. -/
theorem confluence {Γ : List PLLFormula} {φ : PLLFormula}
    {t u₁ u₂ : Tm Γ φ} (h₁ : Steps t u₁) (h₂ : Steps t u₂) :
    ∃ v, Steps u₁ v ∧ Steps u₂ v := by
  revert u₁ u₂
  have acc := strong_normalisation t
  induction acc with
  | intro t _ ih =>
    intro u₁ u₂ h₁ h₂
    cases h₁ with
    | refl _ => exact ⟨u₂, h₂, .refl _⟩
    | head s₁ r₁ =>
      cases h₂ with
      | refl _ => exact ⟨u₁, .refl _, .head s₁ r₁⟩
      | head s₂ r₂ =>
        obtain ⟨w, hw₁, hw₂⟩ := local_confluence s₁ s₂
        obtain ⟨v₁, hv₁, hv₁'⟩ := ih _ s₁ r₁ hw₁
        obtain ⟨v, hv₂, hv₂'⟩ := ih _ s₂ (hw₂.trans hv₁') r₂
        exact ⟨v, hv₁.trans hv₂, hv₂'⟩

/-! ## Uniqueness of normal forms -/

/-- A normal term's only reduct is itself. -/
theorem Steps.eq_of_nf {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} (h : Steps t u) (hn : Nf t) : u = t := by
  cases h with
  | refl _ => rfl
  | head s _ => exact (not_step_of_nf s hn).elim

/-- **Uniqueness of normal forms**: a term reduces to at most one
normal form. -/
theorem normal_form_unique {Γ : List PLLFormula} {φ : PLLFormula}
    {t u₁ u₂ : Tm Γ φ} (h₁ : Steps t u₁) (h₂ : Steps t u₂)
    (n₁ : Nf u₁) (n₂ : Nf u₂) : u₁ = u₂ := by
  obtain ⟨v, hv₁, hv₂⟩ := confluence h₁ h₂
  rw [← Steps.eq_of_nf hv₁ n₁, ← Steps.eq_of_nf hv₂ n₂]

/-! ## Conversion -/

/-- Conversion: the equivalence closure of one-step reduction — the
"interconvertibility" of terms. -/
inductive Conv {Γ : List PLLFormula} {φ : PLLFormula} :
    Tm Γ φ → Tm Γ φ → Prop
  | of_step {t u : Tm Γ φ} : Step t u → Conv t u
  | refl (t : Tm Γ φ) : Conv t t
  | symm {t u : Tm Γ φ} : Conv t u → Conv u t
  | trans {t u v : Tm Γ φ} : Conv t u → Conv u v → Conv t v

/-- Reduction is conversion. -/
theorem Steps.conv {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} (h : Steps t u) : Conv t u := by
  induction h with
  | refl t => exact .refl t
  | head s _ ih => exact (Conv.of_step s).trans ih

/-- **Church–Rosser, classical formulation**: convertible terms have a
common reduct. -/
theorem Conv.joinable {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} (h : Conv t u) : ∃ v, Steps t v ∧ Steps u v := by
  induction h with
  | of_step s => exact ⟨_, .head s (.refl _), .refl _⟩
  | refl t => exact ⟨t, .refl _, .refl _⟩
  | symm _ ih => exact sw ih
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨v₁, hv₁, hv₁'⟩ := ih₁
    obtain ⟨v₂, hv₂, hv₂'⟩ := ih₂
    obtain ⟨v, hv, hv'⟩ := confluence hv₁' hv₂
    exact ⟨v, hv₁.trans hv, hv₂'.trans hv'⟩

/-- Conversion is exactly joinability. -/
theorem conv_iff_joinable {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} : Conv t u ↔ ∃ v, Steps t v ∧ Steps u v :=
  ⟨Conv.joinable, fun ⟨_, h₁, h₂⟩ => h₁.conv.trans h₂.conv.symm⟩

/-- Convertible normal forms are equal. -/
theorem conv_nf_eq {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} (h : Conv t u) (n₁ : Nf t) (n₂ : Nf u) : t = u := by
  obtain ⟨v, hv₁, hv₂⟩ := h.joinable
  rw [← Steps.eq_of_nf hv₁ n₁, ← Steps.eq_of_nf hv₂ n₂]

/-- **Conversion is decided by the normaliser**: two terms are
interconvertible exactly when the total normaliser sends them to the
same normal form. -/
theorem conv_iff_normalize_eq {Γ : List PLLFormula} {φ : PLLFormula}
    {t u : Tm Γ φ} : Conv t u ↔ t.normalize = u.normalize := by
  constructor
  · intro h
    exact conv_nf_eq
      (((Tm.normalize_spec t).1.conv.symm.trans h).trans (Tm.normalize_spec u).1.conv)
      (Tm.normalize_spec t).2 (Tm.normalize_spec u).2
  · intro h
    exact ((Tm.normalize_spec t).1.conv.trans (h ▸ Conv.refl _)).trans
      (Tm.normalize_spec u).1.conv.symm

/-! ## Axiom audit (build-time guards) -/

/-- info: 'PLLND.local_confluence' depends on axioms: [propext] -/
#guard_msgs in
#print axioms local_confluence

/-- info: 'PLLND.confluence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms confluence

/-- info: 'PLLND.conv_iff_normalize_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conv_iff_normalize_eq

end PLLND
