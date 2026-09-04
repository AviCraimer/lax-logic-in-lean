/- # Archive: LJF simplification round 1 — superseded proofs (2026-08-09)

This file is NOT built (Archive/ is outside the Lake package roots). It
preserves, verbatim, the top-level artefacts deleted from LaxLogic/LJF.lean
by simplification round 1, for future archaeologists. The complete
pre-simplification state is tag `ljf-ui-v1` (= commit 7aefbdc, the landmark
"UNIFORM INTERPOLATION FOR LJF — PROVED").

Why each block was superseded (docs/ljf-simplification-pass.md §2):

* `eMin`/`aMin` — minimality of both modes PARAMETRISED by the saturated-
  case statements SatE2/SatA2. Strictly subsumed by `eMinF`/`aMinF`, which
  prove the same statements unconditionally with the saturated case
  discharged inline. These were the working theorems for most of the
  campaign; they became scaffolding the day the mega-mutual landed.
* `qAssemble`/`dykAssemble` — the `.up`-conclusion instances of
  `qAssembleN`/`dykAssembleN`; every use site now goes through
  `unStable (·N ·)`, which is literally the same term unfolded.
* `ΩOk` (+ .cons/.head/.tail) — the pending-list invariant with a
  done-atom alternative. The alternative became unreachable once the deep
  forced patterns (`.rel (.atomL (.stable s'))`) handled shifted atoms, so
  the invariant reverted to plain `PFreeΩ`. The `if hd : ↑a ∈ done`
  branches in TInv/TpInv's `.atomL` arms (the alternative's only consumers)
  were collapsed at the same time — see the tag for their text.
-/

/-! ## eMin / aMin (was LJF.lean Part 5, lines 2725–3022 at ljf-ui-v1) -/

/-- **Minimality of `∃p`, modulo the saturated case**: any `p`-free
consequence of the context follows from its interpolant.  Every processing
clause is its inverse transformation followed by the recursive call; the
saturated case is `satE`. -/
def eMin (p : String) (satE : SatE2 p) :
    ∀ (todo done Δ : List Neg) (ψ : Neg), ParkedCtx done →
      PFreeCtx p Δ → PFreeN p ψ →
      Inv ((todo ++ done) ++ Δ) [] ψ →
      Inv (interp p todo done none :: Δ) [] ψ
  | .up (.atom a) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE todo (.up (.atom a) :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ hψ
        (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, ψ, _, _, _, _ => by
      rw [interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      refine nOrAllElim _ (List.mem_cons_self ..) ?_
      intro x hx Γ' hsub
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine ((eMin p satE (b ++ todo) done Δ ψ hP hΔ hψ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (hsub _ (List.mem_cons_of_mem _ hZ))
  | .up (.down M) :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE (M :: todo) done Δ ψ hP hΔ hψ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE (M :: N :: todo) done Δ ψ hP hΔ hψ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE todo done Δ ψ hP hΔ hψ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE todo (.imp (.atom a) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ hψ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ ψ hP hΔ hψ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE (.imp P' N :: todo) done Δ ψ hP hΔ hψ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ ψ
        hP hΔ hψ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, ψ, hP, hΔ, hψ, d => by
      rw [interp]
      exact eMin p satE todo (.imp (.down (.imp Q' N')) N :: done) Δ ψ
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ hψ
        (d.wk subParkOut)
  | [], done, Δ, ψ, hP, hΔ, hψ, d => by
      match hf : findFire done (splits done) with
      | some (a, N, rest) =>
          have eq1 : interp p [] done none = interp p [N] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1]
          exact eMin p satE [N] rest Δ ψ
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ hψ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satE done Δ ψ hf hP hΔ hψ d
  termination_by todo done _ _ => 2 * sum3 todo + sum3 done
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact dec_drop
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
      | (have h1 := p3_pos (wNeg M); omega)
      | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega); omega)

/-- **Minimality of `∀p`, modulo the saturated case**: any route from the
context beside `p`-free material to the goal factors through the `∀p`
interpolant, given the `∃p` interpolant as a hypothesis. -/
def aMin (p : String) (satA : SatA2 p) :
    ∀ (todo done Δ : List Neg) (G : Neg), ParkedCtx done → PFreeCtx p Δ →
      Inv ((todo ++ done) ++ Δ) [] G →
      Inv (interp p todo done none :: Δ) [] (interp p todo done (some G))
  | .up (.atom a) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA todo (.up (.atom a) :: done) Δ G
        (ParkedCtx.cons (ParkedN.atom a) hP) hΔ (d.wk subParkOut)
  | .up .fls :: todo, done, Δ, G, _, _, _ => by
      rw [interp, interp]
      exact nBotElim _ (List.mem_cons_self ..)
  | .up (.or P Q) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      refine nAndAllIntro ?_
      intro x hx
      obtain ⟨⟨b, hb⟩, hmem, hEq⟩ := memMapWitness _ _ x hx
      subst hEq
      refine .impR (.downL ?_)
      refine ((aMin p satA (b ++ todo) done Δ G hP hΔ
        ((invUp (d.wk subHeadOut) b hb).wk subChainIn)).wk ?_)
      intro Z hZ
      rcases List.mem_cons.mp hZ with rfl | hZ
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hZ)
  | .up (.down M) :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA (M :: todo) done Δ G hP hΔ
        (((invUp (d.wk subHeadOut) [M] (by simp [invertPos]))).wk subChainIn)
  | .and M N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA (M :: N :: todo) done Δ G hP hΔ
        ((invAndHyp (d.wk subHeadOut)).wk (subChainIn (b := [M, N])))
  | .imp .fls N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA todo done Δ G hP hΔ (invImpFls (d.wk subHeadOut))
  | .imp (.atom a) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA todo (.imp (.atom a) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.qimp a N) hP) hΔ
        (d.wk subParkOut)
  | .imp (.or Q₁ Q₂) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA (.imp Q₁ N :: .imp Q₂ N :: todo) done Δ G hP hΔ
        ((invImpOr (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp Q₁ N, .imp Q₂ N])))
  | .imp (.down (.up P')) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA (.imp P' N :: todo) done Δ G hP hΔ
        ((invStrip (d.wk subHeadOut)).wk (subChainIn (b := [.imp P' N])))
  | .imp (.down (.and M₁ M₂)) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA (.imp (.down M₁) (.imp (.down M₂) N) :: todo) done Δ G
        hP hΔ
        ((invCurry (d.wk subHeadOut)).wk
          (subChainIn (b := [.imp (.down M₁) (.imp (.down M₂) N)])))
  | .imp (.down (.imp Q' N')) N :: todo, done, Δ, G, hP, hΔ, d => by
      rw [interp, interp]
      exact aMin p satA todo (.imp (.down (.imp Q' N')) N :: done) Δ G
        (ParkedCtx.cons (ParkedN.dyk Q' N' N) hP) hΔ
        (d.wk subParkOut)
  | [], done, Δ, (.imp Q N), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.imp Q N)) =
              interp p [N'] rest (some (.imp Q N)) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.imp Q N)
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.imp Q N) hf hP hΔ d
  | [], done, Δ, (.and M N), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.and M N)) =
              interp p [N'] rest (some (.and M N)) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.and M N)
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.and M N) hf hP hΔ d
  | [], done, Δ, (.up (.atom q)), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.up (.atom q))) =
              interp p [N'] rest (some (.up (.atom q))) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.up (.atom q))
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.up (.atom q)) hf hP hΔ d
  | [], done, Δ, (.up .fls), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.up .fls)) =
              interp p [N'] rest (some (.up .fls)) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.up .fls)
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.up .fls) hf hP hΔ d
  | [], done, Δ, (.up (.or P₁ P₂)), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.up (.or P₁ P₂))) =
              interp p [N'] rest (some (.up (.or P₁ P₂))) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.up (.or P₁ P₂))
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.up (.or P₁ P₂)) hf hP hΔ d
  | [], done, Δ, (.up (.down M)), hP, hΔ, d => by
      match hf : findFire done (splits done) with
      | some (a, N', rest) =>
          have eq1 : interp p [] done none = interp p [N'] rest none := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          have eq2 : interp p [] done (some (.up (.down M))) =
              interp p [N'] rest (some (.up (.down M))) := by
            rw [interp]; split
            all_goals rename_i heq
            · rw [hf] at heq; cases heq; rfl
            · rw [hf] at heq; cases heq
          rw [eq1, eq2]
          exact aMin p satA [N'] rest Δ (.up (.down M))
            (ParkedCtx.sub (splits_sub (findFire_mem hf)) hP) hΔ (invFireHyp (findFire_mem hf) d)
      | none =>
          exact satA done Δ (.up (.down M)) hf hP hΔ d
  termination_by todo done _ G => 2 * sum3 todo + sum3 done + 3 ^ wNeg G
  decreasing_by
    all_goals simp_wf
    all_goals simp only [sum3, sum3_append, goalW, wNeg, wPos]
    all_goals first
      | exact dec_dyk0 (by assumption)
      | exact dec_park
      | exact dec_shift1
      | exact dec_and
      | exact dec_curry
      | exact dec_stripshift
      | exact dec_drop
      | exact dec_impor (wPos_pos _) (wPos_pos _)
      | exact dec_orctx (by assumption)
      | (have h1 := invertPos_lt (P := Pos.or _ _)
           (by intro a h; nomatch h) _ (by assumption)
         simp only [wPos] at h1; omega)
      | exact Nat.lt_of_lt_of_le (dec_fire (by assumption)) (by omega)
      | exact Nat.lt_of_lt_of_le (dec_qimp (by assumption)) (by omega)
      | (have h1 := p3_pos (wNeg M); omega)
      | (have h1 := p3_strict (a := wNeg M) (b := wNeg M + 1) (by omega); omega)

/-! ## qAssemble / dykAssemble (was lines 3217–3253 at ljf-ui-v1) -/

/-- Fire the `q`-implication conjunct: the atom from `sa`, the recursively
interpolated body consumed through `δ`. -/
def qAssemble {done rest K : List Neg} {a : String} {N : Neg} {P : Pos}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : pGuard p a nTop (.imp (.atom a) (interp p [N] rest none)) ∈ L)
    (hap : ¬ a = p)
    (sa : Stab (interp p [] done none :: K) (.atom a))
    (δ : Inv (interp p [N] rest none :: K) [] (.up P)) :
    Stab (interp p [] done none :: K) P :=
  unStable (simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem (by
          simp only [pGuard]; rw [if_neg hap]
          exact LFoc.impL (sa.wk hs) lf)))
    (Sub.grow _) δ)

/-- Fire the Dyckhoff conjunct: the antecedent interpolant from `sant`, the
recursively interpolated body consumed through `δ`. -/
def dykAssemble {done rest K : List Neg} {Q' : Pos} {N' N : Neg} {P : Pos}
    {L : List Neg}
    (hE : interp p [] done none = nAndAll L)
    (hmem : nAnd
        (.imp (.down (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
             (interp p [N] rest none))
        (interp p [.imp (.down N') N] rest none) ∈ L)
    (sant : Inv (interp p [] done none :: K) []
      (interp p [.imp (.down N') N] rest (some (.imp Q' N'))))
    (δ : Inv (interp p [N] rest none :: K) [] (.up P)) :
    Stab (interp p [] done none :: K) P :=
  unStable (simHyp
    (fl := fun hs lf =>
      .lfoc (hs _ (List.mem_cons_self ..))
        (hE.symm ▸ lfocAndAll hmem
          (.and1 (.impL (.rfoc (.rel (sant.wk hs))) lf))))
    (Sub.grow _) δ)

/-! ## ΩOk and its lemmas (was lines 3280–3301 at ljf-ui-v1) -/

/-- Pending entries are `p`-free or atoms already present in `done` —
the invariant that lets inversion push `done`-atoms back without breaking
the `p`-freeness of the kept side. -/
def ΩOk (p : String) (done : List Neg) (Ω : List Pos) : Prop :=
  ∀ Q ∈ Ω, PFreeP p Q ∨ ∃ a, Q = .atom a ∧ Neg.up (.atom a) ∈ done

theorem ΩOk.cons {p : String} {done : List Neg} {Q : Pos} {Ω : List Pos}
    (hQ : PFreeP p Q ∨ ∃ a, Q = .atom a ∧ Neg.up (.atom a) ∈ done)
    (h : ΩOk p done Ω) : ΩOk p done (Q :: Ω) := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | hZ
  · exact hQ
  · exact h Z hZ

theorem ΩOk.head {p : String} {done : List Neg} {Q : Pos} {Ω : List Pos}
    (h : ΩOk p done (Q :: Ω)) :
    PFreeP p Q ∨ ∃ a, Q = .atom a ∧ Neg.up (.atom a) ∈ done :=
  h Q (List.mem_cons_self ..)

theorem ΩOk.tail {p : String} {done : List Neg} {Q : Pos} {Ω : List Pos}
    (h : ΩOk p done (Q :: Ω)) : ΩOk p done Ω :=
  fun Z hZ => h Z (List.mem_cons_of_mem _ hZ)
