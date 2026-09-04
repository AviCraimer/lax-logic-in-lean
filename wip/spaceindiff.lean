import LaxLogic.PLLG4UITrunc
import absorb_base
import adequacy
import packaging

/-!
# WIP: space-indifference for the truncated quantifiers (v3.1)

The value of `itpE`/`itpA` depends on the space `S` only through the
guard answers on *reachable pieces*: two spaces that agree on the
piece-closure of the data give the **same** formula (literal `Eq`,
not just interderivability).  This is the `SpaceIndiffE`/`SpaceIndiffA`
hypothesis pair of `wip/packaging.lean` (hSI): the packaged quantifier
fixes a Γ-only space while adequacy instantiates a consumer-dependent
one; indifference glues them.

Clause-by-clause, every space gate of the tables tests a member of
the closure of the current data, and every recursive call's data has
closure inside the current closure:

* growth gates `A ∈ S`, `B ∈ S` (∧/∨ clauses), `B ∈ S` (⊃-prop),
  `A⊃(B⊃D) ∈ S` (⊃-∧), `A⊃D, B⊃D ∈ S` (⊃-∨), `D ∈ S`, `B⊃D ∈ S`
  (⊃-⊃), `B ∈ S` (⊃-◯) — pieces of the principal `F ∈ Γ`, all in
  `pieceClosure F`;
* jump gates `(A⊃B)⊃D ∈ S`, `◯A⊃B ∈ S` — the member `F` itself
  (`self_mem_pieceClosure`);
* witness gates `x ∉ S` (γ-loops, *negative* position) — `x` a piece
  of a context member `◯x ∈ Γ`; agreement is an iff, so negative
  occurrences transfer the same way;
* context extensions insert only such pieces, and the `A13` goal
  clause inserts the goal antecedent `C₁` with *no* gate — covered
  because `pieceClosure` of an implication contains the closure of
  its antecedent (`imp_mem`-style field); jump goals `A⊃B`, `A`,
  `◯A` are antecedent pieces of their principal member for the same
  reason;
* the ◯-goal truncation disjunct tests `(itpAoth …).isEmpty` — not a
  space gate; it agrees once the `itpAoth` lists are proved equal.

Shape of the induction: plain induction on the fuel (every recursive
call in the tables is at `fuel`), threading the agreement invariant —
no `mu` arithmetic at all.  The clause mechanics are cloned from
`wip/indiff.lean`: `itpE_succ`/`itpA_succ` + `congr 1`,
`List.flatMap_congr`/`List.filterMap_congr`, per-clause `simp only`
with the agreement iffs to align the two guard columns, then
`split_ifs` and the IH.

Build (absorb_base, adequacy, packaging consumed as precompiled
oleans):

    lake env lean wip/absorb_base.lean -o <depdir>/absorb_base.olean
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/adequacy.lean -o <depdir>/adequacy.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/packaging.lean -o <depdir>/packaging.olean'
    lake env sh -c 'LEAN_PATH="$LEAN_PATH:<depdir>" lean wip/spaceindiff.lean'
-/

open PLLFormula

set_option maxHeartbeats 4000000

namespace PLLND

/-! ### Piece-closure subset kit

One-step containments of `pieceClosure` along exactly the pieces the
clause tables test and insert; each is `pieceClosure_trans` at the
head membership fact given by the named unfolding equations of
`wip/packaging.lean`. -/

private theorem pcSub_and_left {A B : PLLFormula} :
    pieceClosure A ⊆ pieceClosure (A.and B) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_and])

private theorem pcSub_and_right {A B : PLLFormula} :
    pieceClosure B ⊆ pieceClosure (A.and B) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_and])

private theorem pcSub_or_left {A B : PLLFormula} :
    pieceClosure A ⊆ pieceClosure (A.or B) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_or])

private theorem pcSub_or_right {A B : PLLFormula} :
    pieceClosure B ⊆ pieceClosure (A.or B) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_or])

private theorem pcSub_box {χ : PLLFormula} :
    pieceClosure χ ⊆ pieceClosure χ.somehow :=
  pieceClosure_trans _ _ (by simp [pieceClosure_box])

/-- Antecedent closure: `pieceClosure` of an implication contains the
closure of its antecedent (all six antecedent shapes). -/
private theorem pcSub_ant {X D : PLLFormula} :
    pieceClosure X ⊆ pieceClosure (X.ifThen D) := by
  refine pieceClosure_trans _ _ ?_
  cases X with
  | prop a => simp [pieceClosure_impProp]
  | falsePLL => simp [pieceClosure_impFalse]
  | and A B => simp [pieceClosure_impAnd]
  | or A B => simp [pieceClosure_impOr]
  | ifThen A B => simp [pieceClosure_impImp]
  | somehow Y => simp [pieceClosure_impBox]

/-- Consequent closure. -/
private theorem pcSub_csq {X D : PLLFormula} :
    pieceClosure D ⊆ pieceClosure (X.ifThen D) := by
  refine pieceClosure_trans _ _ ?_
  cases X with
  | prop a => simp [pieceClosure_impProp]
  | falsePLL => simp [pieceClosure_impFalse]
  | and A B => simp [pieceClosure_impAnd]
  | or A B => simp [pieceClosure_impOr]
  | ifThen A B => simp [pieceClosure_impImp]
  | somehow Y => simp [pieceClosure_impBox]

private theorem pcSub_impAnd {A B D : PLLFormula} :
    pieceClosure (A.ifThen (B.ifThen D)) ⊆ pieceClosure ((A.and B).ifThen D) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_impAnd])

private theorem pcSub_impOr_left {A B D : PLLFormula} :
    pieceClosure (A.ifThen D) ⊆ pieceClosure ((A.or B).ifThen D) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_impOr])

private theorem pcSub_impOr_right {A B D : PLLFormula} :
    pieceClosure (B.ifThen D) ⊆ pieceClosure ((A.or B).ifThen D) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_impOr])

private theorem pcSub_impImp {A B D : PLLFormula} :
    pieceClosure (B.ifThen D) ⊆ pieceClosure ((A.ifThen B).ifThen D) :=
  pieceClosure_trans _ _ (by simp [pieceClosure_impImp])

/-! ### Agreement bookkeeping -/

/-- Extending an agreement-covered context by a covered formula. -/
private theorem ag_cons {S S' : Finset PLLFormula} {x : PLLFormula}
    {Γ : List PLLFormula}
    (hx : ∀ φ ∈ pieceClosure x, ((φ ∈ S) ↔ (φ ∈ S')))
    (h : ∀ F ∈ Γ, ∀ φ ∈ pieceClosure F, ((φ ∈ S) ↔ (φ ∈ S'))) :
    ∀ F ∈ x :: Γ, ∀ φ ∈ pieceClosure F, ((φ ∈ S) ↔ (φ ∈ S')) := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · exact hx
  · exact h F hF

/-! ### The space-indifference lemma -/

/-- **Space indifference.**  Two spaces that agree on the
piece-closure of the context (and, for `itpA`, of the goal) give the
*same* formula, at every fuel and budget.  Plain fuel induction: the
agreement iffs align the two guard columns clause by clause, and
every recursive call's data stays inside the closure. -/
theorem itp_space_indiff (p : String) (S S' : Finset PLLFormula) : ∀ (f : Nat),
    (∀ b Γ, (∀ F ∈ Γ, ∀ φ ∈ pieceClosure F, ((φ ∈ S) ↔ (φ ∈ S'))) →
      itpE p S f b Γ = itpE p S' f b Γ) ∧
    (∀ b Γ C, (∀ F ∈ Γ, ∀ φ ∈ pieceClosure F, ((φ ∈ S) ↔ (φ ∈ S'))) →
      (∀ φ ∈ pieceClosure C, ((φ ∈ S) ↔ (φ ∈ S'))) →
      itpA p S f b Γ C = itpA p S' f b Γ C) := by
  intro f
  induction f with
  | zero => exact ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ f' IH =>
      obtain ⟨ihE, ihA⟩ := IH
      constructor
      · -- E-half
        intro b Γ hag
        rw [itpE_succ p S f' b Γ, itpE_succ p S' f' b Γ]
        congr 1
        unfold itpEcls
        congr 1
        refine List.flatMap_congr ?_
        intro F hF
        cases F with
        | prop q => rfl
        | falsePLL => rfl
        | and A B =>
            dsimp only
            have hA := hag _ hF _ (pcSub_and_left (self_mem_pieceClosure A))
            have hB := hag _ hF _ (pcSub_and_right (self_mem_pieceClosure B))
            have hext := ag_cons (fun φ hφ => hag _ hF _ (pcSub_and_left hφ))
              (ag_cons (fun φ hφ => hag _ hF _ (pcSub_and_right hφ)) hag)
            simp only [hA, hB]
            split_ifs with h1 h2
            · rfl
            · rw [ihE b (A :: B :: Γ) hext]
            · rfl
        | or A B =>
            dsimp only
            have hA := hag _ hF _ (pcSub_or_left (self_mem_pieceClosure A))
            have hB := hag _ hF _ (pcSub_or_right (self_mem_pieceClosure B))
            have hextA := ag_cons (fun φ hφ => hag _ hF _ (pcSub_or_left hφ)) hag
            have hextB := ag_cons (fun φ hφ => hag _ hF _ (pcSub_or_right hφ)) hag
            simp only [hA, hB]
            split_ifs with h1 h2
            · rfl
            · rw [ihE b (A :: Γ) hextA, ihE b (B :: Γ) hextB]
            · rfl
        | somehow χ =>
            dsimp only
            have hχ := hag _ hF _ (pcSub_box (self_mem_pieceClosure χ))
            have hext := ag_cons (fun φ hφ => hag _ hF _ (pcSub_box hφ)) hag
            simp only [hχ]
            split_ifs with h1
            · rfl
            · rw [ihE b (χ :: Γ) hext]
        | ifThen X D =>
            cases X with
            | falsePLL => rfl
            | prop q =>
                dsimp only
                have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                have hext := ag_cons (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                simp only [hD]
                split_ifs with h1 h2 h3 h4
                · rfl
                · rw [ihE b (D :: Γ) hext]
                · rfl
                · rw [ihE b (D :: Γ) hext]
                · rfl
            | and A B =>
                dsimp only
                have hcur := hag _ hF _
                  (pcSub_impAnd (self_mem_pieceClosure (A.ifThen (B.ifThen D))))
                have hext := ag_cons
                  (fun φ hφ => hag _ hF _ (pcSub_impAnd hφ)) hag
                simp only [hcur]
                split_ifs with h1 h2
                · rfl
                · rw [ihE b (A.ifThen (B.ifThen D) :: Γ) hext]
                · rfl
            | or A B =>
                dsimp only
                have hAD := hag _ hF _
                  (pcSub_impOr_left (self_mem_pieceClosure (A.ifThen D)))
                have hBD := hag _ hF _
                  (pcSub_impOr_right (self_mem_pieceClosure (B.ifThen D)))
                have hext := ag_cons
                  (fun φ hφ => hag _ hF _ (pcSub_impOr_left hφ))
                  (ag_cons (fun φ hφ => hag _ hF _ (pcSub_impOr_right hφ)) hag)
                simp only [hAD, hBD]
                split_ifs with h1 h2
                · rfl
                · rw [ihE b (A.ifThen D :: B.ifThen D :: Γ) hext]
                · rfl
            | ifThen A B =>
                -- F = (A⊃B)⊃D
                dsimp only
                have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                have hFS := hag _ hF _
                  (self_mem_pieceClosure ((A.ifThen B).ifThen D))
                have hBD := hag _ hF _
                  (pcSub_impImp (self_mem_pieceClosure (B.ifThen D)))
                have hAB : ∀ φ ∈ pieceClosure (A.ifThen B),
                    ((φ ∈ S) ↔ (φ ∈ S')) :=
                  fun φ hφ => hag _ hF _ (pcSub_ant hφ)
                have hextD := ag_cons
                  (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                have hextBD := ag_cons
                  (fun φ hφ => hag _ hF _ (pcSub_impImp hφ)) hag
                simp only [hD, hFS, hBD]
                split_ifs with h1 h2 h3 h4 h5
                · rfl
                · -- jump branch: B⊃D present, (A⊃B)⊃D in the space
                  cases b with
                  | zero => rfl
                  | succ b' =>
                      dsimp only
                      rw [ihE b' Γ hag, ihA b' Γ (A.ifThen B) hag hAB,
                        ihE (b' + 1) (D :: Γ) hextD]
                · rfl
                · -- fresh-piece branch: B⊃D ∈ S ∖ Γ
                  rw [ihE b (B.ifThen D :: Γ) hextBD,
                    ihA b (B.ifThen D :: Γ) (A.ifThen B) hextBD hAB,
                    ihE b (D :: Γ) hextD]
                · rfl
                · rfl
            | somehow A =>
                -- F = ◯A⊃D
                dsimp only
                have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                have hFS := hag _ hF _
                  (self_mem_pieceClosure (A.somehow.ifThen D))
                have hOA : ∀ φ ∈ pieceClosure A.somehow,
                    ((φ ∈ S) ↔ (φ ∈ S')) :=
                  fun φ hφ => hag _ hF _ (pcSub_ant hφ)
                have hextD := ag_cons
                  (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                simp only [hD, hFS]
                split_ifs with h1 h2 h3
                · rfl
                · -- present-branch live: ◯A⊃D ∈ S
                  congr 1
                  · cases b with
                    | zero => rfl
                    | succ b' =>
                        dsimp only
                        rw [ihA b' Γ A hag (fun φ hφ => hOA _ (pcSub_box hφ)),
                          ihE (b' + 1) (D :: Γ) hextD, ihE b' Γ hag,
                          ihA b' Γ A.somehow hag hOA]
                  · refine List.filterMap_congr ?_
                    intro X hX
                    cases X with
                    | prop _ => rfl
                    | falsePLL => rfl
                    | and _ _ => rfl
                    | or _ _ => rfl
                    | ifThen _ _ => rfl
                    | somehow x =>
                        dsimp only
                        have hx := hag _ hX _
                          (pcSub_box (self_mem_pieceClosure x))
                        have hxext := ag_cons
                          (fun φ hφ => hag _ hX _ (pcSub_box hφ)) hag
                        simp only [hx]
                        split_ifs with hx1
                        · rfl
                        · rw [ihE b (x :: Γ) hxext,
                            ihA b (x :: Γ) A.somehow hxext hOA,
                            ihE b (D :: Γ) hextD]
                · -- present-branch dead: only the γ-loop
                  congr 1
                  refine List.filterMap_congr ?_
                  intro X hX
                  cases X with
                  | prop _ => rfl
                  | falsePLL => rfl
                  | and _ _ => rfl
                  | or _ _ => rfl
                  | ifThen _ _ => rfl
                  | somehow x =>
                      dsimp only
                      have hx := hag _ hX _
                        (pcSub_box (self_mem_pieceClosure x))
                      have hxext := ag_cons
                        (fun φ hφ => hag _ hX _ (pcSub_box hφ)) hag
                      simp only [hx]
                      split_ifs with hx1
                      · rfl
                      · rw [ihE b (x :: Γ) hxext,
                          ihA b (x :: Γ) A.somehow hxext hOA,
                          ihE b (D :: Γ) hextD]
                · rfl
      · -- A-half
        intro b Γ C hag hagC
        rw [itpA_succ p S f' b Γ C, itpA_succ p S' f' b Γ C]
        have hgoal : itpAgoal p S f' b Γ C = itpAgoal p S' f' b Γ C := by
          cases C with
          | prop q => rfl
          | falsePLL => rfl
          | and C₁ C₂ =>
              simp only [itpAgoal]
              rw [ihA b Γ C₁ hag (fun φ hφ => hagC _ (pcSub_and_left hφ)),
                ihA b Γ C₂ hag (fun φ hφ => hagC _ (pcSub_and_right hφ))]
          | or C₁ C₂ =>
              simp only [itpAgoal]
              rw [ihA b Γ C₁ hag (fun φ hφ => hagC _ (pcSub_or_left hφ)),
                ihA b Γ C₂ hag (fun φ hφ => hagC _ (pcSub_or_right hφ))]
          | ifThen C₁ C₂ =>
              have hext := ag_cons (fun φ hφ => hagC _ (pcSub_ant hφ)) hag
              have hC2 : ∀ φ ∈ pieceClosure C₂, ((φ ∈ S) ↔ (φ ∈ S')) :=
                fun φ hφ => hagC _ (pcSub_csq hφ)
              simp only [itpAgoal]
              split_ifs with h1
              · cases b with
                | zero => rfl
                | succ b' =>
                    dsimp only
                    rw [ihE b' (C₁ :: Γ) hext,
                      ihA (b' + 1) (C₁ :: Γ) C₂ hext hC2]
              · rw [ihE b (C₁ :: Γ) hext, ihA b (C₁ :: Γ) C₂ hext hC2]
          | somehow D =>
              simp only [itpAgoal]
              cases b with
              | zero => rfl
              | succ b' =>
                  dsimp only
                  rw [ihE b' Γ hag,
                    ihA (b' + 1) Γ D hag (fun φ hφ => hagC _ (pcSub_box hφ))]
        have henv : itpAenv p S f' b Γ C = itpAenv p S' f' b Γ C := by
          unfold itpAenv
          refine List.flatMap_congr ?_
          intro F hF
          cases F with
          | prop q => rfl
          | falsePLL => rfl
          | and A B =>
              dsimp only
              have hA := hag _ hF _ (pcSub_and_left (self_mem_pieceClosure A))
              have hB := hag _ hF _ (pcSub_and_right (self_mem_pieceClosure B))
              have hext := ag_cons (fun φ hφ => hag _ hF _ (pcSub_and_left hφ))
                (ag_cons (fun φ hφ => hag _ hF _ (pcSub_and_right hφ)) hag)
              simp only [hA, hB]
              split_ifs with h1 h2
              · rfl
              · rw [ihA b (A :: B :: Γ) C hext hagC]
              · rfl
          | or A B =>
              dsimp only
              have hA := hag _ hF _ (pcSub_or_left (self_mem_pieceClosure A))
              have hB := hag _ hF _ (pcSub_or_right (self_mem_pieceClosure B))
              have hextA := ag_cons (fun φ hφ => hag _ hF _ (pcSub_or_left hφ)) hag
              have hextB := ag_cons (fun φ hφ => hag _ hF _ (pcSub_or_right hφ)) hag
              simp only [hA, hB]
              split_ifs with h1 h2
              · rfl
              · rw [ihE b (A :: Γ) hextA, ihA b (A :: Γ) C hextA hagC,
                  ihE b (B :: Γ) hextB, ihA b (B :: Γ) C hextB hagC]
              · rfl
          | somehow χ =>
              cases C with
              | prop _ => rfl
              | falsePLL => rfl
              | and _ _ => rfl
              | or _ _ => rfl
              | ifThen _ _ => rfl
              | somehow D =>
                  dsimp only
                  have hχ := hag _ hF _ (pcSub_box (self_mem_pieceClosure χ))
                  have hext := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_box hφ)) hag
                  simp only [hχ]
                  split_ifs with h1
                  · rfl
                  · rw [ihE b (χ :: Γ) hext,
                      ihA b (χ :: Γ) D.somehow hext hagC]
          | ifThen X D =>
              cases X with
              | falsePLL => rfl
              | prop q =>
                  dsimp only
                  have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                  have hext := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                  simp only [hD]
                  split_ifs with h1 h2 h3 h4
                  · rfl
                  · rw [ihA b (D :: Γ) C hext hagC]
                  · rfl
                  · rw [ihA b (D :: Γ) C hext hagC]
                  · rfl
              | and A B =>
                  dsimp only
                  have hcur := hag _ hF _
                    (pcSub_impAnd (self_mem_pieceClosure (A.ifThen (B.ifThen D))))
                  have hext := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_impAnd hφ)) hag
                  simp only [hcur]
                  split_ifs with h1 h2
                  · rfl
                  · rw [ihA b (A.ifThen (B.ifThen D) :: Γ) C hext hagC]
                  · rfl
              | or A B =>
                  dsimp only
                  have hAD := hag _ hF _
                    (pcSub_impOr_left (self_mem_pieceClosure (A.ifThen D)))
                  have hBD := hag _ hF _
                    (pcSub_impOr_right (self_mem_pieceClosure (B.ifThen D)))
                  have hext := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_impOr_left hφ))
                    (ag_cons (fun φ hφ => hag _ hF _ (pcSub_impOr_right hφ)) hag)
                  simp only [hAD, hBD]
                  split_ifs with h1 h2
                  · rfl
                  · rw [ihA b (A.ifThen D :: B.ifThen D :: Γ) C hext hagC]
                  · rfl
              | ifThen A B =>
                  -- F = (A⊃B)⊃D
                  dsimp only
                  have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                  have hFS := hag _ hF _
                    (self_mem_pieceClosure ((A.ifThen B).ifThen D))
                  have hBD := hag _ hF _
                    (pcSub_impImp (self_mem_pieceClosure (B.ifThen D)))
                  have hAB : ∀ φ ∈ pieceClosure (A.ifThen B),
                      ((φ ∈ S) ↔ (φ ∈ S')) :=
                    fun φ hφ => hag _ hF _ (pcSub_ant hφ)
                  have hextD := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                  have hextBD := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_impImp hφ)) hag
                  simp only [hD, hFS, hBD]
                  split_ifs with h1 h2 h3 h4 h5
                  · rfl
                  · -- jump branch
                    cases b with
                    | zero => rfl
                    | succ b' =>
                        dsimp only
                        rw [ihE b' Γ hag, ihA b' Γ (A.ifThen B) hag hAB,
                          ihA (b' + 1) (D :: Γ) C hextD hagC]
                  · rfl
                  · -- fresh-piece branch
                    rw [ihE b (B.ifThen D :: Γ) hextBD,
                      ihA b (B.ifThen D :: Γ) (A.ifThen B) hextBD hAB,
                      ihA b (D :: Γ) C hextD hagC]
                  · rfl
                  · rfl
              | somehow A =>
                  -- F = ◯A⊃D
                  dsimp only
                  have hD := hag _ hF _ (pcSub_csq (self_mem_pieceClosure D))
                  have hFS := hag _ hF _
                    (self_mem_pieceClosure (A.somehow.ifThen D))
                  have hOA : ∀ φ ∈ pieceClosure A.somehow,
                      ((φ ∈ S) ↔ (φ ∈ S')) :=
                    fun φ hφ => hag _ hF _ (pcSub_ant hφ)
                  have hextD := ag_cons
                    (fun φ hφ => hag _ hF _ (pcSub_csq hφ)) hag
                  simp only [hD, hFS]
                  split_ifs with h1 h2 h3
                  · rfl
                  · -- present-branch live
                    congr 1
                    · cases b with
                      | zero => rfl
                      | succ b' =>
                          dsimp only
                          rw [ihA b' Γ A hag (fun φ hφ => hOA _ (pcSub_box hφ)),
                            ihA (b' + 1) (D :: Γ) C hextD hagC,
                            ihE b' Γ hag, ihA b' Γ A.somehow hag hOA]
                    · refine List.filterMap_congr ?_
                      intro X hX
                      cases X with
                      | prop _ => rfl
                      | falsePLL => rfl
                      | and _ _ => rfl
                      | or _ _ => rfl
                      | ifThen _ _ => rfl
                      | somehow x =>
                          dsimp only
                          have hx := hag _ hX _
                            (pcSub_box (self_mem_pieceClosure x))
                          have hxext := ag_cons
                            (fun φ hφ => hag _ hX _ (pcSub_box hφ)) hag
                          simp only [hx]
                          split_ifs with hx1
                          · rfl
                          · rw [ihE b (x :: Γ) hxext,
                              ihA b (x :: Γ) A.somehow hxext hOA,
                              ihA b (D :: Γ) C hextD hagC]
                  · -- present-branch dead: only the γ-loop
                    congr 1
                    refine List.filterMap_congr ?_
                    intro X hX
                    cases X with
                    | prop _ => rfl
                    | falsePLL => rfl
                    | and _ _ => rfl
                    | or _ _ => rfl
                    | ifThen _ _ => rfl
                    | somehow x =>
                        dsimp only
                        have hx := hag _ hX _
                          (pcSub_box (self_mem_pieceClosure x))
                        have hxext := ag_cons
                          (fun φ hφ => hag _ hX _ (pcSub_box hφ)) hag
                        simp only [hx]
                        split_ifs with hx1
                        · rfl
                        · rw [ihE b (x :: Γ) hxext,
                            ihA b (x :: Γ) A.somehow hxext hOA,
                            ihA b (D :: Γ) C hextD hagC]
                  · rfl
        have hoth : itpAoth p S f' b Γ C = itpAoth p S' f' b Γ C := by
          unfold itpAoth
          rw [hgoal, henv]
        congr 1
        cases C with
        | prop q => exact hoth
        | falsePLL => exact hoth
        | and _ _ => exact hoth
        | or _ _ => exact hoth
        | ifThen _ _ => exact hoth
        | somehow D =>
            simp only [itpAfull]
            rw [hoth]
            congr 1
            split_ifs with hemp
            · rfl
            · cases b with
              | zero => rfl
              | succ b' =>
                  dsimp only
                  rw [ihE b' Γ hag]

/-! ### Corollaries: union form, subset form, and the hSI dischargers -/

/-- **Space indifference (E), union form.**  Agreement on the context
closure suffices. -/
theorem itpE_space_indiff (p : String) {S S' : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula}
    (h : ∀ φ ∈ pieceClosureList Γ, ((φ ∈ S) ↔ (φ ∈ S'))) :
    itpE p S f b Γ = itpE p S' f b Γ :=
  (itp_space_indiff p S S' f).1 b Γ
    (fun _F hF _φ hφ => h _ (pieceClosure_subset_pieceClosureList hF hφ))

/-- **Space indifference (A), union form.**  Agreement on the context
and goal closures suffices. -/
theorem itpA_space_indiff (p : String) {S S' : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (h : ∀ φ ∈ pieceClosureList Γ ∪ pieceClosure C, ((φ ∈ S) ↔ (φ ∈ S'))) :
    itpA p S f b Γ C = itpA p S' f b Γ C :=
  (itp_space_indiff p S S' f).2 b Γ C
    (fun _F hF _φ hφ => h _ (Finset.mem_union_left _
      (pieceClosure_subset_pieceClosureList hF hφ)))
    (fun _φ hφ => h _ (Finset.mem_union_right _ hφ))

/-- **Space indifference (E), subset form.**  Two spaces that both
contain the context closure agree: every gate tests a closure member,
where both memberships are true (positive gates) resp. both
non-memberships false (the negative γ-witness gates). -/
theorem itpE_space_indiff_of_subset (p : String) {S S' : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula}
    (hS : pieceClosureList Γ ⊆ S) (hS' : pieceClosureList Γ ⊆ S') :
    itpE p S f b Γ = itpE p S' f b Γ :=
  itpE_space_indiff p (fun _φ hφ => iff_of_true (hS hφ) (hS' hφ))

/-- **Space indifference (A), subset form.** -/
theorem itpA_space_indiff_of_subset (p : String) {S S' : Finset PLLFormula}
    {f b : Nat} {Γ : List PLLFormula} {C : PLLFormula}
    (hS : pieceClosureList Γ ∪ pieceClosure C ⊆ S)
    (hS' : pieceClosureList Γ ∪ pieceClosure C ⊆ S') :
    itpA p S f b Γ C = itpA p S' f b Γ C :=
  itpA_space_indiff p (fun _φ hφ => iff_of_true (hS hφ) (hS' hφ))

/-- **hSI discharged (E side)**: the `SpaceIndiffE` hypothesis of
`wip/packaging.lean` holds outright (the `PieceClosed` side
conditions are not even needed). -/
theorem spaceIndiffE (p : String) : SpaceIndiffE p :=
  fun _S _S' _f _b _Γ _ _ hS hS' =>
    itpE_space_indiff_of_subset p hS hS'

/-- **hSI discharged (A side)**: the `SpaceIndiffA` hypothesis of
`wip/packaging.lean` holds outright. -/
theorem spaceIndiffA (p : String) : SpaceIndiffA p :=
  fun _S _S' _f _b _Γ _C _ _ hSΓ hSΓ' hSC hSC' =>
    itpA_space_indiff_of_subset p
      (Finset.union_subset hSΓ hSC) (Finset.union_subset hSΓ' hSC')

end PLLND
