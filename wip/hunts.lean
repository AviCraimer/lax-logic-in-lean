import LaxLogic.PLLUIChains
import LaxLogic.PLLNoFall
import LaxLogic.PLLCtxCompleteness
import wip.gapWidth
import wip.uiObstruct
import wip.collapse
import wip.rungbound
import wip.wlanding

/-!
# The two hunts, instantiated: the chains are armed

`LaxLogic/PLLUIChains.lean` proves the two refutation criteria generically.
This file instantiates them with the repository's mechanised chains, so that
each hunt is reduced to exactly its two remaining obligations about a witness
formula `φ`.

* **∀p side**: the ascending chain is `chainF k = ◯t(2k+1)`, strictness
  `chain_lt_strict` (`wip/chainStrict.lean`).
* **∃p side**: the descending chain is `Gmeet n` (the gap partial meets),
  strictness proved HERE (`Gmeet_strict`) from the `cmE` machinery of
  `wip/gapWidth.lean` — a fact the floor campaign never needed to pin.

`P` is instantiated at `NoFall.VarFree` (closed = variable-free), which at one
propositional variable is exactly `p`-freeness.  Closedness of the chain
members is proved via a substitution lemma: `embed = substP pv ◯⊥` produces a
variable-free formula whenever the argument mentions at most `pv`.
-/

open PLLFormula

namespace PLLND
namespace Hunts

open SemUI RNEmbed UIChains NoFall

/-! ## Closedness of the chain members -/

/-- `A` mentions at most the variable `pv`. -/
def OnlyPv : PLLFormula → Prop
  | .prop a     => a = RNEmbed.pv
  | .falsePLL   => True
  | .and φ ψ    => OnlyPv φ ∧ OnlyPv ψ
  | .or φ ψ     => OnlyPv φ ∧ OnlyPv ψ
  | .ifThen φ ψ => OnlyPv φ ∧ OnlyPv ψ
  | .somehow φ  => OnlyPv φ

/-- Substituting `◯⊥` for `pv` in an `OnlyPv` formula is variable-free. -/
theorem varFree_embed : ∀ (A : PLLFormula), OnlyPv A → VarFree (RNEmbed.embed A)
  | .prop a, h => by
      have h' : a = RNEmbed.pv := h
      show VarFree (if a = RNEmbed.pv then RNEmbed.oBot else .prop a)
      rw [if_pos h']
      exact (trivial : VarFree RNEmbed.oBot)
  | .falsePLL, _ => trivial
  | .and φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .or φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .ifThen φ ψ, h => ⟨varFree_embed φ h.1, varFree_embed ψ h.2⟩
  | .somehow φ, h => varFree_embed φ h

/-- Both components of every `rnP k` mention at most `pv`. -/
theorem onlyPv_rnP : ∀ k : Nat, OnlyPv (rnP k).1 ∧ OnlyPv (rnP k).2
  | 0 => ⟨rfl, ⟨rfl, trivial⟩⟩
  | k + 1 =>
      let ih := onlyPv_rnP k
      ⟨⟨ih.1, ih.2⟩, ⟨⟨ih.1, ih.2⟩, ih.1⟩⟩

/-- Every rung mentions at most `pv`. -/
theorem onlyPv_rn : ∀ n : Nat, OnlyPv (rn n)
  | 0 => trivial
  | n + 1 => by
      show OnlyPv (if n % 2 = 0 then (rnP (n / 2)).1 else (rnP (n / 2)).2)
      split
      · exact (onlyPv_rnP _).1
      · exact (onlyPv_rnP _).2

/-- The substituted rungs are variable-free. -/
theorem varFree_rnSub (n : Nat) : VarFree (rnSub n) :=
  varFree_embed (rn n) (onlyPv_rn n)

/-- The boxed odd rungs are variable-free. -/
theorem varFree_chainF (k : Nat) : VarFree (chainF k) :=
  varFree_rnSub (2 * k + 1)

/-- The gaps are variable-free. -/
theorem varFree_gap (k : Nat) : VarFree (gap k) :=
  ⟨varFree_chainF k, varFree_rnSub (2 * k + 1)⟩

/-- The gap partial meets are variable-free. -/
theorem varFree_Gmeet : ∀ n : Nat, VarFree (Gmeet n)
  | 0 => varFree_gap 1
  | n + 1 => ⟨varFree_Gmeet n, varFree_gap (n + 2)⟩

/-! ## Strict descent of `Gmeet`

`Gmeet (n+1) = Gmeet n ∧ gap (n+2)`, so strictness is
`Gmeet n ⊬ gap (n+2)`.  Countermodel: the edged lift `cmE (n+1)`, at whose
world `some (n+4)` every gap except `n+2`, `n+3` is forced (`gap_forced`) —
in particular gaps `1..n+1`, hence `Gmeet n` — while `gap (n+2)` fails
(`gap_fails`). -/

/-- `Gmeet n` is forced wherever gaps `1..n+1` are. -/
theorem force_Gmeet_cmE (m : Nat) (x : Nat)
    (h : ∀ k : Nat, 1 ≤ k → k ≤ m → (cmE m).force (some x) (gap k)) :
    ∀ n : Nat, n + 1 ≤ m → (cmE m).force (some x) (Gmeet n)
  | 0, hn => h 1 (by omega) (by omega)
  | n + 1, hn =>
      ⟨force_Gmeet_cmE m x h n (by omega), h (n + 2) (by omega) (by omega)⟩

/-- **Strict descent**: `Gmeet n ⊬ gap (n+2)`, hence
`Gmeet n ⊬ Gmeet (n+1)`. -/
theorem Gmeet_strict (n : Nat) : ¬ Deriv [Gmeet n] (Gmeet (n + 1)) := by
  rintro ⟨d⟩
  -- soundness at cmE (n+1), world n+4
  have hs := soundness d (cmE (n + 1)) (some (n + 4)) (fun ψ hψ => by
    have e : ψ = Gmeet n := by
      cases hψ with
      | head => rfl
      | tail _ h' => cases h'
    subst e
    exact force_Gmeet_cmE (n + 1) (n + 4)
      (fun k hk1 hk2 => gap_forced (n + 1) k (by omega) (by omega) (n + 4))
      n (by omega))
  exact gap_fails (n + 1) (n + 2) (by omega) (by omega) hs.2

/-! ## The armed criteria -/

/-- **The ∃p hunt, armed.**  A witness `φ` now needs exactly two facts:
it lies below every `Gmeet n`, and its variable-free consequences are trapped
above the chain.  Given those, `φ` has NO least variable-free consequence —
no post-interpolant — and uniform interpolation fails at one variable. -/
theorem no_existsP_of_trap (φ : PLLFormula)
    (hbelow : ∀ n, Deriv [φ] (Gmeet n))
    (htrap : ∀ ψ, VarFree ψ → Deriv [φ] ψ → ∃ n, Deriv [Gmeet n] ψ) :
    ¬ ∃ χ, VarFree χ ∧ Deriv [φ] χ ∧
        (∀ ψ, VarFree ψ → Deriv [φ] ψ → Deriv [χ] ψ) :=
  no_least_consequence VarFree Gmeet varFree_Gmeet Gmeet_strict φ hbelow htrap

/-- **The ∀p hunt, armed.**  A witness `φ` now needs exactly two facts:
every `chainF k` entails it, and every variable-free formula entailing it sits
below some `chainF k`.  Given those, `φ` has NO greatest variable-free
antecedent — no pre-interpolant. -/
theorem no_forallP_of_trap (φ : PLLFormula)
    (habove : ∀ k, Deriv [chainF k] φ)
    (htrap : ∀ ψ, VarFree ψ → Deriv [ψ] φ → ∃ k, Deriv [ψ] (chainF k)) :
    ¬ ∃ χ, VarFree χ ∧ Deriv [χ] φ ∧
        (∀ ψ, VarFree ψ → Deriv [ψ] φ → Deriv [ψ] χ) :=
  no_greatest_antecedent VarFree chainF varFree_chainF
    (fun k => chain_step_strict k) φ habove htrap

/-! ## Both hunts, as armed, are VACUOUS — neither witness can exist

Before searching for a witness `φ`, check whether one COULD exist. It cannot,
on either side, and the reason is a pair of "collapse" theorems the earlier
campaign already proved for a different purpose (`wip/collapse.lean`,
`wip/rungbound.lean`): a formula pulled all the way to the bottom of the gap
chain collapses onto a single rung; a formula pulled all the way to the top of
the `chainF` chain collapses onto an outright THEOREM. Both collapses hand
back a trivial witness that breaks the trap condition immediately.

## The `∃p` side: `post_interp_exists` already IS the refutation of the trap

`collapse` (`hg : ∀k≥1, φ⊢gap k → ∃m, φ⊢rnSub m`) gives `post_interp_exists`:
every gap-entailing `φ` has a CLOSED consequence `ψ` that ITSELF entails every
gap. That `ψ` is exactly what breaks `htrap`: `htrap` would need
`Gmeet n ⊢ ψ` for some `n`, but `ψ` entailing every gap means `ψ ⊢ Gmeet n`
for ALL `n` (via `gmeet_of_hg`) — in particular `ψ ⊢ Gmeet (n+1)` — so
`Gmeet n ⊢ ψ ⊢ Gmeet (n+1)` gives `Gmeet n ⊢ Gmeet (n+1)`, contradicting
`Gmeet_strict`. So `htrap` can NEVER hold together with `hbelow`: the two
premises of `no_existsP_of_trap` are jointly unsatisfiable. -/

/-- `atomFree` (Bool) and `VarFree` (Prop) are the same notion; the bridge is
a structural induction. -/
theorem varFree_of_atomFree : ∀ (A : PLLFormula),
    LaxInfinite.atomFree A = true → VarFree A
  | .prop _, h => by simp [LaxInfinite.atomFree] at h
  | .falsePLL, _ => trivial
  | .and a b, h => by
      simp only [LaxInfinite.atomFree, Bool.and_eq_true] at h
      exact ⟨varFree_of_atomFree a h.1, varFree_of_atomFree b h.2⟩
  | .or a b, h => by
      simp only [LaxInfinite.atomFree, Bool.and_eq_true] at h
      exact ⟨varFree_of_atomFree a h.1, varFree_of_atomFree b h.2⟩
  | .ifThen a b, h => by
      simp only [LaxInfinite.atomFree, Bool.and_eq_true] at h
      exact ⟨varFree_of_atomFree a h.1, varFree_of_atomFree b h.2⟩
  | .somehow a, h => varFree_of_atomFree a h

/-- `hbelow`'s shape converts to `collapse`'s `hg` shape. -/
theorem hbelow_to_hg {φ : PLLFormula} (hbelow : ∀ n, Deriv [φ] (Gmeet n)) :
    ∀ k, 1 ≤ k → Deriv [φ] (gap k) := by
  intro k hk
  exact Deriv.cutHead (hbelow (k - 1))
    ((show k - 1 + 1 = k from by omega) ▸ Gmeet_proj (k - 1) k hk (by omega))

/-- **The `∃p` trap is UNSATISFIABLE.**  No `φ` can ever meet both premises
of `no_existsP_of_trap` at once, so the hunt via `Gmeet` is closed — not by
exhausting candidates, but by showing none can exist. This is the same fact
the earlier campaign proved as `post_interp_schema_vacuous`
(`wip/collapse.lean`), reached here as a direct corollary of
`no_existsP_of_trap`'s own hypotheses. -/
theorem existsP_trap_unsatisfiable :
    ¬ ∃ φ : PLLFormula, (∀ n, Deriv [φ] (Gmeet n)) ∧
        (∀ ψ, VarFree ψ → Deriv [φ] ψ → ∃ n, Deriv [Gmeet n] ψ) := by
  rintro ⟨φ, hbelow, htrap⟩
  have hg := hbelow_to_hg hbelow
  obtain ⟨ψ, hψVF, hψgap, hψφ⟩ := post_interp_exists hg
  obtain ⟨n, hn⟩ := htrap ψ (varFree_of_atomFree ψ hψVF) hψφ
  exact Gmeet_strict n (Deriv.cutHead hn (gmeet_of_hg hψgap (n + 1)))

/-! ## The `∀p` side: `c_chain_bound_is_theorem` is the mirror collapse

`c_chain_bound_is_theorem` (`hc : ∀k, chainF k ⊢ φ → ⊢ φ`) says a formula
entailed from EVERY level of the ascending chain is an outright theorem. Then
`⊤` is a closed formula with `⊢ φ` (weakening the empty-context proof), so
`htrap` would need `⊤ ⊢ chainF k` for some `k` — i.e. `chainF k` itself a
theorem. It never is: `chain_step_strict k` already forbids it (a theorem
weakens into `Deriv [chainF (k+1)] (chainF k)`, contradicting strictness
directly). So `htrap` can never hold together with `habove` either. -/

/-- No `chainF k` is a theorem — a one-line consequence of `chain_step_strict`
via weakening, no new semantic content needed. -/
theorem chainF_not_theorem (k : Nat) : ¬ Deriv [] (chainF k) := by
  rintro ⟨d⟩
  exact chain_step_strict k ⟨d.rename (fun _ h => by cases h)⟩

/-- **The `∀p` trap is UNSATISFIABLE.**  No `φ` can ever meet both premises of
`no_forallP_of_trap` at once, so the hunt via `chainF` is closed the same way —
the mirror of `existsP_trap_unsatisfiable`, and the same fact the earlier
campaign proved as `pre_interp_schema_vacuous` (`wip/rungbound.lean`). -/
theorem forallP_trap_unsatisfiable :
    ¬ ∃ φ : PLLFormula, (∀ k, Deriv [chainF k] φ) ∧
        (∀ ψ, VarFree ψ → Deriv [ψ] φ → ∃ k, Deriv [ψ] (chainF k)) := by
  rintro ⟨φ, habove, htrap⟩
  have hthm : Deriv [] φ := c_chain_bound_is_theorem habove
  obtain ⟨d⟩ := hthm
  have hψφ : Deriv [truePLL] φ :=
    ⟨d.rename (fun _ h => by cases h)⟩
  obtain ⟨k, hk⟩ := htrap truePLL varFree_truePLL hψφ
  exact chainF_not_theorem k (Deriv.cutHead ⟨PLLND.Ctx.truePLL_intro []⟩ hk)

end Hunts
end PLLND

/-! ### Axiom audit — measured and pinned on creation (2026-08-08). -/

/-- info: 'PLLND.Hunts.Gmeet_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.Gmeet_strict

/-- info: 'PLLND.Hunts.no_existsP_of_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.no_existsP_of_trap

/-- info: 'PLLND.Hunts.no_forallP_of_trap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.no_forallP_of_trap

/-- info: 'PLLND.Hunts.existsP_trap_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.existsP_trap_unsatisfiable

/-- info: 'PLLND.Hunts.forallP_trap_unsatisfiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.forallP_trap_unsatisfiable

/-- info: 'PLLND.Hunts.chainF_not_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms PLLND.Hunts.chainF_not_theorem
