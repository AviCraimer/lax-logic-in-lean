import wip.chainOff

/-!
# RN classification, stage 2–3: codes, tables, semantic correctness

`docs/rn-classification-plan.md` stages 2 and 3.  `UpCode` names the
up-sets of the ladder: `bot = ∅`, `odd a = [0,a] = T(rn(2a+1))`,
`even a = [0,a−1] ∪ {a+1} = T(rn(2a+2))`, `top = ℕ`.  The three tables
compute the Heyting operations on these sets (fully enumerated matches,
so every case reduces after `cases`); `memC_meet/join/imp` verify them
pointwise against the ladder, and `sat_cls` classifies the ladder truth
set of EVERY ◯-free formula by structural recursion.  Everything here
is arithmetic; the derivation side is stages 4–5.
-/

open PLLFormula

namespace PLLND
namespace RNEmbed

open SemUI

/-- Codes for the up-sets of the ladder. -/
inductive UpCode : Type
  | bot | odd (a : Nat) | even (a : Nat) | top
  deriving Repr, DecidableEq

namespace UpCode

/-- Membership, as linear arithmetic. -/
def memC : UpCode → Nat → Prop
  | bot, _ => False
  | odd a, w => w ≤ a
  | even a, w => w + 1 ≤ a ∨ w = a + 1
  | top, _ => True

/-- `[0, a−1]` as a code (`⊥` when `a = 0`). -/
def predOdd (a : Nat) : UpCode := if a = 0 then bot else odd (a - 1)

/-- Meet. -/
def meetC : UpCode → UpCode → UpCode
  | bot, bot => bot
  | bot, odd _ => bot
  | bot, even _ => bot
  | bot, top => bot
  | odd _, bot => bot
  | even _, bot => bot
  | top, bot => bot
  | top, top => top
  | top, odd b => odd b
  | top, even b => even b
  | odd a, top => odd a
  | even a, top => even a
  | odd a, odd b => odd (min a b)
  | odd a, even b => if a < b then odd a else if b < a then even b else predOdd b
  | even a, odd b => if b < a then odd b else if a < b then even a else predOdd a
  | even a, even b =>
      if a = b then even a
      else if a + 2 ≤ b then even a
      else if b + 2 ≤ a then even b
      else if a < b then predOdd a else predOdd b

/-- Join. -/
def joinC : UpCode → UpCode → UpCode
  | top, bot => top
  | top, odd _ => top
  | top, even _ => top
  | top, top => top
  | bot, top => top
  | odd _, top => top
  | even _, top => top
  | bot, bot => bot
  | bot, odd b => odd b
  | bot, even b => even b
  | odd a, bot => odd a
  | even a, bot => even a
  | odd a, odd b => odd (max a b)
  | odd a, even b => if b < a then odd a else if a < b then even b else odd (b + 1)
  | even a, odd b => if a < b then odd b else if b < a then even a else odd (a + 1)
  | even a, even b =>
      if a = b then even a
      else if a + 2 ≤ b then even b
      else if b + 2 ≤ a then even a
      else if a < b then odd (a + 2) else odd (b + 2)

/-- Implication (Heyting, on ladder up-sets). -/
def impC : UpCode → UpCode → UpCode
  | bot, bot => top
  | bot, odd _ => top
  | bot, even _ => top
  | bot, top => top
  | odd _, top => top
  | even _, top => top
  | top, top => top
  | top, bot => bot
  | top, odd b => odd b
  | top, even b => even b
  | odd a, bot => if a = 0 then even 0 else bot
  | even a, bot => if a = 0 then even 1 else if a = 1 then even 0 else bot
  | odd a, odd b =>
      if a ≤ b then top else if a = b + 1 then even (b + 1) else odd b
  | odd a, even b => if a + 1 ≤ b then top else even b
  | even a, odd b =>
      if a + 1 ≤ b then top
      else if a ≤ b + 1 then even (a + 1)
      else if b + 2 = a then even (a - 1)
      else odd b
  | even a, even b => if a = b ∨ a + 2 ≤ b then top else even b

/-! ## Pointwise correctness -/

theorem memC_meet (c d : UpCode) (w : Nat) :
    memC (meetC c d) w ↔ (memC c w ∧ memC d w) := by
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [meetC, memC, predOdd] <;>
    (try split_ifs) <;>
    (try simp only [memC]) <;>
    (first | omega | (simp only [iff_false, not_and, not_or]; intro _; omega)
           | (simp; omega) | simp)

theorem memC_join (c d : UpCode) (w : Nat) :
    memC (joinC c d) w ↔ (memC c w ∨ memC d w) := by
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [joinC, memC, predOdd] <;>
    (try split_ifs) <;>
    (try simp only [memC]) <;>
    (first | omega | (simp only [iff_false, not_and, not_or]; intro _; omega)
           | (simp; omega) | simp)

theorem memC_imp (c d : UpCode) (w : Nat) :
    memC (impC c d) w ↔ (∀ y, ladder.le w y → (memC c y → memC d y)) := by
  have hchar :
      (∀ y, ladder.le w y → (memC c y → memC d y)) ↔
        ((memC c w → memC d w) ∧
         ∀ t, t + 2 ≤ w → (memC c t → memC d t)) := by
    constructor
    · intro h
      exact ⟨h w (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩
    · rintro ⟨h0, h2⟩ y hy
      rcases (hy : y = w ∨ y + 2 ≤ w) with rfl | hy2
      · exact h0
      · exact h2 y hy2
  rw [hchar]
  rcases c with _ | a | a | _ <;> rcases d with _ | b | b | _ <;>
    simp only [impC]
  -- c = bot: implication is ⊤, antecedent absurd
  case bot.bot | bot.odd | bot.even | bot.top =>
    simp only [memC]
    exact ⟨fun _ => ⟨fun hc => hc.elim, fun _ _ hc => hc.elim⟩, fun _ => trivial⟩
  -- d = top: implication is ⊤, consequent trivial
  case odd.top | even.top | top.top =>
    simp only [memC]
    exact ⟨fun _ => ⟨fun _ => trivial, fun _ _ _ => trivial⟩, fun _ => trivial⟩
  -- c = top: implication is d itself
  case top.bot =>
    simp only [memC]
    exact ⟨fun hw => hw.elim, fun h => h.1 trivial⟩
  case top.odd =>
    simp only [memC]
    exact ⟨fun hw => ⟨fun _ => hw, fun t ht _ => by omega⟩, fun h => h.1 trivial⟩
  case top.even =>
    simp only [memC]
    exact ⟨fun hw => ⟨fun _ => hw, fun t ht _ => by omega⟩, fun h => h.1 trivial⟩
  -- negations
  case odd.bot =>
    split_ifs with h1 <;> simp only [memC]
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        by_cases hw0 : w ≤ a
        · exact (h0 hw0).elim
        · by_cases ht : 0 + 2 ≤ w
          · exact (h2 0 ht (by omega)).elim
          · omega
    · constructor
      · intro hw
        exact hw.elim
      · rintro ⟨h0, h2⟩
        by_cases hw0 : w ≤ a
        · exact (h0 hw0).elim
        · by_cases ht : 0 + 2 ≤ w
          · exact (h2 0 ht (by omega)).elim
          · omega
  case even.bot =>
    split_ifs with h1 h2 <;> simp only [memC]
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        by_cases hw0 : w + 1 ≤ a ∨ w = a + 1
        · exact (h0 hw0).elim
        · by_cases ht : 1 + 2 ≤ w
          · exact (h2 1 ht (by omega)).elim
          · omega
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        by_cases hw0 : w + 1 ≤ a ∨ w = a + 1
        · exact (h0 hw0).elim
        · by_cases ht : 0 + 2 ≤ w
          · exact (h2 0 ht (by omega)).elim
          · omega
    · constructor
      · intro hw
        exact hw.elim
      · rintro ⟨h0, h2⟩
        by_cases hw0 : w + 1 ≤ a ∨ w = a + 1
        · exact (h0 hw0).elim
        · by_cases ht : 0 + 2 ≤ w
          · exact (h2 0 ht (by omega)).elim
          · omega
  -- odd ⊃ odd
  case odd.odd =>
    split_ifs with h1 h2 <;> simp only [memC]
    · exact ⟨fun _ => ⟨fun hc => by omega, fun t ht hc => by omega⟩,
             fun _ => trivial⟩
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e1 := h2 (b + 1)
        omega
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e1 := h2 (b + 1)
        omega
  -- odd ⊃ even
  case odd.even =>
    split_ifs with h1 <;> simp only [memC]
    · exact ⟨fun _ => ⟨fun hc => by omega, fun t ht hc => by omega⟩,
             fun _ => trivial⟩
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e0 := h2 b
        omega
  -- even ⊃ odd
  case even.odd =>
    split_ifs with h1 h2 h3 <;> simp only [memC]
    · exact ⟨fun _ => ⟨fun hc => by omega, fun t ht hc => by omega⟩,
             fun _ => trivial⟩
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e1 := h2 (a + 1)
        omega
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e1 := h2 (b + 1)
        omega
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e1 := h2 (b + 1)
        have e2 := h2 (b + 2)
        omega
  -- even ⊃ even
  case even.even =>
    split_ifs with h1 <;> simp only [memC]
    · exact ⟨fun _ => ⟨fun hc => by omega, fun t ht hc => by omega⟩,
             fun _ => trivial⟩
    · constructor
      · intro hw
        exact ⟨fun hc => by omega, fun t ht hc => by omega⟩
      · rintro ⟨h0, h2⟩
        have e0 := h2 b
        omega

end UpCode

open UpCode

/-! ## Stage 3: the classifier and its semantic correctness -/

/-- The classification map: the code of a ◯-free formula's ladder
truth set, by structural recursion over the tables.  (`◯` is sent to
junk; every use is `boxFree`-guarded.  Atoms other than `p` are false
everywhere on the skeleton, hence `bot` — no variable hypothesis is
needed on this, the semantic, side.) -/
def cls : PLLFormula → UpCode
  | .prop a => if a = pv then .odd 0 else .bot
  | .falsePLL => .bot
  | .and A B => meetC (cls A) (cls B)
  | .or A B => joinC (cls A) (cls B)
  | .ifThen A B => impC (cls A) (cls B)
  | .somehow _ => .bot

/-- **Stage 3: the ladder truth set of every ◯-free formula is its
code's set.** -/
theorem sat_cls : ∀ {A : PLLFormula}, boxFree A = true →
    ∀ w : Nat, (ladder.sat A w ↔ memC (cls A) w) := by
  intro A
  induction A with
  | prop a =>
      intro _ w
      by_cases ha : a = pv
      · subst ha
        show (pv = pv ∧ w ∈ ladder.U) ↔ memC (cls (.prop pv)) w
        have e : cls (.prop pv) = .odd 0 := by simp [cls]
        rw [e, ladder_U]
        show (pv = pv ∧ w = 0) ↔ w ≤ 0
        constructor
        · rintro ⟨-, h⟩; omega
        · intro h; exact ⟨rfl, by omega⟩
      · show (a = pv ∧ w ∈ ladder.U) ↔ memC (cls (.prop a)) w
        have e : cls (.prop a) = .bot := by simp [cls, ha]
        rw [e]
        exact ⟨fun h => absurd h.1 ha, False.elim⟩
  | falsePLL =>
      intro _ w
      exact Iff.rfl
  | and A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (ladder.sat A w ∧ ladder.sat B w) ↔ memC (cls (A.and B)) w
      rw [show cls (A.and B) = meetC (cls A) (cls B) from rfl, memC_meet]
      exact and_congr (ihA h.1 w) (ihB h.2 w)
  | or A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (ladder.sat A w ∨ ladder.sat B w) ↔ memC (cls (A.or B)) w
      rw [show cls (A.or B) = joinC (cls A) (cls B) from rfl, memC_join]
      exact or_congr (ihA h.1 w) (ihB h.2 w)
  | ifThen A B ihA ihB =>
      intro h w
      simp only [boxFree, Bool.and_eq_true] at h
      show (∀ y, ladder.le w y → ladder.sat A y → ladder.sat B y) ↔
        memC (cls (A.ifThen B)) w
      rw [show cls (A.ifThen B) = impC (cls A) (cls B) from rfl, memC_imp]
      exact forall_congr' fun y => imp_congr Iff.rfl
        (imp_congr (ihA h.1 y) (ihB h.2 y))
  | somehow A ih =>
      intro h w
      simp only [boxFree] at h
      exact Bool.noConfusion h

/-! ## Axiom audits — sorry-free throughout -/

/-- info: 'PLLND.RNEmbed.UpCode.memC_imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms UpCode.memC_imp

/-- info: 'PLLND.RNEmbed.sat_cls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sat_cls

end RNEmbed
end PLLND
