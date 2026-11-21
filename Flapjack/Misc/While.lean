module

public import Flapjack.HolRef
public import Mathlib.Data.Nat.Find
public import Mathlib.Logic.Function.Iterate

@[expose] public section

/-! HOL's `WHILE` loop, introduced by specification. -/
namespace Flapjack

open Classical in
/-- Existence of a function satisfying the `WHILE` equation (Flapjack
infrastructure, mirroring HOL's `ITERATION`). -/
theorem holWhileExists {α : Type} (P : α → Prop) (g : α → α) :
    ∃ W : α → α, ∀ x, W x = if P x then W (g x) else x := by
  classical
  refine ⟨fun x => if h : ∃ n, ¬ P (g^[n] x) then g^[Nat.find h] x
    else Classical.choice ⟨x⟩, fun x => ?_⟩
  dsimp only
  by_cases px : P x
  · rw [if_pos px]
    by_cases h : ∃ n, ¬ P (g^[n] x)
    · have h' : ∃ n, ¬ P (g^[n] (g x)) := by
        obtain ⟨n, hn⟩ := h
        cases n with
        | zero => exact absurd px hn
        | succ n => exact ⟨n, by simpa [Function.iterate_succ_apply] using hn⟩
      rw [dif_pos h, dif_pos h']
      have hfind : Nat.find h = Nat.find h' + 1 := by
        apply le_antisymm
        · apply Nat.find_min'
          simpa [Function.iterate_succ_apply] using Nat.find_spec h'
        · have spec := Nat.find_spec h
          have pos : Nat.find h ≠ 0 := by
            intro z; rw [z] at spec; exact spec px
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero pos
          rw [hk]
          apply Nat.succ_le_succ
          apply Nat.find_min'
          rw [hk] at spec
          simpa [Function.iterate_succ_apply] using spec
      rw [hfind, Function.iterate_succ_apply]
    · have h' : ¬ ∃ n, ¬ P (g^[n] (g x)) := by
        rintro ⟨n, hn⟩
        exact h ⟨n + 1, by simpa [Function.iterate_succ_apply] using hn⟩
      rw [dif_neg h, dif_neg h']
  · rw [if_neg px, dif_pos ⟨0, px⟩]
    have : Nat.find (⟨0, px⟩ : ∃ n, ¬ P (g^[n] x)) = 0 :=
      Nat.eq_zero_of_le_zero (Nat.find_min' _ px)
    rw [this]
    rfl

open Classical in
/-- HOL's `WHILE`: some function satisfying the loop-unfolding equation for
every input. As in HOL, the result on a nonterminating input is otherwise
unspecified. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "WHILE"]
noncomputable def holWhile {α : Type} (P : α → Prop) (g : α → α) : α → α :=
  Classical.choose (holWhileExists P g)

open Classical in
/-- The specification of `holWhile` (Flapjack proof infrastructure; the
statement of the HOL specification theorem `WHILE`). -/
theorem holWhile_spec {α : Type} (P : α → Prop) (g : α → α) (x : α) :
    holWhile P g x = if P x then holWhile P g (g x) else x := by
  unfold holWhile
  exact Classical.choose_spec (holWhileExists P g) x

end Flapjack
