import Flapjack.Compiler.Encoders.AsmProps.Assertions
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.List.Range
import Lean.Elab.Tactic.Omega

/-! Full generic original ASM assertion iteration and weakening theorems. -/
namespace Flapjack.Compiler.Encoders.AsmProps

/-- Local notation for HOL's FOLDR over reversed GENLIST; infrastructure,
not a separately claimed HOL declaration. -/
private def trajectory {α : Type} (n k : Nat) (next : Nat → α → α) (s : α) : α :=
  (((List.range (k + 1)).map (n - ·)).reverse).foldr next s

private theorem trajectory_zero {α : Type} (n : Nat) (next : Nat → α → α) (s : α) :
    trajectory n 0 next s = next n s := by simp [trajectory]

private theorem trajectory_succ {α : Type} (n k : Nat) (next : Nat → α → α) (s : α) :
    trajectory (n + 1) (k + 1) next s = trajectory n k next (next (n + 1) s) := by
  unfold trajectory
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, Nat.sub_zero, List.map_map, List.reverse_cons, List.foldr_append,
    List.foldr_cons, List.foldr_nil]
  congr 2
  apply congrArg (fun f => List.map f (List.range (k + 1)))
  funext i
  simp only [Function.comp_apply]
  omega

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts_IMP_FOLDR_COUNT_LIST"]
theorem asserts_foldr_countList {α : Type} (n : Nat) (next : Nat → α → α)
    (s : α) (P Q : α → Prop) :
    asserts n next s P Q → Q ((List.range n).foldr next (next n s)) := by
  induction n generalizing s with
  | zero => simp [asserts]
  | succ n ih =>
    intro h
    simpa [List.range_succ] using ih (next (n + 1) s) h.2

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts_IMP_FOLDR_COUNT_LIST_LESS"]
theorem asserts_foldr_countList_less {α : Type} (k n : Nat) (next : Nat → α → α)
    (s : α) (P Q : α → Prop) :
    asserts n next s P Q ∧ k < n →
      P ((((List.range (k + 1)).map (n - ·)).reverse).foldr next s) := by
  change asserts n next s P Q ∧ k < n → P (trajectory n k next s)
  induction n generalizing k s with
  | zero => rintro ⟨_, h⟩; omega
  | succ n ih =>
    rintro ⟨h, hk⟩
    cases k with
    | zero => simpa [trajectory_zero] using h.1
    | succ k =>
      rw [trajectory_succ]
      exact ih k (next (n + 1) s) ⟨h.2, by omega⟩

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts_WEAKEN"]
theorem asserts_weaken {α : Type} (n : Nat) (next next' : Nat → α → α)
    (s : α) (P P' Q : α → Prop) :
    (∀ k, k ≤ n → next k = next' k ∧
      (P ((((List.range (k + 1)).map (n - ·)).reverse).foldr next s) →
       P' ((((List.range (k + 1)).map (n - ·)).reverse).foldr next s))) →
    asserts n next s P Q → asserts n next' s P' Q := by
  change (∀ k, k ≤ n → next k = next' k ∧
    (P (trajectory n k next s) → P' (trajectory n k next s))) → _
  induction n generalizing s with
  | zero =>
    intro h ha
    simpa [asserts, ← (h 0 (by omega)).1] using ha
  | succ n ih =>
    intro h ha
    have he := (h (n + 1) (by omega)).1
    change P' (next' (n + 1) s) ∧ asserts n next' (next' (n + 1) s) P' Q
    rw [← he]
    constructor
    · have hp := (h 0 (by omega)).2
      simp only [trajectory_zero] at hp
      exact hp ha.1
    · apply ih (next (n + 1) s) _ ha.2
      intro k hk
      constructor
      · exact (h k (by omega)).1
      · simpa only [trajectory_succ] using (h (k + 1) (by omega)).2

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts2_change_interfer"]
theorem asserts2_changeInterfer {α β : Type} (n : Nat) (fi fi2 : Nat → β → α)
    (fc : α → β) (s : α) (P : α → β → Prop) :
    asserts2 n fi fc s P ∧ (∀ k, k ≤ n → fi k = fi2 k) → asserts2 n fi2 fc s P := by
  induction n generalizing s with
  | zero => simp [asserts2]
  | succ n ih =>
    rintro ⟨h, he⟩
    constructor
    · exact h.1
    · rw [← he (n + 1) (by omega)]
      exact ih _ ⟨h.2, fun k hk => he k (by omega)⟩

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts2_first"]
theorem asserts2_first {α β : Type} (n : Nat) (fi : Nat → β → α) (fc : α → β)
    (s : α) (P : α → β → Prop) :
    1 ≤ n ∧ asserts2 n fi fc s P → P s (fc s) := by
  cases n with
  | zero => rintro ⟨h, _⟩; omega
  | succ n => exact fun h => h.2.1

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asserts2_every"]
theorem asserts2_every {α β : Type} (n : Nat) (s : α) (j : Nat)
    (f : β → α) (g : α → β) (P : α → β → Prop) :
    asserts2 n (fun _ => f) g s P ∧ j < n →
      P ((f ∘ g)^[j] s) (g ((f ∘ g)^[j] s)) := by
  induction n generalizing j s with
  | zero => rintro ⟨_, h⟩; omega
  | succ n ih =>
    rintro ⟨h, hj⟩
    cases j with
    | zero => simpa using h.1
    | succ j =>
      simpa [Function.iterate_succ_apply] using ih (f (g s)) j ⟨h.2, by omega⟩

end Flapjack.Compiler.Encoders.AsmProps
