import Flapjack.HolRef
import Mathlib.Data.Nat.Find

/-! HOL's optional least natural satisfying a predicate. -/
namespace Flapjack

/-- Return the least witness when one exists, and none otherwise. HOL's
`LEAST` is rendered by `Nat.find` under the existence guard: the least witness
is unique by HOL's `LEAST_EXISTS_IMP` and Lean's `Nat.find_spec` and
`Nat.find_min`. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_def"]
noncomputable def holOLeast (p : Nat → Prop) : Option Nat := by
  classical
  exact if h : ∃ n, p n then some (Nat.find h) else none

/-- Reason by the empty case and by an arbitrary least witness. -/
@[hol "HOL/src/num/theories/WhileScript.sml" "OLEAST_INTRO"]
theorem holOLeast_intro (p : Nat → Prop) (q : Option Nat → Prop)
    (premises : ((∀ n, ¬ p n) → q none) ∧
      (∀ n, p n ∧ (∀ m, m < n → ¬ p m) → q (some n))) :
    q (holOLeast p) := by
  classical
  unfold holOLeast
  split
  · rename_i h
    exact premises.2 (Nat.find h) ⟨Nat.find_spec h, fun m less => Nat.find_min h less⟩
  · rename_i h
    apply premises.1
    intro n hn
    exact h ⟨n, hn⟩

end Flapjack
