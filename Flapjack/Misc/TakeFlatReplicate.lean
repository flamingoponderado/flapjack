import Flapjack.HolRef
import Mathlib.Data.List.Flatten
import Mathlib.Data.List.TakeDrop
namespace Flapjack.Misc

/-- Retains the original independent length binder and permits empty chunks. -/
@[hol "cakeml/misc/miscScript.sml" "TAKE_FLAT_REPLICATE_LEQ"]
theorem takeFlatReplicateLeq {α : Type} (j k : Nat) (ls : List α) (len : Nat) :
    len = ls.length ∧ k ≤ j →
      ((List.replicate j ls).flatten).take (k * len) = (List.replicate k ls).flatten := by
  rintro ⟨rfl, hkj⟩
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hk : k ≤ j := by omega
      have hr := ih j hk
      have ht : ls.take (k * ls.length + ls.length) = ls :=
        List.take_of_length_le (by omega)
      simpa [List.replicate_succ, List.flatten_cons, Nat.succ_mul,
        List.take_append, ht] using congrArg (List.append ls) hr
end Flapjack.Misc
