import Flapjack.HolRef
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Nat.Modify
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original nested-drop law, including its addition order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_DROP_EQ"]
theorem dropDropEq {α : Type} (n m : Nat) (xs : List α) :
    (xs.drop n).drop m = xs.drop (m + n) := by
  simp [List.drop_drop, Nat.add_comm]

/-- Full original nested-take law; both bounds remain arbitrary. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_TAKE_MIN"]
theorem takeTakeMin {α : Type} (xs : List α) (m n : Nat) :
    (xs.take m).take n = xs.take (min m n) := by
  simp [List.take_take, Nat.min_comm]

/-- Full original take/drop transport with no length bound. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_DROP_EQ"]
theorem takeDropEq {α : Type} (xs : List α) (n m : Nat) :
    (xs.drop n).take m = (xs.take (m + n)).drop n := by
  rw [List.drop_take]
  simp

/-- Full original empty suffix of a prefix. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_TAKE_NIL"]
theorem dropTakeNil {α : Type} (n : Nat) (xs : List α) :
    (xs.take n).drop n = [] := List.drop_take_self

/-- Full original single-write prefix transport. List.set, like HOL LUPDATE,
ignores out-of-range writes; no successful-write premise is needed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "TAKE_LUPDATE"]
theorem takeLupdate {α : Type} (xs : List α) (n : Nat) (x : α) (i : Nat) :
    (xs.set i x).take n = (xs.take n).set i x := List.take_set

/-- Full original single-write suffix transport under exactly the source guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE_lemma1"]
theorem dropLupdateGe {α : Type} (xs : List α) (n m : Nat) (h : α)
    (hnm : n ≤ m) :
    (xs.set m h).drop n = (xs.drop n).set (m - n) h := by
  rw [List.drop_set, if_neg (by omega)]

/-- Full original suffix preservation when the write precedes the suffix. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE_lemma2"]
theorem dropLupdateLt {α : Type} (xs : List α) (n m : Nat) (h : α)
    (hmn : m < n) :
    (xs.set m h).drop n = xs.drop n := List.drop_set_of_lt hmn

/-- Full original conditional single-write suffix law, including ignored writes. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_LUPDATE"]
theorem dropLupdate {α : Type} (n : Nat) (h : α) (m : Nat) (xs : List α) :
    (xs.set m h).drop n =
      if m < n then xs.drop n else (xs.drop n).set (m - n) h := List.drop_set

/-- Full original natural-number minimum translation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MIN_ADD"]
theorem minAdd (m1 m2 n : Nat) :
    min m1 m2 + n = min (m1 + n) (m2 + n) := by omega

end Flapjack.Compiler.Backend.WordToStack
