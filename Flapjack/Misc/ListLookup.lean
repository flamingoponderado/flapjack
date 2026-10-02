import Flapjack.HolRef
import Init.Data.List.Nat.TakeDrop

namespace Flapjack.Misc

/-- Original list-first optional indexing overload. The source uses `oEL n xs`,
whose two clauses are re-exported by `LLOOKUP_def`; native optional indexing
has the same zero-based clauses and returns none outside the list.
This does not give a value to total HOL EL outside its domain. -/
@[hol "cakeml/misc/miscScript.sml" "LLOOKUP"]
def llookup {α : Type} (xs : List α) (n : Nat) : Option α := xs[n]?

/-- Both complete re-exported optional-index equations, with arbitrary index
and payload. Natural subtraction is retained in the nonzero cons clause. -/
@[hol "cakeml/misc/miscScript.sml" "LLOOKUP_def"]
theorem llookupDef {α : Type} :
    (∀ n, llookup ([] : List α) n = none) ∧
    (∀ n (x : α) xs, llookup (x :: xs) n =
      if n = 0 then some x else llookup xs (n - 1)) := by
  constructor
  · intro n; rfl
  · intro n x xs
    exact List.getElem?_cons

/-- Full original DROP offset equation, including empty/out-of-range inputs. -/
@[hol "cakeml/misc/miscScript.sml" "LLOOKUP_DROP"]
theorem llookupDrop {α : Type} (n m : Nat) (xs : List α) :
    llookup (xs.drop m) n = llookup xs (m + n) :=
  List.getElem?_drop

/-- Full original TAKE implication; successful lookup is the source premise. -/
@[hol "cakeml/misc/miscScript.sml" "LLOOKUP_TAKE_IMP"]
theorem llookupTakeImp {α : Type} (n m : Nat) (xs : List α) (x : α) :
    llookup (xs.take m) n = some x → llookup xs n = some x := by
  unfold llookup
  rw [List.getElem?_take]
  split
  · exact id
  · intro h; contradiction

/-- Full original update/index case split. Native List.set implements LUPDATE:
updates at an out-of-range index preserve the list and lookup returns none
when that same index is observed. No update or observation bounds are assumed. -/
@[hol "cakeml/misc/miscScript.sml" "LLOOKUP_LUPDATE"]
theorem llookupLupdate {α : Type} (xs : List α) (i n : Nat) (x : α) :
    llookup (xs.set i x) n =
      if i ≠ n then llookup xs n else
        if i < xs.length then some x else none := by
  unfold llookup
  rw [List.getElem?_set]
  by_cases h : i = n <;> simp [h]

/-- Flapjack-only definitional compatibility with existing native consumers.
There is no extra HOL declaration for exposing this alias to Lean notation. -/
theorem llookupEqNative {α : Type} (xs : List α) (n : Nat) :
    llookup xs n = xs[n]? := rfl

end Flapjack.Misc
