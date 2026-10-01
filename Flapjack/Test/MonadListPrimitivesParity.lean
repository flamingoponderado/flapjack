import Flapjack.Translator.Monadic.MonadBase.ListPrimitives

namespace Flapjack.Test.MonadListPrimitivesParity
open Flapjack.Translator.Monadic.MonadBase
/-! Same-input exact exception/list kernel replay of fresh original primitives.
Independent value/exception types, large indices and failure theorem instances
are covered. Finite observations do not establish cross-prover equivalence or
completion of state-array accessors or the executed allocator route. -/
-- lp_sub_empty=T
example : mSub false 0 ([] : List Nat) = .failure false := by decide +kernel
-- lp_sub_empty_bound=T
example : mSub false 0 ([] : List Nat) = .failure false := mSubExnEq ([] : List Nat) 0 false (by decide +kernel)
-- lp_sub_head=T
example : mSub false 0 ([2,3,5] : List Nat) = .success 2 := by decide +kernel
-- lp_sub_middle=T
example : mSub false 1 ([2,3,5] : List Nat) = .success 3 := by decide +kernel
-- lp_sub_last=T
example : mSub false 2 ([2,3,5] : List Nat) = .success 5 := by decide +kernel
-- lp_sub_length=T
example : mSub false 3 ([2,3,5] : List Nat) = .failure false := by decide +kernel
-- lp_sub_length_bound=T
example : mSub false 3 ([2,3,5] : List Nat) = .failure false := mSubExnEq ([2,3,5] : List Nat) 3 false (by decide +kernel)
-- lp_sub_large=T
example : mSub false 18446744073709551616 ([2,3,5] : List Nat) = .failure false := by decide +kernel
-- lp_sub_large_bound=T
example : mSub false 18446744073709551616 ([2,3,5] : List Nat) = .failure false := mSubExnEq ([2,3,5] : List Nat) 18446744073709551616 false (by decide +kernel)
-- lp_sub_duplicate=T
example : mSub false 1 ([2,2,5] : List Nat) = .success 2 := by decide +kernel
-- lp_update_empty=T
example : mUpdate false 7 0 ([] : List Nat) = .failure false := by decide +kernel
-- lp_update_empty_bound=T
example : mUpdate false 7 0 ([] : List Nat) = .failure false := mUpdateExnEq ([] : List Nat) 0 7 false (by decide +kernel)
-- lp_update_head=T
example : mUpdate false 7 0 ([2,3,5] : List Nat) = .success [7,3,5] := by decide +kernel
-- lp_update_middle=T
example : mUpdate false 7 1 ([2,3,5] : List Nat) = .success [2,7,5] := by decide +kernel
-- lp_update_last=T
example : mUpdate false 7 2 ([2,3,5] : List Nat) = .success [2,3,7] := by decide +kernel
-- lp_update_length=T
example : mUpdate false 7 3 ([2,3,5] : List Nat) = .failure false := by decide +kernel
-- lp_update_length_bound=T
example : mUpdate false 7 3 ([2,3,5] : List Nat) = .failure false := mUpdateExnEq ([2,3,5] : List Nat) 3 7 false (by decide +kernel)
-- lp_update_large=T
example : mUpdate false 7 18446744073709551616 ([2,3,5] : List Nat) = .failure false := by decide +kernel
-- lp_update_large_bound=T
example : mUpdate false 7 18446744073709551616 ([2,3,5] : List Nat) = .failure false := mUpdateExnEq ([2,3,5] : List Nat) 18446744073709551616 7 false (by decide +kernel)
-- lp_update_duplicate=T
example : mUpdate false 7 1 ([2,2,5] : List Nat) = .success [2,7,5] := by decide +kernel
-- lp_bool_sub=T
example : mSub 13 1 [true,false,true] = .success false := by decide +kernel
-- lp_bool_update=T
example : mUpdate 13 false 2 [true,false,true] = .success [true,false,false] := by decide +kernel
-- lp_bool_fail=T
example : mUpdate 13 false 3 [true,false,true] = .failure 13 := by decide +kernel
-- lp_tuple_error=T
example : mSub (false, (7 : Nat)) 2 [true] = .failure (false,7) := by decide +kernel
-- lp_tuple_value=T
example : mUpdate true ((11 : Nat),false) 1 [(2,true),(3,true)] = .success [(2,true),(11,false)] := by decide +kernel

example {α ε : Type} (values : List α) (index : Nat) (error : ε)
    (bounds : values.length ≤ index) : mSub error index values = .failure error :=
  mSubExnEq values index error bounds
example {α ε : Type} (values : List α) (index : Nat) (replacement : α) (error : ε)
    (bounds : values.length ≤ index) : mUpdate error replacement index values = .failure error :=
  mUpdateExnEq values index replacement error bounds
#print axioms mSubExnEq
#print axioms mUpdateExnEq

end Flapjack.Test.MonadListPrimitivesParity
