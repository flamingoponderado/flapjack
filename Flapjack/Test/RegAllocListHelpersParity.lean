import Flapjack.Compiler.Backend.RegAlloc.StateFilter
import Flapjack.Compiler.Backend.RegAlloc.SortedInsert
import Flapjack.RiscV.CakeRegAlloc

namespace Flapjack.Test.RegAllocListHelpersParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase Flapjack.RiscV.CakeRegAlloc
/-! Same-input kernel replay of fresh original `st_ex_FILTER` and
`sorted_insert` EVAL results (`scripts/hol-probes/reg_alloc_list_helpers_probe.out`),
covering accumulator order, state threading, state-dependent predicates, every
failure position, independent carriers, large naturals and unsorted inputs.
Finite observations do not establish general cross-prover equivalence. -/

-- fi_empty=(M_success [8; 9],7)
example : stExFilter (fun (_ : Nat) (s : Nat) => ((.failure 9 : Exc Bool Nat), s+100)) [] [8, 9] 7 = (.success [8, 9], 7) := by decide +kernel
-- fi_mixed=(M_success [4; 2; 90],1234)
example : stExFilter (fun (x : Nat) (s : Nat) => ((.success (decide (x % 2 = 0)) : Exc Bool Nat), s*10+x)) [1, 2, 3, 4] [90] 0 = (.success [4, 2, 90], 1234) := by decide +kernel
-- fi_all_true=(M_success [7; 6; 5],3)
example : stExFilter (fun (_ : Nat) (s : Nat) => ((.success true : Exc Bool Nat), s+1)) [5, 6, 7] [] 0 = (.success [7, 6, 5], 3) := by decide +kernel
-- fi_all_false=(M_success [1],3)
example : stExFilter (fun (_ : Nat) (s : Nat) => ((.success false : Exc Bool Nat), s+1)) [5, 6, 7] [1] 0 = (.success [1], 3) := by decide +kernel
-- fi_duplicates=(M_success [2; 2; 2; 2],7)
example : stExFilter (fun (x : Nat) (s : Nat) => ((.success (decide (x > 1)) : Exc Bool Nat), s+x)) [2, 2, 1, 2] [2] 0 = (.success [2, 2, 2, 2], 7) := by decide +kernel
-- fi_state_pred=(M_success [30; 10],4)
example : stExFilter (fun (_ : Nat) (s : Nat) => ((.success (decide (s % 2 = 0)) : Exc Bool Nat), s+1)) [10, 20, 30, 40] [] 0 = (.success [30, 10], 4) := by decide +kernel
-- fi_fail_first=(M_failure 17,12)
example : stExFilter (fun (x : Nat) (s : Nat) => if x = 0 then ((.failure 17 : Exc Bool Nat), s+7) else (.success (decide (x % 2 = 0)), s+x)) [0, 2, 3] [90] 5 = (.failure 17, 12) := by decide +kernel
-- fi_fail_middle=(M_failure 17,14)
example : stExFilter (fun (x : Nat) (s : Nat) => if x = 0 then ((.failure 17 : Exc Bool Nat), s+7) else (.success (decide (x % 2 = 0)), s+x)) [2, 0, 3] [90] 5 = (.failure 17, 14) := by decide +kernel
-- fi_fail_last=(M_failure 17,17)
example : stExFilter (fun (x : Nat) (s : Nat) => if x = 0 then ((.failure 17 : Exc Bool Nat), s+7) else (.success (decide (x % 2 = 0)), s+x)) [2, 3, 0] [90] 5 = (.failure 17, 17) := by decide +kernel
-- fi_bool_value=(M_success [F; F; T],9)
example : stExFilter (fun (x : Bool) (s : Nat) => ((.success (!x) : Exc Bool Bool), s+1)) [true, false, true, false] [true] 5 = (.success [false, false, true], 9) := by decide +kernel
-- fi_large=(M_success [18446744073709551616],2)
example : stExFilter (fun (x : Nat) (s : Nat) => ((.success (decide (x > 3)) : Exc Bool Nat), s+1)) [18446744073709551616, 3] [] 0 = (.success [18446744073709551616], 2) := by decide +kernel

-- si_empty=[6]
example : sortedInsert 6 [] [] = [6] := by decide +kernel
-- si_empty_acc=[8; 9; 6]
example : sortedInsert 6 [9, 8] [] = [8, 9, 6] := by decide +kernel
-- si_middle=[7; 5; 4; 2]
example : sortedInsert 5 [] [7, 4, 2] = [7, 5, 4, 2] := by decide +kernel
-- si_dup=[7; 4; 2]
example : sortedInsert 4 [] [7, 4, 2] = [7, 4, 2] := by decide +kernel
-- si_end=[7; 4; 2; 1]
example : sortedInsert 1 [] [7, 4, 2] = [7, 4, 2, 1] := by decide +kernel
-- si_front=[9; 7; 4; 2]
example : sortedInsert 9 [] [7, 4, 2] = [9, 7, 4, 2] := by decide +kernel
-- si_acc=[10; 12; 7; 5; 4; 2]
example : sortedInsert 5 [12, 10] [7, 4, 2] = [10, 12, 7, 5, 4, 2] := by decide +kernel
-- si_acc_dup=[10; 12; 7; 4; 2]
example : sortedInsert 7 [12, 10] [7, 4, 2] = [10, 12, 7, 4, 2] := by decide +kernel
-- si_unsorted=[5; 3; 9; 5]
example : sortedInsert 5 [] [3, 9, 5] = [5, 3, 9, 5] := by decide +kernel
-- si_unsorted_dup_later=[9; 3; 9; 5]
example : sortedInsert 9 [] [3, 9, 5] = [9, 3, 9, 5] := by decide +kernel
-- si_zero=[0]
example : sortedInsert 0 [] [0] = [0] := by decide +kernel
-- si_large=[18446744073709551617; 18446744073709551616; 2]
example : sortedInsert 18446744073709551616 [] [18446744073709551617, 2] = [18446744073709551617, 18446744073709551616, 2] := by decide +kernel

/-- The executed allocator's insertion is the reviewed definition, for every
key and list (sorted or not). -/
example (x : Nat) (ys : List Nat) : cakeSortedInsert x ys = sortedInsert x [] ys := rfl

end Flapjack.Test.RegAllocListHelpersParity
