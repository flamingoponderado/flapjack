import Flapjack.Compiler.Backend.RegAlloc.StatePartition

namespace Flapjack.Test.RegAllocStatePartitionParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of fresh original predicate/state/accumulator observations.
These finite rows do not prove general cross-prover equivalence or executed
allocator routing. Failure rows observe returned state and absence of tail effects. -/
-- sp_empty=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [] [90] [80,81] 42 = (.success ([90],[80,81]),42) := by decide +kernel
-- sp_singleton_true=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [2] [90] [80] 5 = (.success ([2,90],[80]),52) := by decide +kernel
-- sp_singleton_false=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [3] [90] [80] 5 = (.success ([90],[3,80]),53) := by decide +kernel
-- sp_all_true=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [2,4,6] [] [] 0 = (.success ([6,4,2],[]),246) := by decide +kernel
-- sp_all_false=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [1,3,5] [] [] 0 = (.success ([],[5,3,1]),135) := by decide +kernel
-- sp_mixed=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [1,2,3,4] [90,91] [80] 0 = (.success ([4,2,90,91],[3,1,80]),1234) := by decide +kernel
-- sp_reverse=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [4,3,2,1] [] [] 0 = (.success ([2,4],[1,3]),4321) := by decide +kernel
-- sp_duplicates=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [2,2,3] [2] [3] 0 = (.success ([2,2,2],[3,3]),223) := by decide +kernel
-- sp_large=T
example : stExPartition (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) [18446744073709551616,3] [] [] 0 = (.success ([18446744073709551616],[3]),184467440737095516163) := by decide +kernel
-- sp_fail_empty=T
example : stExPartition (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Bool Nat),s+7) else (.success (decide (x%2=0)),s+x)) [] [90] [80] 5 = (.success ([90],[80]),5) := by decide +kernel
-- sp_fail_first=T
example : stExPartition (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Bool Nat),s+7) else (.success (decide (x%2=0)),s+x)) [0,2,3] [90] [80] 5 = (.failure 17,12) := by decide +kernel
-- sp_fail_middle=T
example : stExPartition (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Bool Nat),s+7) else (.success (decide (x%2=0)),s+x)) [2,0,3] [90] [80] 5 = (.failure 17,14) := by decide +kernel
-- sp_fail_last=T
example : stExPartition (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Bool Nat),s+7) else (.success (decide (x%2=0)),s+x)) [2,3,0] [90] [80] 5 = (.failure 17,17) := by decide +kernel
-- sp_fail_duplicate=T
example : stExPartition (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Bool Nat),s+7) else (.success (decide (x%2=0)),s+x)) [2,2,0,9] [90] [80] 5 = (.failure 17,16) := by decide +kernel
-- sp_state_predicate=T
example : stExPartition (fun (_x : Nat) (s : Nat) => ((.success (decide (s%2=0)) : Exc Bool Bool),s+1)) [10,20,30,40] [] [] 0 = (.success ([30,10],[40,20]),4) := by decide +kernel
-- sp_state_failure=T
example : stExPartition (fun (x : Nat) (s : Nat) => if s>=10 then ((.failure s : Exc Bool Nat),s+100) else (.success (decide (x%2=0)),s+x)) [2,3,5,7] [] [] 0 = (.failure 10,110) := by decide +kernel
-- sp_bool_value=T
example : stExPartition (fun (x : Bool) (s : Nat) => ((.success (!x) : Exc Bool Bool),s+1)) [true,false,true,false] [true] [false] 5 = (.success ([false,false,true],[true,true,false]),9) := by decide +kernel
-- sp_bool_state=T
example : stExPartition (fun (_x : Nat) (s : Bool) => ((.success s : Exc Bool Nat),!s)) [2,3,5] [] [] true = (.success ([5,2],[3]),false) := by decide +kernel
-- sp_list_state=T
example : stExPartition (fun (x : Nat) (s : List Nat) => ((.success (decide (x%2=0)) : Exc Bool (List Nat)),s++[x])) [2,3,5] [] [] [99] = (.success ([2],[5,3]),[99,2,3,5]) := by decide +kernel
-- sp_list_error=T
example : stExPartition (fun (x : Nat) (s : List Nat) => if x=0 then ((.failure [7,11] : Exc Bool (List Nat)),s++[x]) else (.success (decide (x%2=0)),s++[x])) [2,0,5] [] [] [99] = (.failure [7,11],[99,2,0]) := by decide +kernel
-- sp_tuple_state=T
example : stExPartition (fun (x : Bool) (s : Nat × Bool) => ((.success (x && s.2) : Exc Bool Bool),(s.1+2,!s.2))) [true,false,true] [] [] (5,true) = (.success ([true,true],[false]),(11,false)) := by decide +kernel
-- sp_empty_always_failure=T
example : stExPartition (fun (x : Bool) (s : Nat) => ((.failure x : Exc Bool Bool),s+100)) [] [true] [false] 7 = (.success ([true],[false]),7) := by decide +kernel

example {σ α ε : Type} (p : α → M σ Bool ε) (yes no : List α) (s : σ) :
    stExPartition p [] yes no s = (.success (yes,no),s) := rfl

end Flapjack.Test.RegAllocStatePartitionParity
