import Flapjack.Compiler.Backend.RegAlloc.StateMap

namespace Flapjack.Test.RegAllocStateMapParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase
/-! Same-input state/result kernel replay of fresh original st_ex_MAP.
Head-before-tail effects, every failure position, failure-returned state and
independent carrier types are covered. Finite observations do not establish
general cross-prover equivalence or production allocator routing. -/
-- sm_bool_state=T
example : stExMap (fun (x : Nat) (s : Bool) => ((.success (x+1) : Exc Nat Nat),!s)) [2,3] true = (.success [3,4],true) := by decide +kernel
-- sm_num_state=T
example : stExMap (fun (x : Bool) (s : Nat) => ((.success (!x) : Exc Bool Bool),s+1)) [true,false] 5 = (.success [false,true],7) := by decide +kernel
-- sm_empty=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [] 42 = (.success [],42) := by decide +kernel
-- sm_one=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [2] 5 = (.success [52],52) := by decide +kernel
-- sm_order=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [2, 3, 5] 0 = (.success [2, 23, 235],235) := by decide +kernel
-- sm_reverse=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [5, 3, 2] 0 = (.success [5, 53, 532],532) := by decide +kernel
-- sm_duplicates=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [2, 2, 3] 0 = (.success [2, 22, 223],223) := by decide +kernel
-- sm_large=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.success (s*10+x) : Exc Nat Bool),s*10+x)) [18446744073709551616, 3] 0 = (.success [18446744073709551616, 184467440737095516163],184467440737095516163) := by decide +kernel
-- sm_fail_empty=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [] 5 = (.success [],5) := by decide +kernel
-- sm_fail_first=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [0, 2, 3] 5 = (.failure 17,12) := by decide +kernel
-- sm_fail_middle=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [2, 0, 3] 5 = (.failure 17,14) := by decide +kernel
-- sm_fail_last=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [2, 3, 0] 5 = (.failure 17,17) := by decide +kernel
-- sm_fail_duplicates=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [2, 2, 0, 9] 5 = (.failure 17,16) := by decide +kernel
-- sm_success=T
example : stExMap (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success x,s+x)) [2, 3, 5] 5 = (.success [2, 3, 5],15) := by decide +kernel
-- sm_state_failure=T
example : stExMap (fun (x : Nat) (s : Nat) => if s>=10 then ((.failure s : Exc Bool Nat),s+100) else (.success (decide (x%2=0)),s+x)) [2,3,5,7] 0 = (.failure 10,110) := by decide +kernel
-- sm_list_state=T
example : stExMap (fun (x : Nat) (s : List Nat) => ((.success (decide (x%2=0)) : Exc Bool (List Nat)),s++[x])) [2,3,5] [99] = (.success [true,false,false],[99,2,3,5]) := by decide +kernel
-- sm_list_error=T
example : stExMap (fun (x : Nat) (s : List Nat) => if x=0 then ((.failure [7,11] : Exc Bool (List Nat)),s++[x]) else (.success (decide (x%2=0)),s++[x])) [2,0,5] [99] = (.failure [7,11],[99,2,0]) := by decide +kernel
-- sm_tuple_state=T
example : stExMap (fun (x : Bool) (s : Nat × Bool) => ((.success (if x then s.1 else s.1+1) : Exc Nat Bool),(s.1+2,!s.2))) [true,false,true] (5,false) = (.success [5,8,9],(11,true)) := by decide +kernel
-- sm_empty_failure_callback=T
example : stExMap (fun (x : Nat) (s : Nat) => ((.failure x : Exc Bool Nat),s+100)) [] 7 = (.success [],7) := by decide +kernel

example {σ α β ε : Type} (f : α → M σ β ε) (s : σ) :
    stExMap f [] s = (.success [],s) := rfl

end Flapjack.Test.RegAllocStateMapParity
