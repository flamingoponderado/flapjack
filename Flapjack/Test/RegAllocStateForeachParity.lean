import Flapjack.Compiler.Backend.RegAlloc.StateForeach

namespace Flapjack.Test.RegAllocStateForeachParity
open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

-- sf_empty=T
example : stExForeach [] (fun (x : Nat) (s : Nat) => ((.success (x+1) : Exc Nat Nat),s*10+x)) 42 = (.success (),42) := by decide +kernel

-- sf_order=T
example : stExForeach [1,2,3] (fun (x : Nat) (s : Nat) => ((.success (x+1) : Exc Nat Nat),s*10+x)) 0 = (.success (),123) := by decide +kernel

-- sf_reverse=T
example : stExForeach [3,2,1] (fun (x : Nat) (s : Nat) => ((.success (x+1) : Exc Nat Nat),s*10+x)) 0 = (.success (),321) := by decide +kernel

-- sf_duplicates=T
example : stExForeach [2,2,3] (fun (x : Nat) (s : Nat) => ((.success (x+1) : Exc Nat Nat),s*10+x)) 0 = (.success (),223) := by decide +kernel

-- sf_fail_empty=T
example : stExForeach [] (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success (x+1),s+x)) 5 = (.success (),5) := by decide +kernel

-- sf_fail_first=T
example : stExForeach [0,2,3] (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success (x+1),s+x)) 5 = (.failure 17,12) := by decide +kernel

-- sf_fail_middle=T
example : stExForeach [2,0,3] (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success (x+1),s+x)) 5 = (.failure 17,14) := by decide +kernel

-- sf_fail_last=T
example : stExForeach [2,3,0] (fun (x : Nat) (s : Nat) => if x=0 then ((.failure 17 : Exc Nat Nat),s+7) else (.success (x+1),s+x)) 5 = (.failure 17,17) := by decide +kernel

-- sf_bool_result=T
example : stExForeach [1,2,3] (fun (x : Nat) (s : Nat) => ((.success (decide (x%2=0)) : Exc Bool Nat),s*10+x)) 0 = (.success (),123) := by decide +kernel

-- sf_list_state=T
example : stExForeach [2,3,5] (fun (x : Nat) (s : List Nat) => ((.success (x+1) : Exc Nat Nat),s++[x])) [99] = (.success (),[99,2,3,5]) := by decide +kernel

-- sf_bool_state=T
example : stExForeach [2,3,5] (fun (x : Nat) (s : Bool) => ((.success x : Exc Nat Nat),!s)) true = (.success (),false) := by decide +kernel

example {σ α β ε : Type} (a : α → M σ β ε) (s : σ) :
    stExForeach [] a s = (.success (),s) := rfl
end Flapjack.Test.RegAllocStateForeachParity
