import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterFlip
namespace Flapjack.Test.SSARegisterFlipParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
def observe (next : Nat) : Bool × Bool × Bool × Bool :=
  (isAllocVar next, isStackVar next, isAllocVar (next+2), isStackVar (next+2))
example : observe 0 = (false,false,false,false) := by decide +kernel
example : isStackVar (0+2) = isAllocVar 0 ∧ isAllocVar (0+2) = isStackVar 0 := flipRw 0
example : observe 1 = (true,false,false,true) := by decide +kernel
example : isStackVar (1+2) = isAllocVar 1 ∧ isAllocVar (1+2) = isStackVar 1 := flipRw 1
example : observe 2 = (false,false,false,false) := by decide +kernel
example : isStackVar (2+2) = isAllocVar 2 ∧ isAllocVar (2+2) = isStackVar 2 := flipRw 2
example : observe 3 = (false,true,true,false) := by decide +kernel
example : isStackVar (3+2) = isAllocVar 3 ∧ isAllocVar (3+2) = isStackVar 3 := flipRw 3
example : observe 5 = (true,false,false,true) := by decide +kernel
example : isStackVar (5+2) = isAllocVar 5 ∧ isAllocVar (5+2) = isStackVar 5 := flipRw 5
example : observe 7 = (false,true,true,false) := by decide +kernel
example : isStackVar (7+2) = isAllocVar 7 ∧ isAllocVar (7+2) = isStackVar 7 := flipRw 7
example : observe 1000000000000000000000000000001 = (true,false,false,true) := by decide +kernel
example : isStackVar (1000000000000000000000000000001+2) = isAllocVar 1000000000000000000000000000001 ∧ isAllocVar (1000000000000000000000000000001+2) = isStackVar 1000000000000000000000000000001 := flipRw 1000000000000000000000000000001
example : observe 1000000000000000000000000000003 = (false,true,true,false) := by decide +kernel
example : isStackVar (1000000000000000000000000000003+2) = isAllocVar 1000000000000000000000000000003 ∧ isAllocVar (1000000000000000000000000000003+2) = isStackVar 1000000000000000000000000000003 := flipRw 1000000000000000000000000000003
example : isStackVar (1+2) := isAllocVarFlip 1 (by decide)
example : isStackVar (5+2) := isAllocVarFlip 5 (by decide)
example : isStackVar (1000000000000000000000000000001+2) := isAllocVarFlip 1000000000000000000000000000001 (by decide)
example : isAllocVar (3+2) := isStackVarFlip 3 (by decide)
example : isAllocVar (7+2) := isStackVarFlip 7 (by decide)
example : isAllocVar (1000000000000000000000000000003+2) := isStackVarFlip 1000000000000000000000000000003 (by decide)
end Flapjack.Test.SSARegisterFlipParity
