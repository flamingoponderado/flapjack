import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSARegisterClass
namespace Flapjack.Test.SSARegisterClassParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Identical inputs/results as the direct original predicate probe.
private def observe (n : Nat) :=
  (isAllocVar n,isAllocVar (n+4),isStackVar n,isStackVar (n+4))
example : observe 1 = (true,true,false,false) := by decide +kernel
example : observe 3 = (false,false,true,true) := by decide +kernel
example : observe 0 = (false,false,false,false) := by decide +kernel
example : observe 2 = (false,false,false,false) := by decide +kernel
example : observe 5 = (true,true,false,false) := by decide +kernel
example : observe 7 = (false,false,true,true) := by decide +kernel
example : observe 1000000000000000000000000000001 = (true,true,false,false) := by decide +kernel
example : observe 1000000000000000000000000000003 = (false,false,true,true) := by decide +kernel
example : isAllocVar (1+4) := isAllocVarAdd 1 (by decide +kernel)
example : isAllocVar (5+4) := isAllocVarAdd 5 (by decide +kernel)
example : isAllocVar (1000000000000000000000000000001+4) := isAllocVarAdd 1000000000000000000000000000001 (by decide +kernel)
example : isStackVar (3+4) := isStackVarAdd 3 (by decide +kernel)
example : isStackVar (7+4) := isStackVarAdd 7 (by decide +kernel)
example : isStackVar (1000000000000000000000000000003+4) := isStackVarAdd 1000000000000000000000000000003 (by decide +kernel)
end Flapjack.Test.SSARegisterClassParity
