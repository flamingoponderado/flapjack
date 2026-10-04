import Flapjack.Pancake.WordConvs.EveryVarInstMono

namespace Flapjack.Test.WordConvsEveryVarInstMonoParity
open Flapjack
private def small (x : Nat) : Bool := decide (x < 5)
private def large (x : Nat) : Bool := decide (x < 9)
private theorem weaken {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width))
    (h : everyVarInstHOL small instruction = true) :
    everyVarInstHOL large instruction = true :=
  everyVarInstMono small instruction large
    ⟨by intro x hx; simp only [small, large, decide_eq_true_eq] at *; omega, h⟩

-- Original im_skip=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.skip : WordLangInst (BitVec 1)) = true :=
  weaken _ (by decide +kernel)
-- Original im_const=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.const 4 123 : WordLangInst (BitVec 80)) = true :=
  weaken _ (by decide +kernel)
-- Original im_binreg=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.arith (.binop .add 1 2 (.reg 4)) : WordLangInst (BitVec 8)) = true :=
  weaken _ (by decide +kernel)
-- Original im_binimm=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.arith (.binop .add 1 2 (.imm 99)) : WordLangInst (BitVec 8)) = true :=
  weaken _ (by decide +kernel)
-- Original im_shift=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.arith (.shift .lsl 1 2 (.reg 4)) : WordLangInst (BitVec 32)) = true :=
  weaken _ (by decide +kernel)
-- Original im_div=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.arith (.div 1 2 3) : WordLangInst (BitVec 8)) = true :=
  weaken _ (by decide +kernel)
-- Original im_longdiv=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.arith (.longDiv 0 1 2 3 4) : WordLangInst (BitVec 80)) = true :=
  weaken _ (by decide +kernel)
-- Original im_load8=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.mem .load8 1 (.addr 2 99) : WordLangInst (BitVec 64)) = true :=
  weaken _ (by decide +kernel)
-- Original im_load16_ignored=(T,T); source predicate checked internally.
example : everyVarInstHOL large (.mem .load16 99 (.addr 98 0) : WordLangInst (BitVec 1)) = true :=
  weaken _ (by decide +kernel)
-- Original im_fpless=(T,T); source predicate checked internally.
#print axioms everyVarInstMono

def runChecks : IO Bool := do
  IO.println "PASS original instruction predicate monotonicity (14 kernel applications and non-64 guard)"
  return true
end Flapjack.Test.WordConvsEveryVarInstMonoParity
