import Flapjack.Compiler.Backend.WordAlloc.Proofs.MaxVarInst
namespace Flapjack.Test.WordAllocMaxVarInstParity
open Flapjack.Compiler.Backend.WordAlloc
-- Original mi_skip
example : maxVarInstHOL (.skip : WordLangInst (BitVec 64)) = 0 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.skip : WordLangInst (BitVec 64))))
      (.skip : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_const
example : maxVarInstHOL (.const (2^80) 3 : WordLangInst (BitVec 64)) = 1208925819614629174706176 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.const (2^80) 3 : WordLangInst (BitVec 64))))
      (.const (2^80) 3 : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_binreg
example : maxVarInstHOL (.arith (.binop .add 2 9 (.reg 7)) : WordLangInst (BitVec 64)) = 9 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.arith (.binop .add 2 9 (.reg 7)) : WordLangInst (BitVec 64))))
      (.arith (.binop .add 2 9 (.reg 7)) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_binimm
example : maxVarInstHOL (.arith (.binop .add 2 9 (.imm 999)) : WordLangInst (BitVec 64)) = 9 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.arith (.binop .add 2 9 (.imm 999)) : WordLangInst (BitVec 64))))
      (.arith (.binop .add 2 9 (.imm 999)) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_shift
example : maxVarInstHOL (.arith (.shift .lsl 11 9 (.reg 17)) : WordLangInst (BitVec 64)) = 17 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.arith (.shift .lsl 11 9 (.reg 17)) : WordLangInst (BitVec 64))))
      (.arith (.shift .lsl 11 9 (.reg 17)) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_div
example : maxVarInstHOL (.arith (.div 9 21 7) : WordLangInst (BitVec 64)) = 21 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.arith (.div 9 21 7) : WordLangInst (BitVec 64))))
      (.arith (.div 9 21 7) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_longdiv
example : maxVarInstHOL (.arith (.longDiv 1 2 3 4 99) : WordLangInst (BitVec 64)) = 99 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.arith (.longDiv 1 2 3 4 99) : WordLangInst (BitVec 64))))
      (.arith (.longDiv 1 2 3 4 99) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_load8
example : maxVarInstHOL (.mem .load8 2 (.addr 80 7) : WordLangInst (BitVec 64)) = 80 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.mem .load8 2 (.addr 80 7) : WordLangInst (BitVec 64))))
      (.mem .load8 2 (.addr 80 7) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_fp64_to
example : maxVarInstHOL (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 64)) = 2 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 64))))
      (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_fp32_to
example : maxVarInstHOL (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 32)) = 99 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 32))))
      (.fp (.fpMovToReg 2 99 100) : WordLangInst (BitVec 32)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_fp80_from
example : maxVarInstHOL (.fp (.fpMovFromReg 100 2 99) : WordLangInst (BitVec 80)) = 99 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.fp (.fpMovFromReg 100 2 99) : WordLangInst (BitVec 80))))
      (.fp (.fpMovFromReg 100 2 99) : WordLangInst (BitVec 80)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
-- Original mi_fpignored
example : maxVarInstHOL (.fp (.fpAdd 100 200 300) : WordLangInst (BitVec 64)) = 0 ∧
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL (.fp (.fpAdd 100 200 300) : WordLangInst (BitVec 64))))
      (.fp (.fpAdd 100 200 300) : WordLangInst (BitVec 64)) = true := by
  exact ⟨by decide, maxVarInstMax _⟩
end Flapjack.Test.WordAllocMaxVarInstParity
