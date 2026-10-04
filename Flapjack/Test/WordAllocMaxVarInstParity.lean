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
end Flapjack.Test.WordAllocMaxVarInstParity
