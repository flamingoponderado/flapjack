import Flapjack.Compiler.Encoders.RiscV.Target
import Lean.Elab.Tactic.Omega

/-! Full original native encoder length and nonempty contracts. No validity,
accepted-opcode, successful execution, or assembly subset premise is added. -/
namespace Flapjack.RiscV.TargetProof
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target RiscV.L3

theorem length_riscv_encode (i : instruction) : (riscvEncode i).length = 4 := by
  rfl

theorem riscv_encode_not_nil (i : instruction) : riscvEncode i ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_riscv_encode] at this
  contradiction

/-- Flapjack structural infrastructure: full native AST never produces an
empty list, including the original fail encoding for unsupported ASM forms. -/
private theorem ast_nonempty (i : HolAsm 64) : riscvAst i ≠ [] := by
  fun_cases riscvAst i <;> simp_all [riscvConst32, riscvEncodeFail]
  all_goals split <;> simp_all

/-- Flapjack list-fold length infrastructure over every native instruction;
no separately claimed original theorem. -/
private theorem encodeList_length (l : List instruction) :
    (l.flatMap riscvEncode).length = 4 * l.length := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.flatMap_cons, List.length_append, length_riscv_encode,
      ih, List.length_cons]
    omega

/-- Flapjack full list-fold length equation used by offset-length proofs. -/
theorem riscvEnc_length_eq (i : HolAsm 64) :
    (riscvEnc i).length = 4 * (riscvAst i).length :=
  encodeList_length _

theorem riscv_encoding (i : HolAsm 64) :
    (riscvEnc i).length % 4 = 0 ∧ riscvEnc i ≠ [] := by
  constructor
  · rw [riscvEnc, encodeList_length]
    omega
  · intro h
    have hl : 0 < (riscvAst i).length := List.length_pos_iff.mpr (ast_nonempty i)
    have he := congrArg List.length h
    simp only [riscvEnc, encodeList_length, List.length_nil] at he
    omega

end Flapjack.RiscV.TargetProof
