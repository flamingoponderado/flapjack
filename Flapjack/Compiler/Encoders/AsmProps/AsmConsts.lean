import Flapjack.Compiler.Encoders.AsmSem.Step
import Flapjack.Compiler.Encoders.AsmProps.ArithmeticPreservation
import Flapjack.Compiler.Encoders.AsmProps.FpPreservation
import Flapjack.Compiler.Encoders.AsmProps.Memory

/-! Original whole-assembly-step field preservation and new-PC independence
(asmPropsScript.sml:325-408). The statements keep every original field
conjunct over the native positive-width state; they inherit the IEEE real
rendering of fpUpd through asmUpd (reals_as_rational_cuts, SOUNDNESS item 8). -/
namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

/-- Field preservation of the generic load wrapper; Flapjack infrastructure
for the tagged `asm_consts`, which HOL proves by unfolding `mem_op_def`. -/
theorem memLoad_consts {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) :
    (memLoad n r a s).be = s.be ∧ (memLoad n r a s).lr = s.lr ∧
    (memLoad n r a s).align = s.align ∧ (memLoad n r a s).memDomain = s.memDomain := by
  have h := sndReadMemWordConsts (resultWidth := width) n
    (if s.be then addrHOL a s + BitVec.ofNat width (n - 1) else addrHOL a s) s
  simp only [memLoad]
  generalize readMemWord (resultWidth := width)
    (if s.be then addrHOL a s + BitVec.ofNat width (n - 1) else addrHOL a s) n s = p at h
  obtain ⟨w, s'⟩ := p
  simpa [updReg] using h

/-- Field preservation of the generic store wrapper; Flapjack infrastructure
for the tagged `asm_consts`. -/
theorem memStore_consts {width : Nat} [NeZero width] (n r : Nat) (a : HolAddr width)
    (s : AsmState width) :
    (memStore n r a s).be = s.be ∧ (memStore n r a s).lr = s.lr ∧
    (memStore n r a s).align = s.align ∧ (memStore n r a s).memDomain = s.memDomain := by
  have h := writeMemWordConsts (valueWidth := width) n
    (if s.be then addrHOL a s + BitVec.ofNat width (n - 1) else addrHOL a s) (readReg r s) s
  simpa [memStore] using h

/-- Field preservation of every memory operation; Flapjack infrastructure for
the tagged `asm_consts`. -/
theorem memOp_consts {width : Nat} [NeZero width] (m : HolMemop) (r : Nat)
    (a : HolAddr width) (s : AsmState width) :
    (memOp m r a s).be = s.be ∧ (memOp m r a s).lr = s.lr ∧
    (memOp m r a s).align = s.align ∧ (memOp m r a s).memDomain = s.memDomain := by
  cases m <;> first | exact memLoad_consts _ _ _ _ | exact memStore_consts _ _ _ _

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asm_consts"
  (words_as_type_indexed_bitvec)]
theorem asm_consts {width : Nat} [NeZero width] (i : HolAsm width) (w : BitVec width)
    (s : AsmState width) :
    (asmUpd i w s).be = s.be ∧ (asmUpd i w s).lr = s.lr ∧
    (asmUpd i w s).align = s.align ∧ (asmUpd i w s).memDomain = s.memDomain := by
  cases i with
  | inst i =>
    cases i with
    | skip => exact ⟨rfl, rfl, rfl, rfl⟩
    | const r imm => exact ⟨rfl, rfl, rfl, rfl⟩
    | arith x =>
      have h := arithUpd_consts x s
      exact ⟨h.2.2.2.2, h.2.2.2.1, h.2.1, h.1⟩
    | mem m r a => exact memOp_consts m r a s
    | fp fp =>
      have h := fpUpd_consts fp s
      exact ⟨h.2.2.2.2, h.2.2.2.1, h.2.1, h.1⟩
  | jump l => exact ⟨rfl, rfl, rfl, rfl⟩
  | jumpCmp cmp r ri l =>
    simp only [asmUpd]
    split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  | call l => exact ⟨rfl, rfl, rfl, rfl⟩
  | jumpReg r => exact ⟨rfl, rfl, rfl, rfl⟩
  | loc r l => exact ⟨rfl, rfl, rfl, rfl⟩

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asm_failed_ignore_new_pc"
  (words_as_type_indexed_bitvec)]
theorem asm_failed_ignore_new_pc {width : Nat} [NeZero width] (i : HolAsm width)
    (v w : BitVec width) (s : AsmState width) :
    (asmUpd i w s).failed = (asmUpd i v s).failed := by
  cases i <;> simp only [asmUpd] <;> (try split) <;> rfl

@[hol "cakeml/compiler/encoders/asm/asmPropsScript.sml" "asm_mem_ignore_new_pc"
  (words_as_type_indexed_bitvec)]
theorem asm_mem_ignore_new_pc {width : Nat} [NeZero width] (i : HolAsm width)
    (v w : BitVec width) (s : AsmState width) :
    (asmUpd i w s).mem = (asmUpd i v s).mem := by
  cases i <;> simp only [asmUpd] <;> (try split) <;> rfl

end Flapjack.Compiler.Encoders.AsmProps
