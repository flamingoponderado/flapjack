import Flapjack.Compiler.Encoders.AsmSem.MemOps
import Flapjack.Misc.BytesInMemory

/-!
# asmSem instruction and assembly transitions

Ports of `inst_def`, `jump_to_offset_def`, `asm_def` and `asm_step_def`
(`asmSemScript.sml:225-258`) over the reviewed `upd_reg`, `arith_upd`, `mem_op`, `fp_upd`,
`upd_pc`, `read_reg`, `reg_imm`, `assert`, `word_cmp`, `aligned`, `bytes_in_memory`, `asm_ok`
and `asm_config` ports. HOL `~s2.failed` is `¬ s2.failed`, `asm_ok i c` is `asmOkExact i c`,
and the `link_reg` case's `T` is `True`.
-/

namespace Flapjack.Compiler.Encoders.AsmSem
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `inst_def` (`asmSemScript.sml:225-231`): the five instruction clauses. -/
noncomputable def instUpd {width : Nat} [NeZero width] :
    HolInst width → AsmState width → AsmState width
  | .skip, s => s
  | .const r imm, s => updReg r imm s
  | .arith x, s => arithUpd x s
  | .mem m r a, s => memOp m r a s
/-- Exact HOL `jump_to_offset_def` (`asmSemScript.sml:233-235`). -/
def jumpToOffset {width : Nat} [NeZero width] (w : BitVec width) (s : AsmState width) :
    AsmState width :=
  updPc (s.pc + w) s

/-- Exact HOL `asm_def` (`asmSemScript.sml:237-248`): the six assembly clauses. -/
noncomputable def asmUpd {width : Nat} [NeZero width] :
    HolAsm width → BitVec width → AsmState width → AsmState width
  | .inst i, pc, s => updPc pc (instUpd i s)
  | .jump l, _, s => jumpToOffset l s
  | .jumpCmp cmp r ri l, pc, s =>
      if wordCmpHOL cmp (readReg r s) (regImm ri s) then jumpToOffset l s else updPc pc s
  | .call l, pc, s => jumpToOffset l (updReg s.lr pc s)
  | .jumpReg r, _, s =>
      let a := readReg r s
      updPc a (assertState (holAligned s.align a) s)
  | .loc r l, pc, s => updPc pc (updReg r (s.pc + l) s)

/-- Exact HOL `asm_step_def` (`asmSemScript.sml:250-258`): the seven conjuncts in order. -/
noncomputable def asmStep {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (s1 : AsmState width) (i : HolAsm width) (s2 : AsmState width) : Prop :=
  bytesInMemoryHOL s1.pc (c.encode i) s1.mem s1.memDomain ∧
    (match c.linkReg with
     | some r => s1.lr = r
     | none => True) ∧
    s1.be = c.bigEndian ∧
    s1.align = c.codeAlignment ∧
    asmUpd i (s1.pc + BitVec.ofNat width (c.encode i).length) s1 = s2 ∧
    ¬ s2.failed ∧
    asmOkExact i c = true

end Flapjack.Compiler.Encoders.AsmSem
