import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Comparison
import Flapjack.RiscV.CorrectnessEncoding.DecodeBinop
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Encoding

/-! Byte-driven scratch-prefix steps for the full JumpCmp case. These local
compositions have no separately named HOL declaration and remain untagged. -/
namespace Flapjack.RiscV.TargetProof.JumpCmp
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.Asm Compiler.Encoders.AsmSem

theorem next_encoded_andi (ms : riscv_state) (rd rs : BitVec 5) (imm : BitVec 12)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithI (.ANDI (rd,rs,imm)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms &&& imm.signExtend 64)) := by
  have lowbits : (Encode (.ArithI (.ANDI (rd,rs,imm)))).getLsbD 0 = true ∧
      (Encode (.ArithI (.ANDI (rd,rs,imm)))).getLsbD 1 = true := by
    simp only [Encode, Itype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithI (.ANDI (rd,rs,imm))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms &&& imm.signExtend 64,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'ANDI», GPR, gpr]
  exact write_next ms (.ArithI (.ANDI (rd,rs,imm))) (Encode (.ArithI (.ANDI (rd,rs,imm)))) rd (GPR rs ms &&& imm.signExtend 64)
    rn ok (decode_encode_andi _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

theorem next_encoded_and (ms : riscv_state) (rd rs rt : BitVec 5)
    (rn : rd ≠ 0#5) (ok : riscvOk ms = true)
    (bytes : encodedInstructionBytes ms (.ArithR (.AND (rd,rs,rt)))) :
    NextRISCV ms = some (writePost ms rd (GPR rs ms &&& GPR rt ms)) := by
  have lowbits : (Encode (.ArithR (.AND (rd,rs,rt)))).getLsbD 0 = true ∧
      (Encode (.ArithR (.AND (rd,rs,rt)))).getLsbD 1 = true := by
    simp only [Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]
    simp
  have run : Run (.ArithR (.AND (rd,rs,rt))) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
      «write'GPR» (GPR rs ms &&& GPR rt ms,rd) {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
    simp [Run, «dfn'AND», GPR, gpr]
  exact write_next ms (.ArithR (.AND (rd,rs,rt))) (Encode (.ArithR (.AND (rd,rs,rt)))) rd (GPR rs ms &&& GPR rt ms)
    rn ok (decode_encode_and _ _ _) run lowbits.1 lowbits.2 bytes.1 bytes.2.1
    bytes.2.2.1 bytes.2.2.2

/-- Full native projection preserves scratch 31 even though the source
register relation intentionally hides it. This is local composition infrastructure. -/
theorem scratch_after_interference (ms : riscv_state) (value : BitVec 64)
    (domain : BitVec 64 → Prop) (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj domain)) :
    GPR (31#5) (env 0 (writePost ms (31#5) value)) = value := by
  have projection := interference 0 (writePost ms (31#5) value)
  have gprs := congrArg (fun p : RiscVProjection => p.2.2.2.2.1) projection
  simpa [riscvTarget, riscvProj, GPR, gpr, writePost, holUpdate] using
    congrFun gprs (31#5)

/-- Scratch 31 is excluded by the original target register relation, so a
finished branch relates to the unchanged source registers. No separately named
HOL lemma exists for this local relation composition. -/
theorem hide_scratch (s : AsmState 64) (value dest : BitVec 64)
    (ms : riscv_state)
    (rel : targetStateRel riscvTarget (updPc dest (updReg 31 value s)) ms) :
    targetStateRel riscvTarget (updPc dest s) ms := by
  refine ⟨rel.1, rel.2.1, rel.2.2.1, ?_, rel.2.2.2.2⟩
  intro i hi
  have ne : i ≠ 31 := by
    intro e
    subst i
    norm_num [riscvTarget, riscvConfig] at hi
  simpa [updPc, updReg, ne] using rel.2.2.2.1 i hi

/-- Source registers used by JumpCmp survive the scratch prefix. -/
theorem read_after_scratch (r : Nat) (value pc : BitVec 64) (s : AsmState 64)
    (guard : asmRegOkExact r riscvConfig = true) :
    readReg r (updPc pc (updReg 31 value s)) = readReg r s := by
  have ne : r ≠ 31 := by
    intro e
    subst r
    norm_num [asmRegOkExact, riscvConfig] at guard
  simp [readReg, updPc, updReg, ne]

/-- The executed scratch write supplies the source relation after arbitrary
allowed interference; this is used to fetch the subsequent branch bytes. -/
theorem scratch_interference_rel (s : AsmState 64) (ms : riscv_state)
    (value : BitVec 64) (env : Nat → riscv_state → riscv_state)
    (rel : targetStateRel riscvTarget s ms)
    (interference : interferenceOk env (riscvTarget.proj s.memDomain)) :
    targetStateRel riscvTarget
      (updPc (s.pc + 4) (updReg 31 value s))
      (env 0 (writePost ms (31#5) value)) := by
  have midrel := write_post_rel s ms 31 value (by decide) rel
  exact (riscv_target_ok.2
    (env 0 (writePost ms (31#5) value)) (writePost ms (31#5) value)
    (updPc (s.pc + 4) (updReg 31 value s))
    (interference 0 (writePost ms (31#5) value))).1.mpr midrel

/-- Actual immediate prefix execution for all eight original comparisons. -/
theorem immediate_prefix_next (c : Cmp) (r : BitVec 5) (i : BitVec 64)
    (ms : riscv_state) (ok : riscvOk ms = true)
    (bounds : -2048 ≤ i.toInt ∧ i.toInt ≤ 2047)
    (bytes : encodedInstructionBytes ms (immediate_prefix c r (i.setWidth 12))) :
    NextRISCV ms = some (writePost ms (31#5)
      (if c = .test ∨ c = .notTest then GPR r ms &&& i else i)) := by
  have reconstruct := immediate_reconstruct i bounds
  have zero : GPR (0#5) ms = 0#64 := rfl
  cases c
  case equal =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case less =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case lower =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case test =>
    simpa [immediate_prefix, reconstruct] using
      next_encoded_andi ms (31#5) r (i.setWidth 12) (by decide) ok bytes
  case notEqual =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case notLess =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case notLower =>
    simpa [immediate_prefix, reconstruct, zero] using
      next_encoded_ori ms (31#5) (0#5) (i.setWidth 12) (by decide) ok bytes
  case notTest =>
    simpa [immediate_prefix, reconstruct] using
      next_encoded_andi ms (31#5) r (i.setWidth 12) (by decide) ok bytes

/-- Byte-driven immediate branch after its real prefix. The scratch and
operand facts are supplied by the prefix relation and full projection. -/
theorem immediate_branch_next (c : Cmp) (r : BitVec 5) (left i : BitVec 64)
    (off : BitVec 12) (ms : riscv_state) (ok : riscvOk ms = true)
    (read : GPR r ms = left)
    (scratch : GPR (31#5) ms =
      if c = .test ∨ c = .notTest then left &&& i else i)
    (bytes : encodedInstructionBytes ms (immediate_branch c r off)) :
    NextRISCV ms = some (Jump.branchPost ms
      (if wordCmpHOL c left i then
        ms.c_PC ms.procID + (off.signExtend 64 <<< (1 : Nat)) else
        ms.c_PC ms.procID + 4)) := by
  cases c
  case equal =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .equal r (31#5) off ms ok (by simp) bytes
  case less =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .less r (31#5) off ms ok (by simp) bytes
  case lower =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .lower r (31#5) off ms ok (by simp) bytes
  case test =>
    exact test_branch_next .test left i off ms ok (by simp)
      (by simpa using scratch) bytes
  case notEqual =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .notEqual r (31#5) off ms ok (by simp) bytes
  case notLess =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .notLess r (31#5) off ms ok (by simp) bytes
  case notLower =>
    have value : GPR (31#5) ms = i := by simpa using scratch
    simpa only [read, value] using
      simple_branch_next .notLower r (31#5) off ms ok (by simp) bytes
  case notTest =>
    exact test_branch_next .notTest left i off ms ok (by simp)
      (by simpa using scratch) bytes

/-- Final source relation after a scratch prefix and branch, including both
original interference points. Instruction execution is established separately
from bytes; this local composition does not assume a target final relation. -/
theorem scratch_branch_final_rel (s : AsmState 64) (ms : riscv_state)
    (value dest : BitVec 64) (env : Nat → riscv_state → riscv_state)
    (rel : targetStateRel riscvTarget s ms)
    (aligned : holAligned 2 dest = true)
    (interference : interferenceOk env (riscvTarget.proj s.memDomain)) :
    targetStateRel riscvTarget (updPc dest s)
      (env 1 (Jump.branchPost (env 0 (writePost ms (31#5) value)) dest)) := by
  have midrel := scratch_interference_rel s ms value env rel interference
  have post := Jump.branch_post_rel
    (updPc (s.pc + 4) (updReg 31 value s))
    (env 0 (writePost ms (31#5) value)) dest midrel aligned
  have hidden : targetStateRel riscvTarget (updPc dest s)
      (Jump.branchPost (env 0 (writePost ms (31#5) value)) dest) := by
    apply hide_scratch s value dest
    simpa [updPc] using post
  exact (riscv_target_ok.2
    (env 1 (Jump.branchPost (env 0 (writePost ms (31#5) value)) dest))
    (Jump.branchPost (env 0 (writePost ms (31#5) value)) dest)
    (updPc dest s)
    (interference 1 (Jump.branchPost (env 0 (writePost ms (31#5) value)) dest))).1.mpr hidden

/-- Fetch bytes derived from the original source memory assertion. -/
theorem instruction_bytes (s : AsmState 64) (ms : riscv_state) (i : instruction)
    (rel : targetStateRel riscvTarget s ms)
    (bytes : bytesInMemoryHOL s.pc (riscvEncode i) s.mem s.memDomain) :
    encodedInstructionBytes ms i := by
  have native := bytes_in_memory_thm () s ms _ _ _ _ ⟨rel, bytes⟩
  exact ⟨native.2.2.2.2.2.1, native.2.2.2.2.2.2.1,
    native.2.2.2.2.2.2.2.1, native.2.2.2.2.2.2.2.2.1⟩

/-- Both fetches in the actual prefix/branch sequence, including arbitrary
interference between the instructions. -/
theorem scratch_sequence_bytes (s : AsmState 64) (ms : riscv_state)
    (value : BitVec 64) (first second : instruction)
    (env : Nat → riscv_state → riscv_state)
    (rel : targetStateRel riscvTarget s ms)
    (interference : interferenceOk env (riscvTarget.proj s.memDomain))
    (bytes : bytesInMemoryHOL s.pc
      (riscvEncode first ++ riscvEncode second) s.mem s.memDomain) :
    encodedInstructionBytes ms first ∧
    encodedInstructionBytes (env 0 (writePost ms (31#5) value)) second := by
  rw [bytesInMemory_append] at bytes
  refine ⟨instruction_bytes s ms first rel bytes.1, ?_⟩
  have midrel := scratch_interference_rel s ms value env rel interference
  apply instruction_bytes (updPc (s.pc + 4) (updReg 31 value s)) _ second midrel
  simpa [riscvEncode, updPc, updReg] using bytes.2

end Flapjack.RiscV.TargetProof.JumpCmp
