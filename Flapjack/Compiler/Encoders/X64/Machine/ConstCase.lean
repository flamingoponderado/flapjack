module

public import Flapjack.Compiler.Encoders.X64.Machine.JumpRegCase
public import Flapjack.Compiler.Encoders.X64.Machine.MemDecodeProof

@[expose] public section

/-!
# The `const` case of `encoder_correct x64Target`

`const r i` lowers to one of three instructions: `mov r, imm32` when `i` fits in
a nonnegative 31-bit range, `mov r, imm64` otherwise, and `xor r, r` when the
immediate is zero.  Each writes `i` to `r` (the 32-bit move zero-extends, and
the guard makes that the identity; the xor clears the register, matching
`i = 0`) and advances `PC` by the encoded length.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-- The instruction `const` lowers to, with `total_num2Zreg` already applied
(`r < 16` makes it the identity). -/
def x64ConstInsn (r : Nat) (i : BitVec 64) : X64Insn :=
  if i.toNat / 2 ^ 31 = 0 then
    (if i = 0 then .binopRR .zxor .z32 r r else .movRI .z32 r i)
  else
    (if i = 0 then .binopRR .zxor .z32 r r else .movRI .z64 r i)

/-- A 32-bit write of a value below `2 ^ 31` is the identity on 64-bit words. -/
theorem setWidth32_eq_of_toNat_lt (i : BitVec 64) (h : i.toNat < 2 ^ 31) :
    BitVec.setWidth 64 (BitVec.setWidth 32 i) = i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have hlt : i.toNat < 2 ^ 32 := by omega
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]

/-- `asm_ok` of a `const` is its register check. -/
theorem const_ok (r : Nat) (i : BitVec 64)
    (h : asmOkExact (.inst (.const r i)) x64Config = true) :
    asmRegOkExact r x64Config = true := by
  simpa [asmOkExact, asmInstOkExact, x64Config] using h

/-- The range side conditions of `decode_movRI_z32` follow from the lowering's
31-bit guard. -/
theorem const_mov32_range (i : BitVec 64) (h : i.toNat < 2 ^ 31) :
    -(2 ^ 31 : Int) ≤ i.toInt ∧ i.toInt < 2 ^ 31 := by
  have hcond : 2 * i.toNat < 2 ^ 64 := by omega
  rw [BitVec.toInt_eq_toNat_cond, if_pos hcond]
  constructor <;> omega

/-- A 32-bit immediate move is five or six bytes. -/
theorem movRI_z32_length (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (h1 : -(2 ^ 31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2 ^ 31) :
    (encodeInsn (.movRI .z32 dst imm)).length = 5 + (if 8 ≤ dst then 1 else 0) := by
  have hp : (-2147483648 : Int) ≤ imm.toInt ∧ imm.toInt ≤ 2147483647 := by
    constructor <;> omega
  interval_cases dst <;>
    simp [encodeInsn, eOpsizeImm, eOpsize, eImm32, rexPrefix, mkRex, hp]

/-- A 64-bit immediate move is ten bytes. -/
theorem movRI_z64_length (dst : Nat) (hd : dst < 16) (imm : BitVec 64) :
    (encodeInsn (.movRI .z64 dst imm)).length = 10 := by
  interval_cases dst <;>
    simp [encodeInsn, eOpsizeImm, eOpsize, eImm64, rexPrefix, mkRex]

/-- The 32-bit immediate move is nonempty. -/
theorem movRI_z32_ne (dst : Nat) (hd : dst < 16) (imm : BitVec 64)
    (h1 : -(2 ^ 31 : Int) ≤ imm.toInt) (h2 : imm.toInt < 2 ^ 31) :
    encodeInsn (.movRI .z32 dst imm) ≠ [] := by
  intro h
  have hpos : 0 < (encodeInsn (.movRI .z32 dst imm)).length := by
    rw [movRI_z32_length dst hd imm h1 h2]
    omega
  rw [h] at hpos
  simp at hpos

/-- The 64-bit immediate move is nonempty. -/
theorem movRI_z64_ne (dst : Nat) (hd : dst < 16) (imm : BitVec 64) :
    encodeInsn (.movRI .z64 dst imm) ≠ [] := by
  intro h
  have hpos : 0 < (encodeInsn (.movRI .z64 dst imm)).length := by
    rw [movRI_z64_length dst hd imm]; omega
  rw [h] at hpos
  simp at hpos

/-- The zeroing `xor` is nonempty. -/
theorem binopRR_z32_xor_ne (r : Nat) (hr : r < 16) :
    encodeInsn (.binopRR .zxor .z32 r r) ≠ [] := by
  intro h
  have hpos : 0 < (encodeInsn (.binopRR .zxor .z32 r r)).length := by
    interval_cases r <;> decide
  rw [h] at hpos
  simp at hpos

/-- A zero 32-bit write is a zero 64-bit write. -/
theorem setWidth64_setWidth32_zero :
    BitVec.setWidth 64 (BitVec.setWidth 32 (0#64)) = (0 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- One `x64Next` step over a 32-bit immediate move writes the immediate. -/
theorem x64Next_const_mov32 (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (i : BitVec 64)
    (hr : r < 16) (h1 : i.toNat < 2 ^ 31)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRI .z32 r i)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r i) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 r i)).length } := by
  obtain ⟨hlo, hhi⟩ := const_mov32_range i h1
  have hlen := movRI_z32_length r hr i hlo hhi
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRI .z32 r i, 5 + (if 8 ≤ r then 1 else 0)) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_movRI_z32 r hr i hlo hhi)
      (by rw [hlen])
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, writeRegSized,
    writeReg, setWidth32_eq_of_toNat_lt i h1]

/-- One `x64Next` step over a 64-bit immediate move writes the immediate. -/
theorem x64Next_const_mov64 (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (i : BitVec 64)
    (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRI .z64 r i)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r i) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z64 r i)).length } := by
  have hlen := movRI_z64_length r hr i
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRI .z64 r i, 10) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm (decode_movRI_z64 r hr i)
      (by rw [hlen])
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, writeRegSized,
    writeReg]

/-- One `x64Next` step over the zeroing `xor` clears the register. -/
theorem x64Next_const_zero (ms : X64State) (d : BitVec 64 → Prop) (r : Nat) (hr : r < 16)
    (hbm : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR .zxor .z32 r r)) ms.mem d)
    (hfailed : ms.failed = false) :
    x64Next ms = { (writeReg ms r 0) with
      flags := binopFlags .zxor (readReg ms r) (readReg ms r) ms.flags,
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.binopRR .zxor .z32 r r)).length } := by
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.binopRR .zxor .z32 r r, (encodeInsn (.binopRR .zxor .z32 r r)).length) :=
    decode_bytesInMemory _ ms.pc ms.mem d _ _ hbm
      (decode_binopRR_z32 .zxor r r hr hr (by decide)) (by omega)
  simp only [x64Next, hfailed, Bool.false_eq_true, if_false, hdec, execInsn, binopValue,
    BitVec.xor_self, writeRegSized, writeReg]
  rw [setWidth64_setWidth32_zero]

/-- The `const` encoding is the lowering's instruction. -/
theorem x64Enc_const (r : Nat) (hr : r < 16) (i : BitVec 64) :
    x64Target.config.encode (.inst (.const r i)) = encodeInsn (x64ConstInsn r i) := by
  have hdst : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hdiv : (i.toNat / 2 ^ 31 = 0) ↔ i.toNat < 2 ^ 31 := by
    rw [Nat.div_eq_zero_iff]
    simp
  have hflat : (x64Ast (.inst (.const r i))).flatMap encodeInsn =
      encodeInsn (x64ConstInsn r i) := by
    simp only [x64Ast, x64Inst, x64ConstInsn, hdst]
    by_cases h1 : i.toNat / 2 ^ 31 = 0
    · simp only [if_pos h1]
      by_cases h2 : i = 0
      · simp only [if_pos h2]; simp
      · simp only [if_neg h2]; simp
    · simp only [if_neg h1]
      by_cases h2 : i = 0
      · simp only [if_pos h2]; simp
      · simp only [if_neg h2]; simp
  have hne : encodeInsn (x64ConstInsn r i) ≠ [] := by
    by_cases h1 : i.toNat / 2 ^ 31 = 0
    · by_cases h2 : i = 0
      · simp only [x64ConstInsn, if_pos h1, if_pos h2]
        exact binopRR_z32_xor_ne r hr
      · obtain ⟨hlo, hhi⟩ := const_mov32_range i (hdiv.mp h1)
        simp only [x64ConstInsn, if_pos h1, if_neg h2]
        exact movRI_z32_ne r hr i hlo hhi
    · by_cases h2 : i = 0
      · simp only [x64ConstInsn, if_neg h1, if_pos h2]
        exact binopRR_z32_xor_ne r hr
      · simp only [x64ConstInsn, if_neg h1, if_neg h2]
        exact movRI_z64_ne r hr i
  exact x64Enc_of_flatMap (.inst (.const r i)) _ hflat hne

/-- Reading a written register. -/
theorem readReg_writeReg (ms : X64State) (r : Nat) (v : BitVec 64) (x : Nat)
    (hr : r < 16) (hx : x < 16) :
    readReg (writeReg ms r v) x = if x = r then v else readReg ms x := by
  simp only [readReg, writeReg, num2Zreg, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hx]

/-- The `const` constructor of `encoder_correct x64Target`: one `x64Next` step
from a state holding the immediate-move or zeroing bytes writes `i` to the
register and advances `PC` by the encoded length. -/
theorem case_const (r : Nat) (i : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.const r i)) s2 ∧ targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.const r i)) s1 s2 ms := by
  have st := x64Start (.inst (.const r i)) s1 s2 ms h
  have hok : asmOkExact (.inst (.const r i)) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  have hr : r < 16 := jumpReg_reg_lt r (const_ok r i hok)
  have hav : r ∉ x64Config.avoidRegs := jumpReg_reg_avoid r (const_ok r i hok)
  have hreg : r < x64Target.config.regCount ∧ x64Target.config.avoidRegs.contains r = false := by
    refine ⟨?_, ?_⟩
    · simpa [x64Target_config, x64Config] using hr
    · simpa [x64Target_config, x64Config] using hav
  have hdiv : (i.toNat / 2 ^ 31 = 0) ↔ i.toNat < 2 ^ 31 := by
    rw [Nat.div_eq_zero_iff]
    simp
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn (x64ConstInsn r i)).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [x64Enc_const r hr i]
  have hs2regs : ∀ x, s2.regs x = if x = r then i else s1.regs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, updReg]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, updReg]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, updReg]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, updReg]
  have hdom : s2.memDomain = s1.memDomain := hs2dom
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (x64ConstInsn r i)) ms.mem s1.memDomain := by
    rw [st.pc]
    have h' := st.bytesTarget
    rw [x64Enc_const r hr i] at h'
    exact h'
  have hcode : allPcs (x64Target.config.encode (.inst (.const r i))).length s1.pc 0 ⊆
      s1.memDomain :=
    bytesInMemory_allPcs _ s1.pc s1.mem s1.memDomain 0 st.bytes
  have finish (hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms))
      (hsafe : StepSafe s1.memDomain ms) :
      CaseGoal (.inst (.const r i)) s1 s2 ms := by
    exact encoderCaseStep (.inst (.const r i)) s1 s2 ms 0 hdom hcode
      (by
        intro k hk
        have hk0 : k = 0 := by omega
        subst hk0
        simpa using hsafe)
      (by intro k hk1 hk2; omega) hq
  by_cases h2 : i = 0#64
  · -- `xor r, r`
    have hinsn : x64ConstInsn r i = .binopRR .zxor .z32 r r := by
      simp [x64ConstInsn, h2]
    have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
        (encodeInsn (.binopRR .zxor .z32 r r)).length := by
      rw [hs2pc, hinsn]
    have hbmZ : bytesInMemoryHOL ms.pc (encodeInsn (.binopRR .zxor .z32 r r))
        ms.mem s1.memDomain := by
      rw [← hinsn]; exact hbm
    have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
        some (.binopRR .zxor .z32 r r, (encodeInsn (.binopRR .zxor .z32 r r)).length) :=
      decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmZ
        (decode_binopRR_z32 .zxor r r hr hr (by decide)) (by omega)
    have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmZ
    have hstepSafe : StepSafe s1.memDomain ms := by
      refine ⟨.binopRR .zxor .z32 r r, _, hdec, ?_, ?_⟩
      · intro j hj; exact hdomN j hj
      · intro a ha; simp [x64Touched] at ha
    have hnext := x64Next_const_zero ms s1.memDomain r hr hbmZ st.failed
    have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
      show targetStateRel x64Target s2 (x64Next ms)
      rw [hnext]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
      · show ms.pc + BitVec.ofNat 64
            (encodeInsn (.binopRR .zxor .z32 r r)).length = s2.pc
        rw [st.pc, hs2pc']
      · intro a ha
        show ms.mem a = s2.mem a
        rw [hs2mem a]
        rw [hs2dom] at ha
        exact st.mem a ha
      · intro x hx
        show readReg (writeReg ms r 0) x = s2.regs x
        rw [readReg_writeReg ms r 0 x hr hx.1, hs2regs x]
        by_cases hxr : x = r
        · subst hxr; simp [h2]
        · simp only [hxr, if_false]
          exact st.reg x hx
      · intro x hx
        show readXmm ms x = s2.fpRegs x
        rw [hs2fp x]
        exact st.fp x hx
    exact finish hq hstepSafe
  · by_cases h1 : i.toNat < 2147483648
    · -- `mov r, imm32`
      have h1' : i.toNat / 2 ^ 31 = 0 := hdiv.mpr h1
      have hinsn : x64ConstInsn r i = .movRI .z32 r i := by
        simp [x64ConstInsn, h1, h2]
      have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
          (encodeInsn (.movRI .z32 r i)).length := by
        rw [hs2pc, hinsn]
      have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.movRI .z32 r i))
          ms.mem s1.memDomain := by
        rw [← hinsn]; exact hbm
      obtain ⟨hlo, hhi⟩ := const_mov32_range i (by simpa using h1)
      have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.movRI .z32 r i, 5 + (if 8 ≤ r then 1 else 0)) :=
        decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
          (decode_movRI_z32 r hr i hlo hhi)
          (by rw [movRI_z32_length r hr i hlo hhi])
      have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
      have hstepSafe : StepSafe s1.memDomain ms := by
        refine ⟨.movRI .z32 r i, _, hdec, ?_, ?_⟩
        · intro j hj
          exact hdomN j (by rw [movRI_z32_length r hr i hlo hhi]; exact hj)
        · intro a ha; simp [x64Touched] at ha
      have hnext := x64Next_const_mov32 ms s1.memDomain r i hr h1 hbmM st.failed
      have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
        show targetStateRel x64Target s2 (x64Next ms)
        rw [hnext]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
        · show ms.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z32 r i)).length = s2.pc
          rw [st.pc, hs2pc']
        · intro a ha
          show ms.mem a = s2.mem a
          rw [hs2mem a]
          rw [hs2dom] at ha
          exact st.mem a ha
        · intro x hx
          show readReg (writeReg ms r i) x = s2.regs x
          rw [readReg_writeReg ms r i x hr hx.1, hs2regs x]
          by_cases hxr : x = r
          · subst hxr; simp
          · simp only [hxr, if_false]
            exact st.reg x hx
        · intro x hx
          show readXmm ms x = s2.fpRegs x
          rw [hs2fp x]
          exact st.fp x hx
      exact finish hq hstepSafe
    · -- `mov r, imm64`
      have h1' : i.toNat / 2 ^ 31 ≠ 0 := fun hc => h1 (hdiv.mp hc)
      have hinsn : x64ConstInsn r i = .movRI .z64 r i := by
        simp [x64ConstInsn, h1, h2]
      have hs2pc' : s2.pc = s1.pc + BitVec.ofNat 64
          (encodeInsn (.movRI .z64 r i)).length := by
        rw [hs2pc, hinsn]
      have hbmM : bytesInMemoryHOL ms.pc (encodeInsn (.movRI .z64 r i))
          ms.mem s1.memDomain := by
        rw [← hinsn]; exact hbm
      have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
          some (.movRI .z64 r i, 10) :=
        decode_bytesInMemory _ ms.pc ms.mem s1.memDomain _ _ hbmM
          (decode_movRI_z64 r hr i) (by rw [movRI_z64_length r hr i])
      have hdomN := bytesInMemoryHOL_domain _ _ _ _ hbmM
      have hstepSafe : StepSafe s1.memDomain ms := by
        refine ⟨.movRI .z64 r i, _, hdec, ?_, ?_⟩
        · intro j hj
          exact hdomN j (by rw [movRI_z64_length r hr i]; exact hj)
        · intro a ha; simp [x64Touched] at ha
      have hnext := x64Next_const_mov64 ms s1.memDomain r i hr hbmM st.failed
      have hq : targetStateRel x64Target s2 (x64Next^[0 + 1] ms) := by
        show targetStateRel x64Target s2 (x64Next ms)
        rw [hnext]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
        · show ms.pc + BitVec.ofNat 64 (encodeInsn (.movRI .z64 r i)).length = s2.pc
          rw [st.pc, hs2pc']
        · intro a ha
          show ms.mem a = s2.mem a
          rw [hs2mem a]
          rw [hs2dom] at ha
          exact st.mem a ha
        · intro x hx
          show readReg (writeReg ms r i) x = s2.regs x
          rw [readReg_writeReg ms r i x hr hx.1, hs2regs x]
          by_cases hxr : x = r
          · subst hxr; simp
          · simp only [hxr, if_false]
            exact st.reg x hx
        · intro x hx
          show readXmm ms x = s2.fpRegs x
          rw [hs2fp x]
          exact st.fp x hx
      exact finish hq hstepSafe

end Flapjack.Compiler.Encoders.X64
