module

public import Flapjack.Compiler.Encoders.X64.Machine.CarryCase
public import Flapjack.Compiler.Encoders.MemBytes

@[expose] public section

/-!
# The memory cases of `encoder_correct x64Target`

The eight `mem_op` forms (`load`/`load8`/`load16`/`load32` and the four stores)
each lower to a single `movRM`/`movMR`/`movzxRM` memory instruction.  The
interesting parts are:

* the effective address `readReg ms base + off` agrees with the source
  `s1.regs base + off`;
* the bytes the machine reads/writes (`readMemN`/`writeMemN`, little-endian)
  agree with the source `readMemWord`/`writeMemWord` at the byte counts the
  lowering uses;
* a failed source alignment/domain check forces every read byte into the domain,
  so the bytes the target reads are the bytes the source read, and a store keeps
  the domain (`writeMemWord_memDomain`);
* the machine's `writeRegSized .z32` zero-extension is the identity on a
  four-byte read (whose value is below `2^32`).

These are the x86-64 construction cases of `x64_encoder_correct`; the x86-64
encoding is a byte-for-byte port of the CakeML x86-64 encoder rather than of a
HOL script, so no case carries a `@[hol]` reference.
-/

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps

/-! ## The byte bridge between source and target memory -/

/-- `readMemWord` preserves the register file. -/
theorem readMemWord_regs (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.regs = s.regs := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState]
      exact ih _ _

/-- `readMemWord` preserves the floating-point register file. -/
theorem readMemWord_fpRegs (a : BitVec 64) (n : Nat) (s : AsmState 64) :
    (readMemWord (resultWidth := 64) a n s).2.fpRegs = s.fpRegs := by
  induction n generalizing a s with
  | zero => rfl
  | succ n ih =>
      rw [readMemWord_succ]
      simp only [assertState]
      exact ih _ _

/-- `writeMemWord` preserves the floating-point register file. -/
theorem writeMemWord_fpRegs (a : BitVec 64) (n : Nat) (v : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n v s).fpRegs = s.fpRegs := by
  induction n generalizing a v s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState, updMem]
      exact ih _ _ _

/-- `writeMemWord` preserves the register file. -/
theorem writeMemWord_regs (a : BitVec 64) (n : Nat) (v : BitVec 64) (s : AsmState 64) :
    (writeMemWord (valueWidth := 64) a n v s).regs = s.regs := by
  induction n generalizing a v s with
  | zero => rfl
  | succ n ih =>
      rw [writeMemWord_succ]
      simp only [assertState, updMem]
      exact ih _ _ _

/-! ## The machine's byte reads and writes -/

/-- The machine reads one byte as `readBytes` does. -/
theorem readMemN_one (s : X64State) (a : BitVec 64) : readMemN s 1 a = readBytes s.mem a 1 := by
  rw [readBytes_one]; rfl

/-- The machine reads two bytes as `readBytes` does. -/
theorem readMemN_two (s : X64State) (a : BitVec 64) : readMemN s 2 a = readBytes s.mem a 2 := by
  rw [readBytes_two]; rfl

/-- The machine reads four bytes as `readBytes` does. -/
theorem readMemN_four (s : X64State) (a : BitVec 64) : readMemN s 4 a = readBytes s.mem a 4 := by
  rw [readBytes_four]; rfl

/-- The machine reads eight bytes as `readBytes` does. -/
theorem readMemN_eight (s : X64State) (a : BitVec 64) : readMemN s 8 a = readBytes s.mem a 8 := by
  rw [readBytes_eight]; rfl

/-- The machine reads `2 ^ size` bytes as `readBytes` does. -/
theorem readMemN_eq (s : X64State) (size : Nat) (hsize : size < 4) (a : BitVec 64) :
    readMemN s (2 ^ size) a = readBytes s.mem a (2 ^ size) := by
  interval_cases size
  · exact readMemN_one s a
  · exact readMemN_two s a
  · exact readMemN_four s a
  · exact readMemN_eight s a

/-- The value a source load assembles is the value the machine load assembles. -/
theorem readValue_agree (a : BitVec 64) (size : Nat) (hsize : size < 4) (s : AsmState 64)
    (ms : X64State) (hbe : s.be = false)
    (hdom : ∀ k, k < 2 ^ size → s.memDomain (a + BitVec.ofNat 64 k))
    (hmem : ∀ x, s.memDomain x → ms.mem x = s.mem x) :
    (readMemWord (resultWidth := 64) a (2 ^ size) s).1 = readMemN ms (2 ^ size) a := by
  rw [readMemWord_fst a (2 ^ size) s hbe, readMemN_eq ms size hsize]
  exact readBytes_congr _ _ _ _ (fun k hk => (hmem _ (hdom k hk)).symm)

/-- The `k`-th byte of a little-endian write is the `k`-fold right shift. -/
theorem ushr8_iter (v : BitVec 64) (k : Nat) :
    v >>> (8 * k : Nat) = (fun x : BitVec 64 => x >>> (8 : Nat))^[k] v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, BitVec.shiftRight_add, ih, Function.iterate_succ_apply']

/-- The byte `k` of a value, in the shifted form `writeMemWord` produces. -/
theorem byteShift (v : BitVec 64) (k : Nat) :
    (v >>> (8 * k : Nat)).setWidth 8 =
      ((fun x : BitVec 64 => x >>> (8 : Nat))^[k] v).setWidth 8 := by
  rw [ushr8_iter]

/-- A one-byte source store is the machine's one-byte write. -/
theorem writeMemWord_mem_one (s : AsmState 64) (t : X64State) (a v x : BitVec 64)
    (hm : s.mem x = t.mem x) :
    (writeMemWord (valueWidth := 64) a 1 v s).mem x = (writeMemN t 1 a v).mem x := by
  simp only [writeMemWord, writeMemN, updMem_mem, assertState_mem]
  simp [hm]

/-- A two-byte source store is the machine's two-byte write. -/
theorem writeMemWord_mem_two (s : AsmState 64) (t : X64State) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = t.mem x) :
    (writeMemWord (valueWidth := 64) a 2 v s).mem x = (writeMemN t 2 a v).mem x := by
  simp only [writeMemWord, writeMemN, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  simp [hm]

/-- A four-byte source store is the machine's four-byte write. -/
theorem writeMemWord_mem_four (s : AsmState 64) (t : X64State) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = t.mem x) :
    (writeMemWord (valueWidth := 64) a 4 v s).mem x = (writeMemN t 4 a v).mem x := by
  simp only [writeMemWord, writeMemN, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  rw [show a + 1 + 1 + 1 = a + 3 by bv_omega, show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 0]
  simp [hm]

/-- An eight-byte source store is the machine's eight-byte write. -/
theorem writeMemWord_mem_eight (s : AsmState 64) (t : X64State) (a v x : BitVec 64)
    (hbe : s.be = false) (hm : s.mem x = t.mem x) :
    (writeMemWord (valueWidth := 64) a 8 v s).mem x = (writeMemN t 8 a v).mem x := by
  simp only [writeMemWord, writeMemN, updMem_mem, assertState_mem]
  simp only [hbe, Bool.false_eq_true, ite_false]
  rw [show a + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a + 7 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 + 1 = a + 6 by bv_omega,
    show a + 1 + 1 + 1 + 1 + 1 = a + 5 by bv_omega,
    show a + 1 + 1 + 1 + 1 = a + 4 by bv_omega,
    show a + 1 + 1 + 1 = a + 3 by bv_omega,
    show a + 1 + 1 = a + 2 by bv_omega]
  rw [byteShift v 1, byteShift v 2, byteShift v 3, byteShift v 4, byteShift v 5,
    byteShift v 6, byteShift v 0]
  simp [hm]

/-- The source store and the machine store agree at every byte count the
lowering emits. -/
theorem writeMemWord_memSize (s : AsmState 64) (t : X64State) (size : Nat)
    (hsize : size < 4) (a v x : BitVec 64) (hbe : s.be = false) (hm : s.mem x = t.mem x) :
    (writeMemWord (valueWidth := 64) a (2 ^ size) v s).mem x =
      (writeMemN t (2 ^ size) a v).mem x := by
  interval_cases size
  · exact writeMemWord_mem_one s t a v x hm
  · exact writeMemWord_mem_two s t a v x hbe hm
  · exact writeMemWord_mem_four s t a v x hbe hm
  · exact writeMemWord_mem_eight s t a v x hbe hm

/-- A four-byte little-endian read is below `2^32`. -/
theorem readBytes_four_lt (m : BitVec 64 → BitVec 8) (a : BitVec 64) :
    (readBytes m a 4).toNat < 2 ^ 32 := by
  rw [readBytes_four]
  rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft, BitVec.toNat_shiftLeft]
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hb3 : (m (a + 3)).toNat % 2 ^ 64 < 256 := by omega
  have hb2 : (m (a + 2)).toNat % 2 ^ 64 < 256 := by omega
  have hb1 : (m (a + 1)).toNat % 2 ^ 64 < 256 := by omega
  have hb0 : (m a).toNat % 2 ^ 64 < 256 := by omega
  apply Nat.or_lt_two_pow
  · apply Nat.or_lt_two_pow
    · apply Nat.or_lt_two_pow
      · omega
      · omega
    · omega
  · omega

/-- A four-byte machine read is below `2^32`, so `writeRegSized .z32` is the
identity on it. -/
theorem readMemN_four_lt (s : X64State) (a : BitVec 64) :
    (readMemN s 4 a).toNat < 2 ^ 32 := by
  rw [readMemN_four]
  exact readBytes_four_lt s.mem a

theorem setWidth32_eq_of_toNat_lt_32 (i : BitVec 64) (h : i.toNat < 2 ^ 32) :
    BitVec.setWidth 64 (BitVec.setWidth 32 i) = i := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 32)]
  rw [Nat.mod_eq_of_lt (by omega : i.toNat < 2 ^ 64)]

/-! ## Decoder and encoder lengths -/

theorem movRM_z64_length (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movRM .z64 dst base disp)).length =
      2 + (if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) := by
  rw [encodeInsn_movRM_z64 dst base hd hb disp hlo hhi]
  simp only [movRMZ64Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movMR_z64_length (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movMR .z64 src base disp)).length =
      2 + (if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5) := by
  rw [encodeInsn_movMR_z64 src base hs hb disp hlo hhi]
  simp only [movMRZ64Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movRM_z32_length (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movRM .z32 dst base disp)).length =
      (if 8 ≤ dst ∨ 8 ≤ base then 1 else 0) + 1 +
        ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movRM_z32 dst base hd hb disp hlo hhi]
  simp only [movRMZ32Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movMR_z32_length (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movMR .z32 src base disp)).length =
      (if 8 ≤ src ∨ 8 ≤ base then 1 else 0) + 1 +
        ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movMR_z32 src base hs hb disp hlo hhi]
  simp only [movMRZ32Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movMR_z16_length (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movMR .z16 src base disp)).length =
      2 + (if 8 ≤ src ∨ 8 ≤ base then 1 else 0) +
        ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movMR_z16 src base hs hb disp hlo hhi]
  simp only [movMRZ16Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movzxRM_z16_length (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movzxRM .z16 .z64 dst base disp)).length =
      3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movzxRM_z16 dst base hd hb disp hlo hhi]
  simp only [movzxBytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movzxRM_z8_length (dst base : Nat) (hd : dst < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movzxRM (.z8 true) .z64 dst base disp)).length =
      3 + ((if base % 8 = 4 then 1 else 0) +
        (if disp = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movzxRM_z8 dst base hd hb disp hlo hhi]
  simp only [movzxBytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

theorem movMR_z8_length (h : Bool) (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movMR (.z8 h) src base disp)).length =
      1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if h = true then 1 else 0) +
        ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [encodeInsn_movMR_z8 h src base hs hb disp hlo hhi]
  simp only [movMRZ8Bytes, List.length_append, List.length_cons, List.length_nil]
  split_ifs <;> simp

/-! ## Encodings of the lowered forms -/

/-- The encode of a single-instruction memory lowering is that instruction's
encoding. -/
theorem x64Enc_memSingle (op : HolMemop) (r base : Nat) (off : BitVec 64) (insn : X64Insn)
    (hflat : (x64Ast (.inst (.mem op r (.addr base off)))).flatMap encodeInsn =
      encodeInsn insn)
    (hne : encodeInsn insn ≠ []) :
    x64Target.config.encode (.inst (.mem op r (.addr base off))) = encodeInsn insn := by
  show x64Enc (.inst (.mem op r (.addr base off))) = encodeInsn insn
  rw [x64Enc_of_flatMap _ _ hflat hne]

theorem x64Enc_load (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .load r (.addr base off))) =
      encodeInsn (.movRM .z64 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .load r base off (.movRM .z64 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movRM_z64 r base hr hb off hlo hhi]; simp [movRMZ64Bytes]

theorem x64Enc_load32 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .load32 r (.addr base off))) =
      encodeInsn (.movRM .z32 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .load32 r base off (.movRM .z32 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movRM_z32 r base hr hb off hlo hhi]; simp [movRMZ32Bytes]

theorem x64Enc_load16 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .load16 r (.addr base off))) =
      encodeInsn (.movzxRM .z16 .z64 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .load16 r base off (.movzxRM .z16 .z64 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movzxRM_z16 r base hr hb off hlo hhi]; simp [movzxBytes]

theorem x64Enc_load8 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .load8 r (.addr base off))) =
      encodeInsn (.movzxRM (.z8 true) .z64 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .load8 r base off (.movzxRM (.z8 true) .z64 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movzxRM_z8 r base hr hb off hlo hhi]; simp [movzxBytes]

theorem x64Enc_store (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .store r (.addr base off))) =
      encodeInsn (.movMR .z64 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .store r base off (.movMR .z64 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movMR_z64 r base hr hb off hlo hhi]; simp [movMRZ64Bytes]

theorem x64Enc_store32 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .store32 r (.addr base off))) =
      encodeInsn (.movMR .z32 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .store32 r base off (.movMR .z32 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movMR_z32 r base hr hb off hlo hhi]; simp [movMRZ32Bytes]

theorem x64Enc_store16 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .store16 r (.addr base off))) =
      encodeInsn (.movMR .z16 r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .store16 r base off (.movMR .z16 r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movMR_z16 r base hr hb off hlo hhi]; simp [movMRZ16Bytes]

theorem x64Enc_store8 (r base : Nat) (off : BitVec 64) (hr : r < 16) (hb : base < 16)
    (hlo : -(2^31 : Int) ≤ off.toInt) (hhi : off.toInt < 2^31) :
    x64Target.config.encode (.inst (.mem .store8 r (.addr base off))) =
      encodeInsn (.movMR (.z8 (3 < r)) r base off) := by
  have hzr : totalNum2Zreg r = r := totalNum2Zreg_eq r hr
  have hzb : totalNum2Zreg base = base := totalNum2Zreg_eq base hb
  refine x64Enc_memSingle .store8 r base off (.movMR (.z8 (3 < r)) r base off) ?_ ?_
  · simp only [x64Ast, x64Inst, hzr, hzb, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  · rw [encodeInsn_movMR_z8 (3 < r) r base hr hb off hlo hhi]; simp [movMRZ8Bytes]

/-! ## Model steps over the memory forms -/

theorem execInsn_movRM (sz : ZSize) (dst base : Nat) (disp : BitVec 64) (len : Nat)
    (s : X64State) :
    execInsn (.movRM sz dst base disp) len s =
      writeRegSized sz dst (readMemN s (sizeBytes sz) (readReg s base + disp)) s := rfl

theorem execInsn_movMR (sz : ZSize) (src base : Nat) (disp : BitVec 64) (len : Nat)
    (s : X64State) :
    execInsn (.movMR sz src base disp) len s =
      writeMemN s (sizeBytes sz) (readReg s base + disp) (readReg s src) := rfl

theorem execInsn_movzxRM (sz1 sz2 : ZSize) (dst base : Nat) (disp : BitVec 64) (len : Nat)
    (s : X64State) :
    execInsn (.movzxRM sz1 sz2 dst base disp) len s =
      writeReg s dst (readMemN s (sizeBytes sz1) (readReg s base + disp)) := rfl

theorem x64Next_memRM (ms : X64State) (_dm : BitVec 64 → Prop) (sz : ZSize) (dst base : Nat)
    (disp : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRM sz dst base disp, len))
    (hlen : (encodeInsn (.movRM sz dst base disp)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeRegSized sz dst
        (readMemN ms (sizeBytes sz) (readReg ms base + disp)) ms with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRM sz dst base disp)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn_movRM]

theorem x64Next_memMR (ms : X64State) (_dm : BitVec 64 → Prop) (sz : ZSize) (src base : Nat)
    (disp : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movMR sz src base disp, len))
    (hlen : (encodeInsn (.movMR sz src base disp)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeMemN ms (sizeBytes sz) (readReg ms base + disp) (readReg ms src) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movMR sz src base disp)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn_movMR]

theorem x64Next_memZXRM (ms : X64State) (_dm : BitVec 64 → Prop) (sz1 sz2 : ZSize)
    (dst base : Nat) (disp : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movzxRM sz1 sz2 dst base disp, len))
    (hlen : (encodeInsn (.movzxRM sz1 sz2 dst base disp)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeReg ms dst
        (readMemN ms (sizeBytes sz1) (readReg ms base + disp)) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movzxRM sz1 sz2 dst base disp)).length } := by
  rw [hlen]
  simp only [x64Next, hfailed, Bool.false_eq_true, ite_false, hdec, execInsn_movzxRM]

/-- A 32-bit register write is the identity on a value below `2^32`. -/
theorem writeRegSized_z32_eq (ms : X64State) (r : Nat) (V : BitVec 64)
    (hV : V.toNat < 2 ^ 32) :
    writeRegSized .z32 r V ms = writeReg ms r V := by
  simp only [writeRegSized]
  rw [setWidth32_eq_of_toNat_lt_32 V hV]

/-- A 32-bit load writes the four-byte read unchanged. -/
theorem x64Next_memRM_z32 (ms : X64State) (_dm : BitVec 64 → Prop) (dst base : Nat)
    (disp : BitVec 64) (len : Nat)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRM .z32 dst base disp, len))
    (hlen : (encodeInsn (.movRM .z32 dst base disp)).length = len)
    (hfailed : ms.failed = false) :
    x64Next ms = { writeReg ms dst (readMemN ms 4 (readReg ms base + disp)) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRM .z32 dst base disp)).length } := by
  rw [x64Next_memRM ms _dm .z32 dst base disp len hdec hlen hfailed]
  simp only [sizeBytes]
  rw [writeRegSized_z32_eq ms dst (readMemN ms 4 (readReg ms base + disp))
    (readMemN_four_lt ms _)]

/-! ## `asm_ok` extraction -/

/-- `asm_ok` of a memory instruction checks the destination and base registers. -/
theorem memRegOk_of_asm (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem op r (.addr base off))) x64Config = true) :
    asmRegOkExact r x64Config = true ∧ asmRegOkExact base x64Config = true := by
  cases op <;>
    simp only [asmOkExact, asmInstOkExact, x64Config, Bool.and_eq_true, Bool.or_eq_true,
      asmAddrOffsetOkExact, asmHwOffsetOkExact, asmByteOffsetOkExact] at h
  all_goals
    simp at h
    exact ⟨h.1.1, h.1.2⟩

/-- The offset window of the x86-64 memory forms. -/
theorem offsetBounds_of (off : BitVec 64)
    (h : asmOffsetOkExact 0 (x64Min32, x64Max32) off = true) :
    -(2 ^ 31 : Int) ≤ off.toInt ∧ off.toInt < 2 ^ 31 := by
  simp only [asmOffsetOkExact, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlo, hhi⟩, -⟩ := h
  rw [x64Min32_toInt] at hlo
  rw [x64Max32_toInt] at hhi
  omega

/-- `asm_ok` bounds the offset of every memory form by the signed 32-bit
range. -/
theorem memOffset_of_asm (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem op r (.addr base off))) x64Config = true) :
    -(2 ^ 31 : Int) ≤ off.toInt ∧ off.toInt < 2 ^ 31 := by
  cases op <;>
    simp only [asmOkExact, asmInstOkExact, x64Config, Bool.and_eq_true, Bool.or_eq_true,
      asmAddrOffsetOkExact, asmHwOffsetOkExact, asmByteOffsetOkExact] at h
  all_goals
    simp at h
    exact offsetBounds_of off h.2

/-! ## Domain facts from the source's failed checks -/

theorem memLoadDomain (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (sz : Nat) (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ sz))
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.mem op r (.addr base off)))).length) s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 ^ sz → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ sz) s1).2.failed = false := by
    have h : s2.failed = false := by
      rw [Bool.not_eq_true] at hok
      exact hok
    rw [← hupd] at h
    simp only [asmUpd, instUpd, updPc, hspec, memLoad, addrHOL, updReg, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at h
    obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 h
    exact hf
  exact readMemWord_domain (s1.regs base + off) (2 ^ sz) s1 hbe hfail

theorem memStoreDomain (op : HolMemop) (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64)
    (sz : Nat) (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ sz))
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) (s1.pc + BitVec.ofNat 64
      (x64Target.config.encode (.inst (.mem op r (.addr base off)))).length) s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 ^ sz → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ sz)
      (s1.regs r) s1).failed = false := by
    have h : s2.failed = false := by
      rw [Bool.not_eq_true] at hok
      exact hok
    rw [← hupd] at h
    simp only [asmUpd, instUpd, updPc, hspec, memStore, addrHOL,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at h
    obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 h
    exact hf
  exact writeMemWord_domain (s1.regs base + off) (2 ^ sz) (s1.regs r) s1 hbe
    (not_of_eq_false hfail)

/-! ## The machine's memory writes leave the rest of the state alone -/

/-! ## Touched-byte facts -/

/-- A per-byte domain fact gives the domain fact for every address in the
touched byte list. -/
theorem bytesAt_subset {d : BitVec 64 → Prop} {a : BitVec 64} {n : Nat}
    (h : ∀ j, j < n → d (a + BitVec.ofNat 64 j)) :
    ∀ x, x ∈ bytesAt a n → d x := by
  intro x hx
  simp only [bytesAt, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  exact h j hj

/-- The encoder's 8-bit store flag `3 < r` and the decoder's normalised flag
agree whenever a REX prefix is present, so the two byte lists coincide. -/
theorem encodeInsn_movMR_z8_self (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    encodeInsn (.movMR (.z8 (if 8 ≤ src ∨ 8 ≤ base then true else 3 < src)) src base disp) =
      encodeInsn (.movMR (.z8 (3 < src)) src base disp) := by
  rw [encodeInsn_movMR_z8 _ src base hs hb disp hlo hhi,
      encodeInsn_movMR_z8 _ src base hs hb disp hlo hhi]
  by_cases h8 : 8 ≤ src ∨ 8 ≤ base <;> simp [movMRZ8Bytes, h8]

/-- Length of the decoder's normalised 8-bit store, matching the encoder. -/
theorem movMR_z8_length_self (src base : Nat) (hs : src < 16) (hb : base < 16)
    (disp : BitVec 64) (hlo : -(2^31 : Int) ≤ disp.toInt) (hhi : disp.toInt < 2^31) :
    (encodeInsn (.movMR (.z8 (if 8 ≤ src ∨ 8 ≤ base then true else decide (3 < src)))
        src base disp)).length =
      1 + (if 8 ≤ src ∨ 8 ≤ base then 1 else if decide (3 < src) = true then 1 else 0) +
        ((if base % 8 = 4 then 1 else 0) +
          (if disp = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ disp.toInt ∧ disp.toInt ≤ 127 then 2 else 5)) := by
  rw [movMR_z8_length (if 8 ≤ src ∨ 8 ≤ base then true else decide (3 < src))
    src base hs hb disp hlo hhi]
  by_cases h8 : 8 ≤ src ∨ 8 ≤ base <;> simp [h8]

/-! ## The load spine -/

theorem case_memLoadSpine (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State) (sz : Nat) (hsz : sz < 4) (insn : X64Insn)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ sz))
    (henc : x64Target.config.encode (.inst (.mem op r (.addr base off))) = encodeInsn insn)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (insn, (encodeInsn insn).length))
    (hnext : x64Next ms = { writeReg ms r (readMemN ms (2 ^ sz) (readReg ms base + off)) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn insn).length })
    (htouch : ∀ a, a ∈ x64Touched ms insn → s1.memDomain a)
    (hdom : ∀ k, k < 2 ^ sz → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k))
    (hrok : asmRegOkExact r x64Config = true) (hbok : asmRegOkExact base x64Config = true)
    (hpos : 0 < (encodeInsn insn).length)
    (h : asmStep x64Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregr := regOk_of_asmRegOk r hrok
  have hregb := regOk_of_asmRegOk base hbok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn insn).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [henc]
  have hs2mem : ∀ a, s2.mem a = s1.mem a := by
    rw [← st.upd]; intro a
    simp only [asmUpd, instUpd, updPc, hspec, memLoad, addrHOL, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, hspec, memLoad, addrHOL, updReg, assertState,
      readMemWord_memDomain]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, hspec, memLoad, addrHOL, updReg, assertState,
      readMemWord_fpRegs, st.be, Bool.false_eq_true, ite_false]
  have hs2regs : ∀ x, s2.regs x =
      (if x = r then (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ sz) s1).1
       else s1.regs x) := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, hspec, memLoad, addrHOL, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true,
      ite_false]
  have haddr : readReg ms base + off = s1.regs base + off := by
    rw [st.reg base hregb]
  have hvalue : (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ sz) s1).1 =
      readMemN ms (2 ^ sz) (readReg ms base + off) := by
    rw [haddr]
    exact readValue_agree _ sz hsz s1 ms st.be hdom st.mem
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn insn) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hq : targetStateRel x64Target s2 (x64Next ms) := by
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeReg, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 (encodeInsn insn).length = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show ms.mem a = s2.mem a
      rw [hs2mem a]
      exact st.mem a (hs2dom ▸ ha)
    · intro x hx
      have hx16 : x < 16 := by simpa [x64Target_config, x64Config] using hx.1
      show readReg (writeReg ms r (readMemN ms (2 ^ sz) (readReg ms base + off))) x = s2.regs x
      rw [readReg_writeReg ms r _ x hr hx16]
      by_cases hxr : x = r
      · rw [ite_eq_left hxr, hs2regs x, ite_eq_left hxr]
        exact hvalue.symm
      · rw [ite_eq_right hxr, hs2regs x, ite_eq_right hxr]
        exact st.reg x hx
    · intro x hx
      show readXmm ms x = s2.fpRegs x
      rw [hs2fp x]
      exact st.fp x (by simpa [x64Target_config, x64Config] using hx)
  let t : Nat → X64State := fun k => match k with | 0 => ms | _ => x64Next ms
  let offs : Nat → Nat := fun k => match k with | 0 => 0 | _ => (encodeInsn insn).length
  have hsafe : ∀ k, k ≤ 0 → StepSafe s1.memDomain (t k) := by
    intro k hk
    interval_cases k
    rw [show t 0 = ms from rfl]
    refine ⟨insn, (encodeInsn insn).length, hdec, ?_, ?_⟩
    · intro j hj
      exact bytesInMemoryHOL_domain _ _ _ _ hbm j hj
    · intro a ha
      exact htouch a ha
  have hoff : ∀ k, k ≤ 0 → offs k < offs 1 := by
    intro k hk
    interval_cases k
    show 0 < (encodeInsn insn).length
    exact hpos
  exact x64RunCase _ s1 s2 ms 0 t offs h
    (by
      show (x64Target.config.encode (.inst (.mem op r (.addr base off)))).length = offs 1
      rw [henc]
      rfl)
    (by rfl)
    (by
      intro k hk
      interval_cases k
      rfl)
    (by intro k h1 h2; omega) hoff hsafe hs2dom hq

/-! ## The store spine -/

theorem case_memStoreSpine (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : X64State) (sz : Nat) (hsz : sz < 4) (insn : X64Insn)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ sz))
    (henc : x64Target.config.encode (.inst (.mem op r (.addr base off))) = encodeInsn insn)
    (hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (insn, (encodeInsn insn).length))
    (hnext : x64Next ms = { writeMemN ms (2 ^ sz) (readReg ms base + off) (readReg ms r) with
      pc := ms.pc + BitVec.ofNat 64 (encodeInsn insn).length })
    (htouch : ∀ a, a ∈ x64Touched ms insn → s1.memDomain a)
    (hrok : asmRegOkExact r x64Config = true) (hbok : asmRegOkExact base x64Config = true)
    (hpos : 0 < (encodeInsn insn).length)
    (h : asmStep x64Config s1 (.inst (.mem op r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem op r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregr := regOk_of_asmRegOk r hrok
  have hregb := regOk_of_asmRegOk base hbok
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 (encodeInsn insn).length := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc]
    rw [henc]
  have hs2mem : ∀ a, s2.mem a =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) (2 ^ sz) (s1.regs r) s1).mem a := by
    intro a
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, hspec, memStore, addrHOL, assertState_mem,
      Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true, ite_false]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, hspec, memStore, addrHOL, assertState,
      writeMemWord_memDomain]
  have hs2fp : ∀ x, s2.fpRegs x = s1.fpRegs x := by
    rw [← st.upd]; intro x
    simp only [asmUpd, instUpd, updPc, hspec, memStore, addrHOL, assertState,
      writeMemWord_fpRegs, st.be, Bool.false_eq_true, ite_false]
  have hs2regs : ∀ x, s2.regs x = s1.regs x := by
    intro x
    rw [← st.upd]
    simp only [asmUpd, instUpd, updPc, hspec, memStore, addrHOL, assertState,
      writeMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, st.be, Bool.false_eq_true,
      ite_false]
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn insn) ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hq : targetStateRel x64Target s2 (x64Next ms) := by
    rw [hnext]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp only [x64Target_stateOk, x64StateOk, writeMemN_failed, st.failed, Bool.not_false]
    · show ms.pc + BitVec.ofNat 64 (encodeInsn insn).length = s2.pc
      rw [st.pc, hs2pc]
    · intro a ha
      show (writeMemN ms (2 ^ sz) (readReg ms base + off) (readReg ms r)).mem a = s2.mem a
      rw [hs2mem a]
      have hm : s1.mem a = ms.mem a := (st.mem a (hs2dom ▸ ha)).symm
      have hmem := writeMemWord_memSize s1 ms sz hsz (s1.regs base + off) (s1.regs r) a st.be hm
      rw [show s1.regs r = readReg ms r from (st.reg r hregr).symm,
          show s1.regs base = readReg ms base from (st.reg base hregb).symm] at hmem ⊢
      exact hmem.symm
    · intro x hx
      show readReg (writeMemN ms (2 ^ sz) (readReg ms base + off) (readReg ms r)) x = s2.regs x
      rw [show readReg (writeMemN ms (2 ^ sz) (readReg ms base + off) (readReg ms r)) x
          = readReg ms x by simp only [readReg, writeMemN_regs]]
      rw [hs2regs x]
      exact st.reg x hx
    · intro x hx
      simp only [x64Target_getFpReg, readXmm, writeMemN_xmm]
      rw [hs2fp x]
      exact st.fp x (by simpa [x64Target_config, x64Config] using hx)
  let t : Nat → X64State := fun k => match k with | 0 => ms | _ => x64Next ms
  let offs : Nat → Nat := fun k => match k with | 0 => 0 | _ => (encodeInsn insn).length
  have hsafe : ∀ k, k ≤ 0 → StepSafe s1.memDomain (t k) := by
    intro k hk
    interval_cases k
    rw [show t 0 = ms from rfl]
    refine ⟨insn, (encodeInsn insn).length, hdec, ?_, ?_⟩
    · intro j hj
      exact bytesInMemoryHOL_domain _ _ _ _ hbm j hj
    · intro a ha
      exact htouch a ha
  have hoff : ∀ k, k ≤ 0 → offs k < offs 1 := by
    intro k hk
    interval_cases k
    show 0 < (encodeInsn insn).length
    exact hpos
  exact x64RunCase _ s1 s2 ms 0 t offs h
    (by
      show (x64Target.config.encode (.inst (.mem op r (.addr base off)))).length = offs 1
      rw [henc]
      rfl)
    (by rfl)
    (by
      intro k hk
      interval_cases k
      rfl)
    (by intro k h1 h2; omega) hoff hsafe hs2dom hq


/-! ## The eight `mem_op` cases -/

/-- The `load` constructor of `encoder_correct x64Target`. -/
theorem case_load (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .load r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .load r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .load r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .load r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .load = memLoad (width := 64) (2 ^ 3) := rfl
  have henc : x64Target.config.encode (.inst (.mem .load r (.addr base off))) =
      encodeInsn (.movRM .z64 r base off) := x64Enc_load r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movRM .z64 r base off)).length =
      2 + (if base % 8 = 4 then 1 else 0) +
        (if off = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5) :=
    movRM_z64_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRM .z64 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRM .z64 r base off, (encodeInsn (.movRM .z64 r base off)).length) := by
    have hd := decode_movRM_z64 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movRM .z64 r base off)) ms.pc ms.mem
      s1.memDomain (.movRM .z64 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeReg ms r (readMemN ms (2 ^ 3) (readReg ms base + off)) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRM .z64 r base off)).length } := by
    rw [x64Next_memRM ms s1.memDomain .z64 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memLoadDomain .load r base off s1 s2 3 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movRM .z64 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movRM .z64 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memLoadSpine .load r base off s1 s2 ms 3 (by decide) (.movRM .z64 r base off)
    hspec henc hdec hnext htouch hdom hrok hbok hpos h

/-- The `load32` constructor of `encoder_correct x64Target`. -/
theorem case_load32 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .load32 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .load32 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .load32 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .load32 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load32 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .load32 = memLoad (width := 64) (2 ^ 2) := rfl
  have henc : x64Target.config.encode (.inst (.mem .load32 r (.addr base off))) =
      encodeInsn (.movRM .z32 r base off) := x64Enc_load32 r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movRM .z32 r base off)).length =
      (if 8 ≤ r ∨ 8 ≤ base then 1 else 0) + 1 +
        ((if base % 8 = 4 then 1 else 0) +
          (if off = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movRM_z32_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movRM .z32 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movRM .z32 r base off, (encodeInsn (.movRM .z32 r base off)).length) := by
    have hd := decode_movRM_z32 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movRM .z32 r base off)) ms.pc ms.mem
      s1.memDomain (.movRM .z32 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeReg ms r (readMemN ms (2 ^ 2) (readReg ms base + off)) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movRM .z32 r base off)).length } := by
    rw [x64Next_memRM_z32 ms s1.memDomain r base off _ hdec rfl st.failed]
    rfl
  have hdom := memLoadDomain .load32 r base off s1 s2 2 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movRM .z32 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movRM .z32 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memLoadSpine .load32 r base off s1 s2 ms 2 (by decide) (.movRM .z32 r base off)
    hspec henc hdec hnext htouch hdom hrok hbok hpos h

/-- The `load16` constructor of `encoder_correct x64Target`. -/
theorem case_load16 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .load16 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .load16 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .load16 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .load16 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load16 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .load16 = memLoad (width := 64) (2 ^ 1) := rfl
  have henc : x64Target.config.encode (.inst (.mem .load16 r (.addr base off))) =
      encodeInsn (.movzxRM .z16 .z64 r base off) := x64Enc_load16 r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movzxRM .z16 .z64 r base off)).length =
      3 + ((if base % 8 = 4 then 1 else 0) +
        (if off = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movzxRM_z16_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movzxRM .z16 .z64 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movzxRM .z16 .z64 r base off,
        (encodeInsn (.movzxRM .z16 .z64 r base off)).length) := by
    have hd := decode_movzxRM_z16 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movzxRM .z16 .z64 r base off)) ms.pc ms.mem
      s1.memDomain (.movzxRM .z16 .z64 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeReg ms r (readMemN ms (2 ^ 1) (readReg ms base + off)) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movzxRM .z16 .z64 r base off)).length } := by
    rw [x64Next_memZXRM ms s1.memDomain .z16 .z64 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memLoadDomain .load16 r base off s1 s2 1 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movzxRM .z16 .z64 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movzxRM .z16 .z64 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memLoadSpine .load16 r base off s1 s2 ms 1 (by decide) (.movzxRM .z16 .z64 r base off)
    hspec henc hdec hnext htouch hdom hrok hbok hpos h

/-- The `load8` constructor of `encoder_correct x64Target`. -/
theorem case_load8 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .load8 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .load8 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .load8 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .load8 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .load8 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .load8 = memLoad (width := 64) (2 ^ 0) := rfl
  have henc : x64Target.config.encode (.inst (.mem .load8 r (.addr base off))) =
      encodeInsn (.movzxRM (.z8 true) .z64 r base off) := x64Enc_load8 r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movzxRM (.z8 true) .z64 r base off)).length =
      3 + ((if base % 8 = 4 then 1 else 0) +
        (if off = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movzxRM_z8_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movzxRM (.z8 true) .z64 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movzxRM (.z8 true) .z64 r base off,
        (encodeInsn (.movzxRM (.z8 true) .z64 r base off)).length) := by
    have hd := decode_movzxRM_z8 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movzxRM (.z8 true) .z64 r base off)) ms.pc ms.mem
      s1.memDomain (.movzxRM (.z8 true) .z64 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeReg ms r (readMemN ms (2 ^ 0) (readReg ms base + off)) with
        pc := ms.pc + BitVec.ofNat 64
          (encodeInsn (.movzxRM (.z8 true) .z64 r base off)).length } := by
    rw [x64Next_memZXRM ms s1.memDomain (.z8 true) .z64 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memLoadDomain .load8 r base off s1 s2 0 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movzxRM (.z8 true) .z64 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movzxRM (.z8 true) .z64 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memLoadSpine .load8 r base off s1 s2 ms 0 (by decide)
    (.movzxRM (.z8 true) .z64 r base off) hspec henc hdec hnext htouch hdom hrok hbok hpos h

/-- The `store` constructor of `encoder_correct x64Target`. -/
theorem case_store (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .store r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .store r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .store r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .store r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .store = memStore (width := 64) (2 ^ 3) := rfl
  have henc : x64Target.config.encode (.inst (.mem .store r (.addr base off))) =
      encodeInsn (.movMR .z64 r base off) := x64Enc_store r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movMR .z64 r base off)).length =
      2 + (if base % 8 = 4 then 1 else 0) +
        (if off = 0 ∧ base % 8 ≠ 5 then 1
         else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5) :=
    movMR_z64_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movMR .z64 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movMR .z64 r base off, (encodeInsn (.movMR .z64 r base off)).length) := by
    have hd := decode_movMR_z64 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movMR .z64 r base off)) ms.pc ms.mem
      s1.memDomain (.movMR .z64 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeMemN ms (2 ^ 3) (readReg ms base + off) (readReg ms r) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movMR .z64 r base off)).length } := by
    rw [x64Next_memMR ms s1.memDomain .z64 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memStoreDomain .store r base off s1 s2 3 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movMR .z64 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movMR .z64 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memStoreSpine .store r base off s1 s2 ms 3 (by decide) (.movMR .z64 r base off)
    hspec henc hdec hnext htouch hrok hbok hpos h

/-- The `store32` constructor of `encoder_correct x64Target`. -/
theorem case_store32 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .store32 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .store32 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .store32 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .store32 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store32 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .store32 = memStore (width := 64) (2 ^ 2) := rfl
  have henc : x64Target.config.encode (.inst (.mem .store32 r (.addr base off))) =
      encodeInsn (.movMR .z32 r base off) := x64Enc_store32 r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movMR .z32 r base off)).length =
      (if 8 ≤ r ∨ 8 ≤ base then 1 else 0) + 1 +
        ((if base % 8 = 4 then 1 else 0) +
          (if off = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movMR_z32_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movMR .z32 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movMR .z32 r base off, (encodeInsn (.movMR .z32 r base off)).length) := by
    have hd := decode_movMR_z32 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movMR .z32 r base off)) ms.pc ms.mem
      s1.memDomain (.movMR .z32 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeMemN ms (2 ^ 2) (readReg ms base + off) (readReg ms r) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movMR .z32 r base off)).length } := by
    rw [x64Next_memMR ms s1.memDomain .z32 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memStoreDomain .store32 r base off s1 s2 2 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movMR .z32 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movMR .z32 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memStoreSpine .store32 r base off s1 s2 ms 2 (by decide) (.movMR .z32 r base off)
    hspec henc hdec hnext htouch hrok hbok hpos h

/-- The `store16` constructor of `encoder_correct x64Target`. -/
theorem case_store16 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .store16 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .store16 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .store16 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .store16 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store16 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .store16 = memStore (width := 64) (2 ^ 1) := rfl
  have henc : x64Target.config.encode (.inst (.mem .store16 r (.addr base off))) =
      encodeInsn (.movMR .z16 r base off) := x64Enc_store16 r base off hr hb hlo hhi
  have hlen : (encodeInsn (.movMR .z16 r base off)).length =
      2 + (if 8 ≤ r ∨ 8 ≤ base then 1 else 0) +
        ((if base % 8 = 4 then 1 else 0) +
          (if off = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movMR_z16_length r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc (encodeInsn (.movMR .z16 r base off)) ms.mem
      s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movMR .z16 r base off, (encodeInsn (.movMR .z16 r base off)).length) := by
    have hd := decode_movMR_z16 r base hr hb off hlo hhi
    have h := decode_bytesInMemory (encodeInsn (.movMR .z16 r base off)) ms.pc ms.mem
      s1.memDomain (.movMR .z16 r base off) _ hbm hd (by rw [hlen])
    rw [← hlen] at h
    exact h
  have hnext : x64Next ms =
      { writeMemN ms (2 ^ 1) (readReg ms base + off) (readReg ms r) with
        pc := ms.pc + BitVec.ofNat 64 (encodeInsn (.movMR .z16 r base off)).length } := by
    rw [x64Next_memMR ms s1.memDomain .z16 r base off _ hdec rfl st.failed]
    rfl
  have hdom := memStoreDomain .store16 r base off s1 s2 1 hspec st.upd st.be st.ok
  have htouch : ∀ a, a ∈ x64Touched ms (.movMR .z16 r base off) → s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movMR .z16 r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memStoreSpine .store16 r base off s1 s2 ms 1 (by decide) (.movMR .z16 r base off)
    hspec henc hdec hnext htouch hrok hbok hpos h

/-- The `store8` constructor of `encoder_correct x64Target`.  The decoder
normalises the 8-bit store flag to `true` whenever a REX prefix is present, so
the case uses the decoded flag throughout. -/
theorem case_store8 (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (ms : X64State)
    (h : asmStep x64Config s1 (.inst (.mem .store8 r (.addr base off))) s2 ∧
      targetStateRel x64Target s1 ms) :
    CaseGoal (.inst (.mem .store8 r (.addr base off))) s1 s2 ms := by
  have st := x64Start _ s1 s2 ms h
  have hok : asmOkExact (.inst (.mem .store8 r (.addr base off))) x64Config = true := by
    simpa [x64Target_config] using st.asmOk
  obtain ⟨hrok, hbok⟩ := memRegOk_of_asm .store8 r base off hok
  obtain ⟨hlo, hhi⟩ := memOffset_of_asm .store8 r base off hok
  have hr : r < 16 := jumpReg_reg_lt r hrok
  have hb : base < 16 := jumpReg_reg_lt base hbok
  have hregb := regOk_of_asmRegOk base hbok
  have hspec : memOp (width := 64) .store8 = memStore (width := 64) (2 ^ 0) := rfl
  have henc : x64Target.config.encode (.inst (.mem .store8 r (.addr base off))) =
      encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r)) r base off) := by
    rw [x64Enc_store8 r base off hr hb hlo hhi]
    exact (encodeInsn_movMR_z8_self r base hr hb off hlo hhi).symm
  have hlen : (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else decide (3 < r)))
        r base off)).length =
      1 + (if 8 ≤ r ∨ 8 ≤ base then 1 else if decide (3 < r) = true then 1 else 0) +
        ((if base % 8 = 4 then 1 else 0) +
          (if off = 0 ∧ base % 8 ≠ 5 then 1
           else if -128 ≤ off.toInt ∧ off.toInt ≤ 127 then 2 else 5)) :=
    movMR_z8_length_self r base hr hb off hlo hhi
  have hbm : bytesInMemoryHOL ms.pc
      (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r)) r base off))
      ms.mem s1.memDomain := by
    have h' := st.bytesTarget
    rw [henc] at h'
    rw [← st.pc] at h'
    exact h'
  have hdec : decode (fun k => ms.mem (ms.pc + BitVec.ofNat 64 k)) =
      some (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else decide (3 < r))) r base off,
        (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else decide (3 < r)))
          r base off)).length) := by
    have hd := decode_movMR_z8 (3 < r) r base hr hb off hlo hhi
    rw [← encodeInsn_movMR_z8_self r base hr hb off hlo hhi] at hd
    rw [← hlen] at hd
    exact decode_bytesInMemory
      (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else decide (3 < r))) r base off))
      ms.pc ms.mem s1.memDomain _ _ hbm hd (by omega)
  have hnext : x64Next ms =
      { writeMemN ms (2 ^ 0) (readReg ms base + off) (readReg ms r) with
        pc := ms.pc + BitVec.ofNat 64
          (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r))
            r base off)).length } := by
    rw [x64Next_memMR ms s1.memDomain
      (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r)) r base off _ hdec rfl st.failed]
    rfl
  have hdom := memStoreDomain .store8 r base off s1 s2 0 hspec st.upd st.be st.ok
  have htouch : ∀ a,
      a ∈ x64Touched ms (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r)) r base off) →
      s1.memDomain a := by
    intro a ha
    have hd := hdom
    rw [← st.reg base hregb] at hd
    exact bytesAt_subset hd a (by simpa [x64Touched, sizeBytes] using ha)
  have hpos : 0 < (encodeInsn (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r))
      r base off)).length := by
    rw [hlen]; split_ifs <;> omega
  exact case_memStoreSpine .store8 r base off s1 s2 ms 0 (by decide)
    (.movMR (.z8 (if 8 ≤ r ∨ 8 ≤ base then true else 3 < r)) r base off)
    hspec henc hdec hnext htouch hrok hbok hpos h

end Flapjack.Compiler.Encoders.X64
