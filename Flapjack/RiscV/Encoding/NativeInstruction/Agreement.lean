import Flapjack.RiscV.Encoding
import Flapjack.RiscV.Encoding.Reference

/-! Unconditional production/native encoding agreement. These infrastructure
relations compare distinct Lean carriers and do not narrow the full tagged HOL
encoder. No target-run or operand-validity premise is introduced. -/
namespace Flapjack.RiscV

/-- Universal byte-order agreement for the full native instruction carrier.
This follows the existing Flapjack byte-slice theorem; it makes no claim about
production word encoding or cross-language equivalence. No HOL original names
this relation between the two Lean byte emitters, so it stays untagged. -/
theorem nativeEncodeBytes (i : L3.instruction) :
    encodeWordBytes (L3.Encode i) =
      Compiler.Encoders.RiscV.Target.riscvEncode i := by
  rw [encodeWordBytes_eq_extracts]
  simp only [Compiler.Encoders.RiscV.Target.riscvEncode, List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [L3.holWordExtract, BitVec.extractLsb']


private theorem appendNumeric (x : BitVec m) (y : BitVec n) :
    (x ++ y).toNat = x.toNat * 2 ^ n + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

private theorem rtypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (d a b : BitVec 5) (f7 : BitVec 7) :
    L3.Rtype (o,f3,d,a,b,f7) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + f3.toNat * 4096 +
        a.toNat * 32768 + b.toNat * 1048576 + f7.toNat * 33554432) := by
  apply BitVec.eq_of_toNat_eq
  change (f7 ++ (b ++ (a ++ (f3 ++ (d ++ o))))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega

private theorem itypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (d a : BitVec 5) (i : BitVec 12) :
    L3.Itype (o,f3,d,a,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + f3.toNat * 4096 +
        a.toNat * 32768 + i.toNat * 1048576) := by
  apply BitVec.eq_of_toNat_eq
  change (i ++ (a ++ (f3 ++ (d ++ o)))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  omega

private theorem utypeNumeric (o : BitVec 7) (d : BitVec 5) (i : BitVec 20) :
    L3.Utype (o,d,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 + i.toNat * 4096) := by
  apply BitVec.eq_of_toNat_eq
  change (i ++ (d ++ o)).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  omega

private theorem encodeRNative (o : BitVec 7) (f3 : BitVec 3)
    (f7 : BitVec 7) (d a b : Fin 32) :
    EncodingReference.encodeR o.toNat f3.toNat f7.toNat d a b =
      L3.Rtype (o,f3,nativeRegister d,nativeRegister a,nativeRegister b,f7) := by
  rw [rtypeNumeric]
  simp [EncodingReference.encodeR, EncodingReference.encodeWord32, EncodingReference.registerBits, nativeRegister_toNat]

private theorem encodeINative (o : BitVec 7) (f3 : BitVec 3)
    (d a : Fin 32) (i : BitVec width) :
    EncodingReference.encodeI o.toNat f3.toNat d a i =
      L3.Itype (o,f3,nativeRegister d,nativeRegister a,i.setWidth 12) := by
  rw [itypeNumeric]
  simp [EncodingReference.encodeI, EncodingReference.encodeIValue, EncodingReference.encodeWord32, EncodingReference.lowBits, EncodingReference.registerBits, nativeRegister_toNat]

private theorem encodeUNative (o : BitVec 7) (d : Fin 32) (i : BitVec width) :
    EncodingReference.encodeU o.toNat d i = L3.Utype (o,nativeRegister d,i.setWidth 20) := by
  rw [utypeNumeric]
  simp [EncodingReference.encodeU, EncodingReference.encodeWord32, EncodingReference.lowBits, EncodingReference.registerBits, nativeRegister_toNat]

private theorem stypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (a b : BitVec 5) (i : BitVec 12) :
    L3.Stype (o,f3,a,b,i) =
      BitVec.ofNat 32 (o.toNat + (i.toNat / 32 % 128) * 33554432 +
        b.toNat * 1048576 + a.toNat * 32768 + f3.toNat * 4096 +
        (i.toNat % 32) * 128) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holWordExtract 7 11 5 i) ++
    (b ++ (a ++ (f3 ++ ((L3.holWordExtract 5 4 0 i) ++ o))))).toNat = _
  simp only [appendNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

private theorem encodeSNative (f3 : BitVec 3) (b a : Fin 32) (i : BitVec width) :
    EncodingReference.encodeS f3.toNat b a i =
      L3.Stype (0x23,f3,nativeRegister a,nativeRegister b,i.setWidth 12) := by
  rw [stypeNumeric]
  simp [EncodingReference.encodeS, EncodingReference.encodeWord32, EncodingReference.lowBits, EncodingReference.registerBits, nativeRegister_toNat]

private theorem singletonV2w (b : Bool) : L3.holV2w 1 [b] = BitVec.ofBool b := by
  cases b <;> decide

private theorem bitNumeric (w : BitVec m) (n : Nat) :
    (L3.holV2w 1 [w.getLsbD n]).toNat = w.toNat / 2 ^ n % 2 := by
  rw [singletonV2w, BitVec.toNat_ofBool]
  by_cases h : w.toNat / 2 ^ n % 2 = 1
  · simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h]
  · simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, h]
    omega

private theorem sbtypeNumeric (o : BitVec 7) (f3 : BitVec 3)
    (a b : BitVec 5) (i : BitVec 12) :
    L3.SBtype (o,f3,a,b,i) =
      BitVec.ofNat 32 (o.toNat + (i.toNat / 2048 % 2) * 2147483648 +
        (i.toNat / 16 % 64) * 33554432 + b.toNat * 1048576 +
        a.toNat * 32768 + f3.toNat * 4096 + (i.toNat % 16) * 256 +
        (i.toNat / 1024 % 2) * 128) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holV2w 1 [i.getLsbD 11]) ++
    ((L3.holWordExtract 6 9 4 i) ++ (b ++ (a ++ (f3 ++
      ((L3.holWordExtract 4 3 0 i) ++ ((L3.holV2w 1 [i.getLsbD 10]) ++ o))))))).toNat = _
  simp only [appendNumeric, bitNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

private theorem opcLoad : L3.opc (BitVec.ofNat 8 0) = BitVec.ofNat 7 3 := by decide
private theorem opcStore : L3.opc (BitVec.ofNat 8 8) = BitVec.ofNat 7 35 := by decide

private theorem encodeBNative {width : Nat} [NeZero width] (f3 : BitVec 3) (a b : Fin 32) (i : BitVec width) :
    EncodingReference.encodeB f3.toNat a b i =
      L3.SBtype (0x63,f3,nativeRegister a,nativeRegister b,(i >>> 1).setWidth 12) := by
  rw [sbtypeNumeric]
  apply BitVec.eq_of_toNat_eq
  simp [EncodingReference.encodeB, EncodingReference.encodeWord32, EncodingReference.lowBits, EncodingReference.registerBits, nativeRegister_toNat,
    Nat.shiftRight_eq_div_pow]
  have hmod : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))
  simp only [hmod, Nat.reducePow]
  simp only [Nat.mod_mul_right_div_self i.toNat 4096 2,
    Nat.mod_mul_right_div_self i.toNat 32 256,
    Nat.mod_mul_right_div_self i.toNat 2 4096,
    Nat.mod_mul_right_div_self i.toNat 2048 4,
    Nat.mod_mul_right_div_self (i.toNat / 2) 2048 2,
    Nat.mod_mul_right_div_self (i.toNat / 2) 16 256,
    Nat.mod_mul_right_div_self (i.toNat / 2) 1024 4]
  simp [Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4),
    Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 256)]

private theorem ujtypeNumeric (o : BitVec 7) (d : BitVec 5) (i : BitVec 20) :
    L3.UJtype (o,d,i) =
      BitVec.ofNat 32 (o.toNat + d.toNat * 128 +
        (i.toNat / 2048 % 256) * 4096 + (i.toNat / 1024 % 2) * 1048576 +
        (i.toNat % 1024) * 2097152 + (i.toNat / 524288 % 2) * 2147483648) := by
  apply BitVec.eq_of_toNat_eq
  change ((L3.holV2w 1 [i.getLsbD 19]) ++
    ((L3.holWordExtract 10 9 0 i) ++ ((L3.holV2w 1 [i.getLsbD 10]) ++
      ((L3.holWordExtract 8 18 11 i) ++ (d ++ o))))).toNat = _
  simp only [appendNumeric, bitNumeric, BitVec.toNat_ofNat, Nat.reducePow]
  simp [L3.holWordExtract, Nat.shiftRight_eq_div_pow]
  omega

private theorem encodeJNative {width : Nat} [NeZero width] (d : Fin 32) (i : BitVec width) :
    EncodingReference.encodeJ d i =
      L3.UJtype (0x6f,nativeRegister d,(i >>> 1).setWidth 20) := by
  rw [ujtypeNumeric]
  apply BitVec.eq_of_toNat_eq
  simp [EncodingReference.encodeJ, EncodingReference.encodeWord32, EncodingReference.lowBits, EncodingReference.registerBits, nativeRegister_toNat,
    Nat.shiftRight_eq_div_pow]
  have hmod : 1 % 2 ^ width = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (NeZero.ne width))
  simp only [hmod, Nat.reducePow]
  simp only [Nat.mod_mul_right_div_self i.toNat 4096 512,
    Nat.mod_mul_right_div_self i.toNat 2048 1024,
    Nat.mod_mul_right_div_self i.toNat 2 1048576,
    Nat.mod_mul_right_div_self i.toNat 1048576 2,
    Nat.mod_mul_right_div_self (i.toNat / 2) 2048 512,
    Nat.mod_mul_right_div_self (i.toNat / 2) 1024 1024,
    Nat.mod_mul_right_div_self (i.toNat / 2) 524288 2]
  simp [Nat.div_div_eq_div_mul, Nat.mod_mod_of_dvd _ (by decide : 256 ∣ 512),
    Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 1024),
    Nat.mod_mod_of_dvd _ (by decide : 1024 ∣ 1048576)]

/-- Universal agreement on the entire production RV64 carrier. It stays
untagged because that carrier is Flapjack-specific. Every constructor and
arbitrary register/word64 operand is retained, without validity or target-run
premises. This does not claim equivalence of execution semantics. -/
theorem encodeInstructionWeighted_native (i : Instruction 64) :
    EncodingReference.encodeInstructionWeighted i = L3.Encode (nativeInstruction i) := by
  cases i with
  | add d a b => exact encodeRNative 51 0 0 d a b
  | sub d a b => exact encodeRNative 51 0 32 d a b
  | addW d a b => exact encodeRNative 59 0 0 d a b
  | subW d a b => exact encodeRNative 59 0 32 d a b
  | and d a b => exact encodeRNative 51 7 0 d a b
  | or d a b => exact encodeRNative 51 6 0 d a b
  | xor d a b => exact encodeRNative 51 4 0 d a b
  | addi d a i => exact encodeINative 19 0 d a i
  | addiW d a i => exact encodeINative 27 0 d a i
  | andi d a i => exact encodeINative 19 7 d a i
  | ori d a i => exact encodeINative 19 6 d a i
  | xori d a i => exact encodeINative 19 4 d a i
  | mul d a b => exact encodeRNative 51 0 1 d a b
  | mulW d a b => exact encodeRNative 59 0 1 d a b
  | mulHU d a b => exact encodeRNative 51 3 1 d a b
  | sll d a b => exact encodeRNative 51 1 0 d a b
  | srl d a b => exact encodeRNative 51 5 0 d a b
  | sra d a b => exact encodeRNative 51 5 32 d a b
  | sllW d a b => exact encodeRNative 59 1 0 d a b
  | srlW d a b => exact encodeRNative 59 5 0 d a b
  | sraW d a b => exact encodeRNative 59 5 32 d a b
  | slt d a b => exact encodeRNative 51 2 0 d a b
  | sltu d a b => exact encodeRNative 51 3 0 d a b
  | divU d a b => exact encodeRNative 51 4 1 d a b
  | remU d a b => exact encodeRNative 51 7 1 d a b
  | slti d a i => exact encodeINative 19 2 d a i
  | sltiu d a i => exact encodeINative 19 3 d a i
  | lui d i => exact encodeUNative 55 d i
  | auipc d i => exact encodeUNative 23 d i
  | branchEq a b i => exact encodeBNative 0 a b i
  | branchNe a b i => exact encodeBNative 1 a b i
  | branchLt a b i => exact encodeBNative 4 a b i
  | branchGe a b i => exact encodeBNative 5 a b i
  | branchLtU a b i => exact encodeBNative 6 a b i
  | branchGeU a b i => exact encodeBNative 7 a b i
  | jal d i => exact encodeJNative d i
  | jalr d a i => exact encodeINative 103 0 d a i
  | ecall => rfl
  | loadByte d a => exact encodeINative 3 4 d a (0 : BitVec 64)
  | loadByteSigned d a => exact encodeINative 3 0 d a (0 : BitVec 64)
  | storeByte d a => exact encodeSNative 0 d a (0 : BitVec 64)
  | loadHalf d a => exact encodeINative 3 5 d a (0 : BitVec 64)
  | loadHalfSigned d a => exact encodeINative 3 1 d a (0 : BitVec 64)
  | storeHalf d a => exact encodeSNative 1 d a (0 : BitVec 64)
  | load32 d a => exact encodeINative 3 6 d a (0 : BitVec 64)
  | store32 d a => exact encodeSNative 2 d a (0 : BitVec 64)
  | loadWord d a => exact encodeINative 3 3 d a (0 : BitVec 64)
  | storeWord d a => exact encodeSNative 3 d a (0 : BitVec 64)
  | loadWordOffset d a i => exact encodeINative 3 3 d a i
  | storeWordOffset d a i => exact encodeSNative 3 d a i
  | loadByteOffset d a i => exact encodeINative 3 4 d a i
  | storeByteOffset d a i => exact encodeSNative 0 d a i
  | loadHalfOffset d a i => exact encodeINative 3 5 d a i
  | storeHalfOffset d a i => exact encodeSNative 1 d a i
  | load32Offset d a i => exact encodeINative 3 6 d a i
  | store32Offset d a i => exact encodeSNative 2 d a i
  | slli d a i | srli d a i | srai d a i
  | slliW d a i | srliW d a i | sraiW d a i =>
      apply BitVec.eq_of_toNat_eq
      simp [nativeInstruction, nativeInstructionAtWidth, EncodingReference.encodeInstructionWeighted, L3.Encode, itypeNumeric,
        EncodingReference.encodeIValue, EncodingReference.encodeWord32, shiftAmount, EncodingReference.registerBits, nativeRegister_toNat,
        L3.opc, L3.holWordExtract]
      rw [appendNumeric]
      simp
      omega

/-- Every generic diagnostic outcome is preserved by native format emission.
This is an unconditional migration relation, not a HOL port at other widths. -/
theorem encodeInstructionDiagnostic_eq_weighted {width : Nat} [NeZero width]
    (i : Instruction width) :
    encodeInstructionDiagnostic i = EncodingReference.encodeInstructionWeighted i := by
  cases i with
  | add d a b => exact (encodeRNative 51 0 0 d a b).symm
  | sub d a b => exact (encodeRNative 51 0 32 d a b).symm
  | addW d a b => exact (encodeRNative 59 0 0 d a b).symm
  | subW d a b => exact (encodeRNative 59 0 32 d a b).symm
  | and d a b => exact (encodeRNative 51 7 0 d a b).symm
  | or d a b => exact (encodeRNative 51 6 0 d a b).symm
  | xor d a b => exact (encodeRNative 51 4 0 d a b).symm
  | addi d a i => exact (encodeINative 19 0 d a i).symm
  | addiW d a i => exact (encodeINative 27 0 d a i).symm
  | andi d a i => exact (encodeINative 19 7 d a i).symm
  | ori d a i => exact (encodeINative 19 6 d a i).symm
  | xori d a i => exact (encodeINative 19 4 d a i).symm
  | mul d a b => exact (encodeRNative 51 0 1 d a b).symm
  | mulW d a b => exact (encodeRNative 59 0 1 d a b).symm
  | mulHU d a b => exact (encodeRNative 51 3 1 d a b).symm
  | sll d a b => exact (encodeRNative 51 1 0 d a b).symm
  | srl d a b => exact (encodeRNative 51 5 0 d a b).symm
  | sra d a b => exact (encodeRNative 51 5 32 d a b).symm
  | sllW d a b => exact (encodeRNative 59 1 0 d a b).symm
  | srlW d a b => exact (encodeRNative 59 5 0 d a b).symm
  | sraW d a b => exact (encodeRNative 59 5 32 d a b).symm
  | slt d a b => exact (encodeRNative 51 2 0 d a b).symm
  | sltu d a b => exact (encodeRNative 51 3 0 d a b).symm
  | divU d a b => exact (encodeRNative 51 4 1 d a b).symm
  | remU d a b => exact (encodeRNative 51 7 1 d a b).symm
  | slti d a i => exact (encodeINative 19 2 d a i).symm
  | sltiu d a i => exact (encodeINative 19 3 d a i).symm
  | lui d i => exact (encodeUNative 55 d i).symm
  | auipc d i => exact (encodeUNative 23 d i).symm
  | branchEq a b i => exact (encodeBNative 0 a b i).symm
  | branchNe a b i => exact (encodeBNative 1 a b i).symm
  | branchLt a b i => exact (encodeBNative 4 a b i).symm
  | branchGe a b i => exact (encodeBNative 5 a b i).symm
  | branchLtU a b i => exact (encodeBNative 6 a b i).symm
  | branchGeU a b i => exact (encodeBNative 7 a b i).symm
  | jal d i => exact (encodeJNative d i).symm
  | jalr d a i => exact (encodeINative 103 0 d a i).symm
  | ecall => rfl
  | loadByte d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 4 d a (0 : BitVec width)).symm
  | loadByteSigned d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 0 d a (0 : BitVec width)).symm
  | storeByte d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcStore]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeSNative 0 d a (0 : BitVec width)).symm
  | loadHalf d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 5 d a (0 : BitVec width)).symm
  | loadHalfSigned d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 1 d a (0 : BitVec width)).symm
  | storeHalf d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcStore]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeSNative 1 d a (0 : BitVec width)).symm
  | load32 d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 6 d a (0 : BitVec width)).symm
  | store32 d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcStore]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeSNative 2 d a (0 : BitVec width)).symm
  | loadWord d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcLoad]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeINative 3 3 d a (0 : BitVec width)).symm
  | storeWord d a =>
      simp only [encodeInstructionDiagnostic, nativeInstructionAtWidth, L3.Encode]
      rw [opcStore]
      simpa [EncodingReference.encodeInstructionWeighted, EncodingReference.encodeI, EncodingReference.lowBits] using (encodeSNative 3 d a (0 : BitVec width)).symm
  | loadWordOffset d a i => exact (encodeINative 3 3 d a i).symm
  | storeWordOffset d a i => exact (encodeSNative 3 d a i).symm
  | loadByteOffset d a i => exact (encodeINative 3 4 d a i).symm
  | storeByteOffset d a i => exact (encodeSNative 0 d a i).symm
  | loadHalfOffset d a i => exact (encodeINative 3 5 d a i).symm
  | storeHalfOffset d a i => exact (encodeSNative 1 d a i).symm
  | load32Offset d a i => exact (encodeINative 3 6 d a i).symm
  | store32Offset d a i => exact (encodeSNative 2 d a i).symm
  | slli d a i | srli d a i | srai d a i
  | slliW d a i | srliW d a i | sraiW d a i =>
      simp only [encodeInstructionDiagnostic, EncodingReference.encodeInstructionWeighted]
      rw [itypeNumeric]
      simp [EncodingReference.encodeIValue, EncodingReference.encodeWord32,
        EncodingReference.registerBits, nativeRegister_toNat]

/-- All existing diagnostic widths retain exactly their previous word output. -/
theorem encodeInstruction_eq_weighted {width : Nat} [NeZero width]
    (i : Instruction width) :
    encodeInstruction i = EncodingReference.encodeInstructionWeighted i := by
  unfold encodeInstruction
  split
  · subst width
    exact (encodeInstructionWeighted_native i).symm
  · exact encodeInstructionDiagnostic_eq_weighted i

/-- The executed RV64 word encoder uses the full native encoder directly. -/
theorem encodeInstruction_native (i : Instruction 64) :
    encodeInstruction i = L3.Encode (nativeInstruction i) := by
  simp [encodeInstruction]

/-- Unconditional byte agreement follows from whole-carrier word agreement
and the full native byte-order theorem. This is Flapjack carrier infrastructure
with no separate HOL declaration. -/
theorem encodeInstructionBytes_native (i : Instruction 64) :
    encodeInstructionBytes i =
      Compiler.Encoders.RiscV.Target.riscvEncode (nativeInstruction i) := by
  simp [encodeInstructionBytes]

/-- List agreement for every production instruction sequence, without a
successful execution or input-validity premise. There is no HOL original
for this relation between the distinct Lean carriers. -/
theorem encodeInstructions_native (instructions : List (Instruction 64)) :
    encodeInstructions instructions = instructions.flatMap
      (fun i => Compiler.Encoders.RiscV.Target.riscvEncode (nativeInstruction i)) := by
  induction instructions with
  | nil => rfl
  | cons i rest ih =>
      simp only [encodeInstructions, List.flatMap_cons, encodeInstructionBytes_native, ih]


/-- Numerical byte emission is retained only as a non-executable proof reference. -/
theorem encodeWordBytes_eq_weighted (value : BitVec 32) :
    encodeWordBytes value = EncodingReference.encodeWordBytesWeighted value := by
  simp only [encodeWordBytes, EncodingReference.encodeWordBytesWeighted,
    List.cons.injEq, and_true]
  repeat' apply And.intro
  all_goals
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- Every diagnostic width emits the bytes of its public word encoder. -/
theorem encodeInstructionBytes_eq_word [NeZero width] (i : Instruction width) :
    encodeInstructionBytes i = encodeWordBytes (encodeInstruction i) := by
  unfold encodeInstructionBytes encodeInstruction
  split
  · subst width
    exact (nativeEncodeBytes (nativeInstruction i)).symm
  · rfl

/-- Unconditional preservation of historical bytes at every diagnostic width. -/
theorem encodeInstructionBytes_eq_weighted [NeZero width] (i : Instruction width) :
    encodeInstructionBytes i = EncodingReference.encodeWordBytesWeighted
      (EncodingReference.encodeInstructionWeighted i) := by
  rw [encodeInstructionBytes_eq_word, encodeInstruction_eq_weighted,
    encodeWordBytes_eq_weighted]

/-- Arbitrary instruction lists retain their complete emitted byte sequence. -/
theorem encodeInstructions_eq_weighted [NeZero width] (xs : List (Instruction width)) :
    encodeInstructions xs = xs.flatMap (fun i =>
      EncodingReference.encodeWordBytesWeighted (EncodingReference.encodeInstructionWeighted i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [encodeInstructions, List.flatMap_cons, encodeInstructionBytes_eq_weighted, ih]

end Flapjack.RiscV
