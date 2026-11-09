module

public import Mathlib.Tactic
public import Flapjack.Compiler.Encoders.X64.Machine.EncodingProof
public import Flapjack.Compiler.Encoders.X64.Machine.Target
public import Flapjack.Compiler.Encoders.AsmProps.Encoding

-- Sum `==` must reduce by `rfl`/`decide`; core's derived instance is not exposed.
import all Init.Data.Sum.Basic
@[expose] public section

/-!
# Structural facts about the closed x86-64 target

This module proves `enc_ok` and the projection-consistency half of `target_ok`
for the closed x86-64 target.  The transition simulation is developed
separately.
-/

set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.X64

open Flapjack Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-! ## Helper lengths -/

/-- `e_ModRM` for a register operand always produces one `ModRM` byte. -/
theorem eModRM_zr (r : BitVec 4) (dst : Nat) :
    eModRM r (.zr dst) =
      some (mkRex false (r.toNat / 8 = 1) false ((dst % 16) / 8 = 1),
        [byte (0xC0 ||| ((r.toNat % 8) <<< 3) ||| ((dst % 16) % 8))]) := by
  simp [eModRM]

/-- A REX prefix with the `W` bit set is one byte. -/
theorem rexPrefix_or_eight_length (rex : BitVec 4) :
    (rexPrefix (rex ||| BitVec.ofNat 4 8)).length = 1 := by
  revert rex
  decide

/-- `e_opsize` for a 64-bit operation prefixes one REX byte and sets `v = 1`. -/
theorem eOpsize_z64 (rex : BitVec 4) :
    eOpsize .z64 rex = (rexPrefix (rex ||| BitVec.ofNat 4 8), 1) := by
  simp [eOpsize]

/-- `e_opsize_imm` for a 64-bit operation with a normal (sign-extended
32-bit) immediate yields one prefix byte, `v = 1`, and four immediate bytes. -/
theorem eOpsizeImm_z64 (rex : BitVec 4) (imm : BitVec 64)
    (h1 : -(2^31 : Int) ≤ imm.toInt) (h2 : imm.toInt ≤ 2^31 - 1) :
    eOpsizeImm .z64 rex imm true =
      some (rexPrefix (rex ||| BitVec.ofNat 4 8), 1,
        [byte imm.toNat, byte (imm.toNat / 2 ^ 8), byte (imm.toNat / 2 ^ 16),
          byte (imm.toNat / 2 ^ 24)]) := by
  simp only [eOpsizeImm, eOpsize_z64]
  simp only [decide_true, Bool.true_and, if_true]
  have he : eImm32 imm = some [byte imm.toNat, byte (imm.toNat / 2 ^ 8),
      byte (imm.toNat / 2 ^ 16), byte (imm.toNat / 2 ^ 24)] := by
    simp only [eImm32]
    rw [if_pos ⟨h1, h2⟩]
  simp only [he]

/-- `e_imm8` is defined exactly on the signed eight-bit range. -/
theorem eImm8_some {imm : BitVec 64} (h : -128 ≤ imm.toInt ∧ imm.toInt ≤ 127) :
    eImm8 imm = some [byte imm.toNat] := by
  simp only [eImm8]
  rw [if_pos h]

/-- A successful `e_imm8` has one byte. -/
theorem eImm8_length {imm : BitVec 64} {l : List (BitVec 8)} (h : eImm8 imm = some l) :
    l.length = 1 := by
  unfold eImm8 at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp
  · simp at h

/-! ## `Inst` lengths -/

/-- A `binopRR` over the emitted register forms is three bytes. -/
theorem encodeInsn_binopRR_length (op : ZBinopName) (dst src : Nat)
    (hshift : op ≠ .ztest → op.code / 8 = 1 → src % 16 = 1) :
    (encodeInsn (.binopRR op .z64 dst src)).length = 3 := by
  simp only [encodeInsn]
  by_cases ht : op = .ztest
  · simp only [ht, if_true]
    simp only [eGenRmReg, eModRM_zr]
    simp [eOpsize_z64, rexPrefix_or_eight_length]
  · simp only [ht, if_false]
    by_cases hs : op.code / 8 = 1
    · have h1 : src % 16 = 1 := hshift ht hs
      simp only [hs, h1, if_true]
      simp only [eGenRmReg, eModRM_zr]
      simp [eOpsize_z64, rexPrefix_or_eight_length]
    · simp only [hs, if_false]
      simp only [eGenRmReg, eModRM_zr]
      simp [eOpsize_z64, rexPrefix_or_eight_length]

/-- A `binopRI` over the emitted forms has a length determined by the opcode
and the register/immediate shape. -/
theorem encodeInsn_binopRI_length (op : ZBinopName) (dst : Nat) (imm : BitVec 64)
    (himm : -(2^31 : Int) ≤ imm.toInt ∧ imm.toInt ≤ 2^31 - 1)
    (hshift : op ≠ .ztest → op.code / 8 = 1 → (eImm8 imm).isSome = true) :
    (encodeInsn (.binopRI op .z64 dst imm)).length =
      if op = .ztest then (if dst % 16 = 0 then 6 else 7)
      else if op.code / 8 = 1 then (if imm = 1 then 3 else 4)
      else if (eImm8 imm).isSome then 4
      else if dst % 16 = 0 then 6
      else 7 := by
  simp only [encodeInsn]
  by_cases ht : op = .ztest
  · simp only [ht, if_true]
    by_cases hrax : dst % 16 = 0
    · simp only [isRax, hrax, if_true]
      simp only [eRaxImm, eOpsizeImm_z64 _ imm himm.1 himm.2]
      simp [rexPrefix, BitVec.toNat_ofNat]
    · simp only [isRax, hrax, if_false]
      simp only [eRmImm, eModRM_zr, eOpsizeImm_z64 _ imm himm.1 himm.2]
      simp [rexPrefix_or_eight_length]
  · simp only [ht, if_false]
    by_cases hsh : op.code / 8 = 1
    · by_cases h1 : imm = 1
      · simp only [hsh, h1, if_true]
        simp only [eGenRmReg, eModRM_zr]
        simp [eOpsize_z64, rexPrefix_or_eight_length]
      · have h8 : (eImm8 imm).isSome = true := hshift ht hsh
        simp only [hsh, h1, if_false]
        simp only [eRmImm8, eModRM_zr]
        cases he : eImm8 imm
        · simp [he] at h8
        · rename_i l
          have hl : l.length = 1 := eImm8_length he
          simp [hl, eOpsize_z64, rexPrefix_or_eight_length]
    · simp only [hsh, if_false]
      have hnb : notByte .z64 = true := rfl
      simp only [hnb]
      by_cases h8 : (eImm8 imm).isSome
      · simp only [h8, if_true]
        simp only [eRmImm8, eModRM_zr]
        cases he : eImm8 imm
        · simp [he] at h8
        · rename_i l
          have hl : l.length = 1 := eImm8_length he
          simp [hl, eOpsize_z64, rexPrefix_or_eight_length]
      · simp only [h8]
        by_cases hrax : dst % 16 = 0
        · simp only [isRax, hrax, if_true]
          simp only [eRaxImm, eOpsizeImm_z64 _ imm himm.1 himm.2]
          simp [rexPrefix, BitVec.toNat_ofNat]
        · simp only [isRax, hrax, if_false]
          simp only [eRmImm, eModRM_zr, eOpsizeImm_z64 _ imm himm.1 himm.2]
          simp [rexPrefix_or_eight_length]

/-! ## Conditional-jump offset range -/

/-- The range facts `asm_ok` gives a `jumpCmp` target. -/
theorem cjump_offset_range (w : BitVec 64)
    (h : asmCjumpOffsetOkExact x64Config w = true) :
    (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt ∧
      w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt := by
  simp only [asmCjumpOffsetOkExact, asmOffsetOkExact, x64Config, Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1.1, of_decide_eq_true h.1.2⟩

/-- A `jumpCmp` target shifted by `-9` lies in the signed 32-bit range. -/
theorem cjump_offset_sub_nine (w : BitVec 64)
    (hlo : (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 9).toInt ∧ (w - 9).toInt < 2^31 := by
  have hlo' : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by decide
  have hhi' : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 9 : BitVec 64).toInt = w.toInt - 9 := by
    rw [BitVec.toInt_sub]
    have h9 : ((9 : BitVec 64).toInt : Int) = 9 := by decide
    rw [h9]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-- A `jumpCmp` target shifted by `-10` lies in the signed 32-bit range. -/
theorem cjump_offset_sub_ten (w : BitVec 64)
    (hlo : (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 10).toInt ∧ (w - 10).toInt < 2^31 := by
  have hlo' : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by decide
  have hhi' : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 10 : BitVec 64).toInt = w.toInt - 10 := by
    rw [BitVec.toInt_sub]
    have h10 : ((10 : BitVec 64).toInt : Int) = 10 := by decide
    rw [h10]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-- A `jumpCmp` target shifted by `-12` lies in the signed 32-bit range. -/
theorem cjump_offset_sub_twelve (w : BitVec 64)
    (hlo : (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 12).toInt ∧ (w - 12).toInt < 2^31 := by
  have hlo' : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by decide
  have hhi' : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 12 : BitVec 64).toInt = w.toInt - 12 := by
    rw [BitVec.toInt_sub]
    have h12 : ((12 : BitVec 64).toInt : Int) = 12 := by decide
    rw [h12]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-- A `jumpCmp` target shifted by `-13` lies in the signed 32-bit range. -/
theorem cjump_offset_sub_thirteen (w : BitVec 64)
    (hlo : (x64Min32 + 13 : BitVec 64).toInt ≤ w.toInt)
    (hhi : w.toInt ≤ (x64Max32 + 5 : BitVec 64).toInt) :
    -(2^31 : Int) ≤ (w - 13).toInt ∧ (w - 13).toInt < 2^31 := by
  have hlo' : (x64Min32 + 13 : BitVec 64).toInt = -(2^31 : Int) + 13 := by decide
  have hhi' : (x64Max32 + 5 : BitVec 64).toInt = (2^31 : Int) - 1 + 5 := by decide
  rw [hlo'] at hlo
  rw [hhi'] at hhi
  have htoInt : (w - 13 : BitVec 64).toInt = w.toInt - 13 := by
    rw [BitVec.toInt_sub]
    have h13 : ((13 : BitVec 64).toInt : Int) = 13 := by decide
    rw [h13]
    rw [Int.bmod_def]
    norm_num
    omega
  rw [htoInt]
  omega

/-! ## `x64_enc` of a nonempty lowering -/

/-- `x64_enc` returns the concatenated bytes when the lowering is nonempty. -/
theorem x64Enc_of_flatMap (i : HolAsm 64) (l : List (BitVec 8))
    (h : (x64Ast i).flatMap encodeInsn = l) (hl : l ≠ []) : x64Enc i = l := by
  unfold x64Enc
  rw [h]
  cases l with
  | nil => simp at hl
  | cons x xs => rfl

/-! ## Conditional-jump lengths -/

/-- `total_num2Zreg` is the identity on valid register numbers. -/
theorem totalNum2Zreg_eq (n : Nat) (h : n < 16) : totalNum2Zreg n = n := by
  simp only [totalNum2Zreg, num2Zreg]
  rw [if_pos h, Nat.mod_eq_of_lt h]

/-- A `binopRI` comparison plus its six-byte branch is the width the lowering
subtracts. -/
theorem binopRI_jumpCmp_length (operator : Cmp) (source : Nat) (value : BitVec 64)
    (hsrc : source < 16)
    (himm : -(2^31 : Int) ≤ value.toInt ∧ value.toInt ≤ 2^31 - 1) :
    (encodeInsn (.binopRI (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) value)).length + 6 =
      (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
       else if source % 16 = 0 then 12 else 13) := by
  have htn : totalNum2Zreg source % 16 = source % 16 := by
    rw [totalNum2Zreg_eq source hsrc, Nat.mod_eq_of_lt hsrc]
  rw [encodeInsn_binopRI_length _ _ _ himm (by
    intro hne hc
    by_cases ht : isTest operator = true
    · simp only [ht, if_true] at hne
      exact absurd rfl hne
    · simp only [ht] at hc
      simp [ZBinopName.code] at hc)]
  rw [htn]
  by_cases ht : isTest operator = true
  · simp only [ht, if_true, Bool.not_true, Bool.false_and]
    by_cases hs : source % 16 = 0 <;> simp [hs]
  · simp only [ht, Bool.not_false, Bool.true_and]
    simp only [ZBinopName.code]
    by_cases h8 : (eImm8 value).isSome
    · have h8' : -128 ≤ value.toInt ∧ value.toInt ≤ 127 := by
        unfold eImm8 at h8
        split at h8
        · assumption
        · simp at h8
      simp [h8, h8']
    · have h8' : ¬(-128 ≤ value.toInt ∧ value.toInt ≤ 127) := by
        intro hr
        rw [eImm8_some hr] at h8
        simp at h8
      by_cases hs : source % 16 = 0 <;> simp [h8, h8', hs]

/-- The `jumpCmp` register form encodes to nine bytes under `asm_ok`. -/
theorem x64Enc_jumpCmp_reg_length (operator : Cmp) (source right : Nat) (target : BitVec 64)
    (h : asmOkExact (.jumpCmp operator source (.reg right) target) x64Config = true) :
    (x64Enc (.jumpCmp operator source (.reg right) target)).length = 9 := by
  have hok : asmCjumpOffsetOkExact x64Config target = true := by
    simp only [asmOkExact, Bool.and_eq_true] at h
    exact h.1
  obtain ⟨hlo, hhi⟩ := cjump_offset_range target hok
  have hr := cjump_offset_sub_nine target hlo hhi
  have hjcc : (encodeInsn (.jcc (x64Cmp operator) (target - 9))).length = 6 :=
    encodeInsn_jcc_long (x64Cmp operator) (target - 9)
      (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator) hr.1 hr.2
  have hbr : (encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
      (totalNum2Zreg source) (totalNum2Zreg right))).length = 3 := by
    apply encodeInsn_binopRR_length
    intro hne hc
    by_cases ht : isTest operator = true
    · simp only [ht, if_true] at hne
      exact absurd rfl hne
    · simp only [ht] at hc
      simp [ZBinopName.code] at hc
  have hfm : (x64Ast (.jumpCmp operator source (.reg right) target)).flatMap encodeInsn =
      encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) (totalNum2Zreg right)) ++
      encodeInsn (.jcc (x64Cmp operator) (target - 9)) := by
    simp [x64Ast]
  have hne : encodeInsn (.binopRR (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) (totalNum2Zreg right)) ++
      encodeInsn (.jcc (x64Cmp operator) (target - 9)) ≠ [] := by
    intro h'
    have := congrArg List.length h'
    simp [hbr] at this
  rw [x64Enc_of_flatMap _ _ hfm hne, List.length_append, hbr, hjcc]

/-- The `jumpCmp` immediate form encodes to the width the lowering subtracts. -/
theorem x64Enc_jumpCmp_imm_length (operator : Cmp) (source : Nat) (value target : BitVec 64)
    (hsrc : source < 16)
    (h : asmOkExact (.jumpCmp operator source (.imm value) target) x64Config = true) :
    (x64Enc (.jumpCmp operator source (.imm value) target)).length =
      (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
       else if source % 16 = 0 then 12 else 13) := by
  have hok : asmCjumpOffsetOkExact x64Config target = true := by
    simp only [asmOkExact, Bool.and_eq_true] at h
    exact h.1
  have hcmp : asmCmpOkExact operator source (.imm value) x64Config = true := by
    simp only [asmOkExact, Bool.and_eq_true] at h
    exact h.2
  have himm : -(2^31 : Int) ≤ value.toInt ∧ value.toInt ≤ 2^31 - 1 := by
    simp only [asmCmpOkExact, asmRegImmOkExact, x64Config, Bool.and_eq_true] at hcmp
    obtain ⟨_, hx⟩ := hcmp
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hx
    rcases hx with ⟨hxor, _⟩ | hv
    · have hf : (Sum.inr operator == Sum.inl BinOp.xor) = false := rfl
      rw [hf] at hxor
      simp at hxor
    · rw [x64Min32, x64Max32] at hv
      simp only [BitVec.toInt_ofInt] at hv
      exact of_decide_eq_true hv
  obtain ⟨hlo, hhi⟩ := cjump_offset_range target hok
  have hbr := binopRI_jumpCmp_length operator source value hsrc himm
  have hW : 10 ≤ (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
      else if source % 16 = 0 then 12 else 13) := by
    by_cases h8 : !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127
    · simp [h8]
    · by_cases hs : source % 16 = 0 <;> simp [h8, hs]
  have hjcc : (encodeInsn (.jcc (x64Cmp operator)
      (target - BitVec.ofNat 64 (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
        else if source % 16 = 0 then 12 else 13)))).length = 6 := by
    by_cases h8 : !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127
    · have hw : (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
          else if source % 16 = 0 then 12 else 13) = 10 := by simp [h8]
      rw [hw]
      exact encodeInsn_jcc_long (x64Cmp operator) (target - 10)
        (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
        (cjump_offset_sub_ten target hlo hhi).1 (cjump_offset_sub_ten target hlo hhi).2
    · by_cases hs : source % 16 = 0
      · have hw : (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
            else if source % 16 = 0 then 12 else 13) = 12 := by simp [h8, hs]
        rw [hw]
        exact encodeInsn_jcc_long (x64Cmp operator) (target - 12)
          (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
          (cjump_offset_sub_twelve target hlo hhi).1 (cjump_offset_sub_twelve target hlo hhi).2
      · have hw : (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
            else if source % 16 = 0 then 12 else 13) = 13 := by simp [h8, hs]
        rw [hw]
        exact encodeInsn_jcc_long (x64Cmp operator) (target - 13)
          (x64Cmp_ne_zP operator) (x64Cmp_ne_zAlways operator)
          (cjump_offset_sub_thirteen target hlo hhi).1 (cjump_offset_sub_thirteen target hlo hhi).2
  have hfm : (x64Ast (.jumpCmp operator source (.imm value) target)).flatMap encodeInsn =
      encodeInsn (.binopRI (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) value) ++
      encodeInsn (.jcc (x64Cmp operator)
        (target - BitVec.ofNat 64 (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
          else if source % 16 = 0 then 12 else 13))) := by
    simp [x64Ast]
  have hne : encodeInsn (.binopRI (if isTest operator then .ztest else .zcmp) .z64
        (totalNum2Zreg source) value) ++
      encodeInsn (.jcc (x64Cmp operator)
        (target - BitVec.ofNat 64 (if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
          else if source % 16 = 0 then 12 else 13))) ≠ [] := by
    intro h'
    have hlen := congrArg List.length h'
    rw [List.length_append] at hlen
    simp only [List.length_nil] at hlen
    omega
  rw [x64Enc_of_flatMap _ _ hfm hne, List.length_append]
  omega

/-- The `jumpCmp` length, uniform in the target offset. -/
theorem x64Enc_jumpCmp_length (operator : Cmp) (source : Nat) (ri : HolRegImm 64)
    (target : BitVec 64) (hsrc : source < 16)
    (h : asmOkExact (.jumpCmp operator source ri target) x64Config = true) :
    (x64Enc (.jumpCmp operator source ri target)).length =
      (match ri with
       | .reg _ => 9
       | .imm value =>
           if !isTest operator && -128 ≤ value.toInt && value.toInt ≤ 127 then 10
           else if source % 16 = 0 then 12 else 13) := by
  cases ri with
  | reg right => exact x64Enc_jumpCmp_reg_length operator source right target h
  | imm value => exact x64Enc_jumpCmp_imm_length operator source value target hsrc h

/-! ## `enc_ok` -/

/-- `enc_ok` for the closed x86-64 configuration. -/
theorem x64EncOk : encOk x64Config := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · intro instruction
    refine ⟨?_, ?_⟩
    · simp [x64Config, Nat.mod_one]
    · simpa [x64Config] using x64Enc_ne_nil instruction
  · intro w1 w2 hok
    simp only [x64Config_encode]
    constructor
    · intro _
      rw [x64Enc_jump_length w1 hok.1, x64Enc_jump_length w2 hok.2]
    · intro _
      rw [x64Enc_jump_length w1 hok.1, x64Enc_jump_length w2 hok.2]
  · intro cmp reg ri w1 w2 hok
    have hsrc : reg < 16 := by
      have hcmp : asmCmpOkExact cmp reg ri x64Config = true := by
        simp only [asmOkExact, Bool.and_eq_true] at hok
        exact hok.1.2
      simp only [asmCmpOkExact, asmRegOkExact, x64Config, Bool.and_eq_true] at hcmp
      exact of_decide_eq_true hcmp.1.1
    simp only [x64Config_encode]
    constructor
    · intro _
      rw [x64Enc_jumpCmp_length cmp reg ri w1 hsrc hok.1,
        x64Enc_jumpCmp_length cmp reg ri w2 hsrc hok.2]
      split <;> omega
    · intro _
      rw [x64Enc_jumpCmp_length cmp reg ri w1 hsrc hok.1,
        x64Enc_jumpCmp_length cmp reg ri w2 hsrc hok.2]
      split <;> omega
  · intro w1 w2 _
    constructor <;> intro _ <;> simp [x64Config, x64Enc_call_length]
  · intro w1 w2 reg hok
    simp only [x64Config_encode]
    constructor
    · intro _
      rw [x64Enc_loc_length reg w1 hok.1, x64Enc_loc_length reg w2 hok.2]
    · intro _
      rw [x64Enc_loc_length reg w1 hok.1, x64Enc_loc_length reg w2 hok.2]

/-! ## `target_ok` projection consistency -/

/-- Membership in the projected memory graph. -/
theorem x64Proj_memory (d : BitVec 64 → Prop) (s : X64State)
    (a : BitVec 64) (b : BitVec 8) :
    (x64Proj d s).2.2.2.2.2 (a, b) ↔ s.mem a = b ∧ d a := by
  exact SetSep.fun2SetThm s.mem d a b

/-- Projection consistency: equal projections give equal readable state. -/
theorem x64TargetOkProjection (ms1 ms2 : X64State) (s : AsmState 64)
    (h : x64Proj s.memDomain ms1 = x64Proj s.memDomain ms2) :
    (targetStateRel x64Target s ms1 ↔ targetStateRel x64Target s ms2) ∧
      x64StateOk ms1 = x64StateOk ms2 ∧
      ms1.pc = ms2.pc ∧
      (∀ a, s.memDomain a → ms1.mem a = ms2.mem a) := by
  have hpc : ms1.pc = ms2.pc := congrArg Prod.fst h
  have hregs : ms1.regs = ms2.regs := congrArg (fun p => p.2.1) h
  have hxmm : ms1.xmm = ms2.xmm := congrArg (fun p => p.2.2.1) h
  have hflags : ms1.flags = ms2.flags := congrArg (fun p => p.2.2.2.1) h
  have hfailed : ms1.failed = ms2.failed := congrArg (fun p => p.2.2.2.2.1) h
  have hmem : (x64Proj s.memDomain ms1).2.2.2.2.2 =
      (x64Proj s.memDomain ms2).2.2.2.2.2 := congrArg (fun p => p.2.2.2.2.2) h
  have hget (a : BitVec 64) (ha : s.memDomain a) : ms1.mem a = ms2.mem a := by
    have hleft : (x64Proj s.memDomain ms1).2.2.2.2.2 (a, ms1.mem a) := by
      rw [x64Proj_memory]
      exact ⟨rfl, ha⟩
    rw [congrFun hmem (a, ms1.mem a)] at hleft
    rw [x64Proj_memory] at hleft
    exact hleft.1.symm
  have hok : x64StateOk ms1 = x64StateOk ms2 := by
    simp only [x64StateOk, hfailed]
  refine ⟨?_, hok, hpc, hget⟩
  simp only [targetStateRel, x64Target_stateOk, x64Target_getPc, x64Target_getReg,
    x64Target_getByte, x64Target_getFpReg, x64Target_config, x64Config]
  constructor
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hok]; exact hok1
    · rw [← hpc]; exact hpc1
    · intro a ha; rw [← hget a ha]; exact hmem1 a ha
    · intro i hi; simp only [readReg]; rw [← hregs]; exact hreg1 i hi
    · intro i hi; simp only [readXmm]; rw [← hxmm]; exact hfp1 i hi
  · intro hs
    rcases hs with ⟨hok1, hpc1, hmem1, hreg1, hfp1⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hok]; exact hok1
    · rw [hpc]; exact hpc1
    · intro a ha; rw [hget a ha]; exact hmem1 a ha
    · intro i hi; simp only [readReg]; rw [hregs]; exact hreg1 i hi
    · intro i hi; simp only [readXmm]; rw [hxmm]; exact hfp1 i hi

/-- `target_ok` for the closed x86-64 target. -/
theorem x64TargetOk : targetOk x64Target := by
  refine ⟨x64EncOk, ?_⟩
  intro ms1 ms2 s hproj
  exact x64TargetOkProjection ms1 ms2 s hproj

end Flapjack.Compiler.Encoders.X64
