/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Flapjack.Compiler.Encoders.Arm8.Machine.Execute

/-!
# ARMv8 decoder inverses

This module records the first kernel-checked decoder inverse for the closed
ARMv8 model.  The full per-instruction inverse is future work; the existing
`decodeInsn`/`encodeInsn` bridge is deliberately stated with explicit
hypotheses on the fetched word.
-/

namespace Flapjack.Compiler.Encoders.Arm8

/-- A 32-bit `ofNat` is the width-`n` truncation zero-extended to 32 bits. -/
theorem ofNat_mod_self32 (x n : Nat) :
    BitVec.ofNat 32 (x % 2 ^ n) = (BitVec.ofNat n x).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- `part` of a word is the `toNat` of the corresponding width-typed slice. -/
theorem part_eq_of_setWidth {w : BitVec 32} {lo len : Nat} {x : BitVec len}
    (h : (w >>> lo).setWidth len = x) : part w lo len = x.toNat := by
  unfold part
  rw [h]

/-- The 32-bit encoding of `noOp` decodes back to `noOp`. -/
theorem decode_encode_noOp32 :
    decodeInsn32 (fields [(24, 0xD50320), (3, 0), (5, 31)]) = some .noOp := by
  decide

/-- The 64-bit carrier encoding of `noOp`. -/
theorem encodeInsn_noOp :
    encodeInsn .noOp = some ((fields [(24, 0xD50320), (3, 0), (5, 31)]).setWidth 64) := rfl

end Flapjack.Compiler.Encoders.Arm8
