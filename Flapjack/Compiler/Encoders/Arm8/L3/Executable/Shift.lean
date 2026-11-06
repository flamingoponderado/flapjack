import Flapjack.Compiler.Encoders.Arm8.L3.Executable.Arith
import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfield

/-!
# Bitfield move: bytes for the L3 bridge

`Arm8.encodeInsn32` encodes `BitfieldMove` from the `(inzero, extend)` pair and
the two six-bit fields, and returns `none` when the pair has no opcode or a
field does not fit six bits.  The L3 `Encode` additionally requires the
`DecodeBitMasks` of those fields to succeed, which every `arm8_ast` call site
guarantees by pattern-matching on it.  This module proves `Arm8.encodeBytes`
equals `L3.arm8Encode` under that hypothesis.

No new HOL claim is introduced: the bridge relates two Lean renderings of the
same instruction word.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem

/-- The computable `bitfieldOpBits` is the L3 `arm8BitfieldOpc`. -/
theorem bitfieldOpBits_eq (inzero extend : Bool) (n : Nat)
    (h : bitfieldOpBits inzero extend = some n) :
    arm8BitfieldOpc inzero extend = some (BitVec.ofNat 2 n) := by
  unfold bitfieldOpBits at h
  cases inzero <;> cases extend <;> simp_all [arm8BitfieldOpc]

/-- `fields` builds the bitfield-move word. -/
theorem fields_bitfieldMove (opc immr imms rn rd : Nat) :
    fields [(1, 1), (2, opc), (6, 38), (1, 1), (6, immr), (6, imms), (5, rn), (5, rd)] =
      arm8BitfieldWord 1 (BitVec.ofNat 2 opc) (BitVec.ofNat 6 immr) (BitVec.ofNat 6 imms)
        (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, arm8BitfieldWord]
  rw [ofNat_mod_setWidth 1, ofNat_mod_setWidth 2, ofNat_mod_setWidth 6,
    ofNat_mod_setWidth 5]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat,
    BitVec.getLsbD_append, BitVec.getLsbD_setWidth, Nat.testBit_mod_two_pow]
  interval_cases i <;> simp

/-- The bitfield move encodes to the same four bytes on both sides, provided
the L3 `DecodeBitMasks` of the two fields succeeds. -/
theorem encodeBytes_bitfieldMove (inzero extend : Bool) (immr imms rn rd : Nat)
    (n : Nat) (wmask tmask : BitVec 64)
    (hopc : bitfieldOpBits inzero extend = some n)
    (himmr : immr < 64) (himms : imms < 64)
    (hmasks : DecodeBitMasks (TM := 64)
      ((1 : BitVec 1), (BitVec.ofNat 6 imms, (BitVec.ofNat 6 immr, false))) =
        some (wmask, tmask)) :
    encodeBytes (.bitfieldMove inzero extend immr imms rn rd) =
      arm8Encode (.Data (.«BitfieldMove@64»
        ((1 : BitVec 64), (inzero, (extend, (wmask, (tmask,
          (immr, (imms, (BitVec.ofNat 5 rn, BitVec.ofNat 5 rd)))))))))) := by
  have hopc' : arm8BitfieldOpc inzero extend = some (BitVec.ofNat 2 n) :=
    bitfieldOpBits_eq inzero extend n hopc
  have hguard : (immr < 64 && imms < 64) = true := by
    simp [himmr, himms]
  have hw : encodeInsn32 (.bitfieldMove inzero extend immr imms rn rd) =
      some (fields [(1, 1), (2, n), (6, 38), (1, 1), (6, immr), (6, imms),
        (5, rn), (5, rd)]) := by
    simp only [encodeInsn32]
    simp only [hopc, hguard, if_true]
  rw [encodeBytes_eq_of_encodeInsn32 _ _ hw]
  simp only [arm8Encode, arm8Encode_bitfieldMove inzero extend (BitVec.ofNat 2 n)
    wmask tmask immr imms (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) hopc' himmr himms hmasks,
    fields_bitfieldMove]

end Flapjack.Compiler.Encoders.Arm8.L3
