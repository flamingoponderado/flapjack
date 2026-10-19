/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProof

/-!
# ARMv8 decoder inverses: fixed-opcode forms

Kernel-checked decoder inverses for the emitted forms whose word is a fixed
opcode plus register/immediate fields.  Bit facts are proved by extensionality
over `getLsbD` and `interval_cases`, not by a native decision procedure.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-! ## `extractRegister` -/

def extractWord (rm : BitVec 5) (imms : BitVec 6) (rn : BitVec 5) (rd : BitVec 5) : BitVec 32 :=
  ((((((1182 : BitVec 32) <<< 5 ||| rm.setWidth 32) <<< 6 ||| imms.setWidth 32) <<< 5 |||
      rn.setWidth 32) <<< 5 ||| rd.setWidth 32))

theorem fields_extract (rm imms rn rd : Nat) :
    fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]
      = extractWord (BitVec.ofNat 5 rm) (BitVec.ofNat 6 imms) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

theorem decode_extract_word (rm : BitVec 5) (imms : BitVec 6) (rn : BitVec 5) (rd : BitVec 5) :
    decodeInsn32 (extractWord rm imms rn rd) = some (.extractRegister imms.toNat rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (extractWord rm imms rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [extractWord] at hb
    simp at hb
  have h2 : bitMatches (extractWord rm imms rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [extractWord] at hb
    simp at hb
  have h3 : bitMatches (extractWord rm imms rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [extractWord] at hb
    simp at hb
  have h4 : bitMatches (extractWord rm imms rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [extractWord] at hb
    simp at hb
  have h5 : bitMatches (extractWord rm imms rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [extractWord] at hb
    simp at hb
  have h6 : bitMatches (extractWord rm imms rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [extractWord] at hb
    simp at hb
  have h7 : bitMatches (extractWord rm imms rn rd) 0x9FE00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [extractWord] at hb
    simp at hb
  have hK : bitMatches (extractWord rm imms rn rd) 0xFFE00000 0x93C00000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [extractWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (extractWord rm imms rn rd) 10 6 = imms.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [extractWord]
    simp
    interval_cases i <;> simp
  have f2 : part (extractWord rm imms rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [extractWord]
    simp
    interval_cases i <;> simp
  have f3 : part (extractWord rm imms rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [extractWord]
    simp
    interval_cases i <;> simp
  have f4 : part (extractWord rm imms rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [extractWord]
    simp
  simp only [f1, f2, f3, f4]

theorem decode_encode_extractRegister32 (rm imms rn rd : Nat)
    (hrm : rm < 32) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)])
      = some (.extractRegister imms rm rn rd) := by
  rw [fields_extract rm imms rn rd, decode_extract_word]
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm, Nat.mod_eq_of_lt himms,
    Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

theorem encodeInsn_extractRegister (rm imms rn rd : Nat) :
    encodeInsn (.extractRegister imms rm rn rd) =
      some ((fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]).setWidth 64) := rfl

theorem decode_encode_extractRegister (rm imms rn rd : Nat)
    (hrm : rm < 32) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.extractRegister imms rm rn rd)).getD 0)
      = some (.extractRegister imms rm rn rd) := by
  rw [encodeInsn_extractRegister, Option.getD_some]
  rw [show decodeInsn ((fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_extractRegister32 rm imms rn rd hrm himms hrn hrd

theorem arm8Next_extractRegister (s : Arm8State) (d : BitVec 64 → Prop)
    (rm imms rn rd : Nat) (hrm : rm < 32) (himms : imms < 64) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.extractRegister imms rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.extractRegister imms rm rn rd) := by
  rw [arm8Next_encodeBytes s (.extractRegister imms rm rn rd)
    ((fields [(11, 1182), (5, rm), (6, imms), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_extractRegister rm imms rn rd)
    (decode_encode_extractRegister rm imms rn rd hrm himms hrn hrd) hbytes]

end Flapjack.Compiler.Encoders.Arm8
