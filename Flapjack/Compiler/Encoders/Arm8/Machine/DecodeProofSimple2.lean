/-
Copyright (c) 2025 Flapjack contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.IntervalCases
import Flapjack.Compiler.Encoders.Arm8.Machine.DecodeProofSimple

/-!
# ARMv8 decoder inverses: unconditional fixed-opcode forms

Kernel-checked decoder inverses for the remaining unconditional emitted
instruction forms.  Bit facts are proved by extensionality over `getLsbD` and
`interval_cases`, not by a native decision procedure.
-/

namespace Flapjack.Compiler.Encoders.Arm8

open Flapjack Compiler.Encoders.Asm

/-! ## `shift` -/

/-- The 32-bit word of a `shift` instruction, over width-typed atoms. -/
def shiftWord (sh : BitVec 2) (rm rn rd : BitVec 5) : BitVec 32 :=
  ((((((1238 : BitVec 32) <<< 5 ||| rm.setWidth 32) <<< 4 ||| (2 : BitVec 32)) <<< 2 |||
      sh.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `shift` is the width-typed word. -/
theorem fields_shift (sh : ShiftType) (rm rn rd : Nat) :
    fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn), (5, rd)]
      = shiftWord (BitVec.ofNat 2 (shiftTypeBits sh)) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `shift` word. -/
theorem decode_shift_word (sh : BitVec 2) (rm rn rd : BitVec 5) :
    decodeInsn32 (shiftWord sh rm rn rd)
      = some (.shift (decodeShift sh.toNat) rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (shiftWord sh rm rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [shiftWord] at hb
    simp at hb
  have h2 : bitMatches (shiftWord sh rm rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [shiftWord] at hb
    simp at hb
  have h3 : bitMatches (shiftWord sh rm rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [shiftWord] at hb
    simp at hb
  have h4 : bitMatches (shiftWord sh rm rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [shiftWord] at hb
    simp at hb
  have h5 : bitMatches (shiftWord sh rm rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [shiftWord] at hb
    simp at hb
  have h6 : bitMatches (shiftWord sh rm rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [shiftWord] at hb
    simp at hb
  have h7 : bitMatches (shiftWord sh rm rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [shiftWord] at hb
    simp at hb
  have h8 : bitMatches (shiftWord sh rm rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [shiftWord] at hb
    simp at hb
  have hK : bitMatches (shiftWord sh rm rn rd) 0xFFE0F000 0x9AC02000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [shiftWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (shiftWord sh rm rn rd) 10 2 = sh.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [shiftWord]
    simp
    interval_cases i <;> simp
  have f2 : part (shiftWord sh rm rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [shiftWord]
    simp
    interval_cases i <;> simp
  have f3 : part (shiftWord sh rm rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [shiftWord]
    simp
    interval_cases i <;> simp
  have f4 : part (shiftWord sh rm rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [shiftWord]
    simp
  simp only [f1, f2, f3, f4]

/-- The `shift` instruction survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_shift32 (sh : ShiftType) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn), (5, rd)])
      = some (.shift sh rm rn rd) := by
  rw [fields_shift sh rm rn rd, decode_shift_word]
  cases sh <;>
    simp [shiftTypeBits, decodeShift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm,
      Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `shift`. -/
theorem encodeInsn_shift (sh : ShiftType) (rm rn rd : Nat) :
    encodeInsn (.shift sh rm rn rd) =
      some ((fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn),
        (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_shift (sh : ShiftType) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn),
      (5, rd)]).setWidth 64) = some (.shift sh rm rn rd) := by
  rw [show decodeInsn ((fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn),
      (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn),
          (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_shift32 sh rm rn rd hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `shift`. -/
theorem decode_encode_shiftInsn (sh : ShiftType) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.shift sh rm rn rd)).getD 0) = some (.shift sh rm rn rd) := by
  rw [encodeInsn_shift, Option.getD_some]
  exact decode_encode_shift sh rm rn rd hrm hrn hrd

/-- One machine step executes a `shift` instruction whose bytes are at the PC. -/
theorem arm8Next_shift (s : Arm8State) (d : BitVec 64 → Prop)
    (sh : ShiftType) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.shift sh rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.shift sh rm rn rd) := by
  rw [arm8Next_encodeBytes s (.shift sh rm rn rd)
    ((fields [(11, 1238), (5, rm), (4, 2), (2, shiftTypeBits sh), (5, rn),
      (5, rd)]).setWidth 64) d
    (encodeInsn_shift sh rm rn rd)
    (decode_encode_shiftInsn sh rm rn rd hrm hrn hrd) hbytes]

/-! ## `division` -/

/-- The 32-bit word of a `division` instruction, over width-typed atoms. -/
def divisionWord (o1 : BitVec 1) (rm rn rd : BitVec 5) : BitVec 32 :=
  ((((((1238 : BitVec 32) <<< 5 ||| rm.setWidth 32) <<< 5 ||| (1 : BitVec 32)) <<< 1 |||
      o1.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `division` is the width-typed word. -/
theorem fields_division (o1 : Bool) (rm rn rd : Nat) :
    fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn), (5, rd)]
      = divisionWord (BitVec.ofNat 1 (bit (!o1))) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `division` word. -/
theorem decode_division_word (o1 : BitVec 1) (rm rn rd : BitVec 5) :
    decodeInsn32 (divisionWord o1 rm rn rd)
      = some (.division (o1.toNat = 0) rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (divisionWord o1 rm rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [divisionWord] at hb
    simp at hb
  have h2 : bitMatches (divisionWord o1 rm rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [divisionWord] at hb
    simp at hb
  have h3 : bitMatches (divisionWord o1 rm rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [divisionWord] at hb
    simp at hb
  have h4 : bitMatches (divisionWord o1 rm rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [divisionWord] at hb
    simp at hb
  have h5 : bitMatches (divisionWord o1 rm rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [divisionWord] at hb
    simp at hb
  have h6 : bitMatches (divisionWord o1 rm rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [divisionWord] at hb
    simp at hb
  have h7 : bitMatches (divisionWord o1 rm rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [divisionWord] at hb
    simp at hb
  have h8 : bitMatches (divisionWord o1 rm rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [divisionWord] at hb
    simp at hb
  have h9 : bitMatches (divisionWord o1 rm rn rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 13) h
    simp only [divisionWord] at hb
    simp at hb
  have hK : bitMatches (divisionWord o1 rm rn rd) 0xFFE0F800 0x9AC00800 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [divisionWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (divisionWord o1 rm rn rd) 10 1 = o1.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [divisionWord]
    simp
    interval_cases i; simp
  have f2 : part (divisionWord o1 rm rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [divisionWord]
    simp
    interval_cases i <;> simp
  have f3 : part (divisionWord o1 rm rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [divisionWord]
    simp
    interval_cases i <;> simp
  have f4 : part (divisionWord o1 rm rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [divisionWord]
    simp
  simp only [f1, f2, f3, f4]

/-- The `division` instruction survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_division32 (o1 : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn), (5, rd)])
      = some (.division o1 rm rn rd) := by
  rw [fields_division o1 rm rn rd, decode_division_word]
  cases o1 <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm,
      Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `division`. -/
theorem encodeInsn_division (o1 : Bool) (rm rn rd : Nat) :
    encodeInsn (.division o1 rm rn rd) =
      some ((fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn),
        (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_division (o1 : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn),
      (5, rd)]).setWidth 64) = some (.division o1 rm rn rd) := by
  rw [show decodeInsn ((fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn),
      (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn),
          (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_division32 o1 rm rn rd hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `division`. -/
theorem decode_encode_divisionInsn (o1 : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.division o1 rm rn rd)).getD 0) = some (.division o1 rm rn rd) := by
  rw [encodeInsn_division, Option.getD_some]
  exact decode_encode_division o1 rm rn rd hrm hrn hrd

/-- One machine step executes a `division` instruction whose bytes are at the PC. -/
theorem arm8Next_division (s : Arm8State) (d : BitVec 64 → Prop)
    (o1 : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.division o1 rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.division o1 rm rn rd) := by
  rw [arm8Next_encodeBytes s (.division o1 rm rn rd)
    ((fields [(11, 1238), (5, rm), (5, 1), (1, bit (!o1)), (5, rn),
      (5, rd)]).setWidth 64) d
    (encodeInsn_division o1 rm rn rd)
    (decode_encode_divisionInsn o1 rm rn rd hrm hrn hrd) hbytes]


/-! ## `multiplyHigh` -/

/-- The 32-bit word of a `multiplyHigh` instruction, over width-typed atoms. -/
def multiplyHighWord (u : BitVec 1) (rm rn rd : BitVec 5) : BitVec 32 :=
  (((((((155 : BitVec 32) <<< 1 ||| u.setWidth 32) <<< 2 ||| (2 : BitVec 32)) <<< 5 |||
      rm.setWidth 32) <<< 6 ||| (31 : BitVec 32)) <<< 5 ||| rn.setWidth 32) <<< 5 |||
      rd.setWidth 32)

/-- The `fields` composition of a `multiplyHigh` is the width-typed word. -/
theorem fields_multiplyHigh (u : Bool) (rm rn rd : Nat) :
    fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn), (5, rd)]
      = multiplyHighWord (BitVec.ofNat 1 (bit (!u))) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `multiplyHigh` word. -/
theorem decode_multiplyHigh_word (u : BitVec 1) (rm rn rd : BitVec 5) :
    decodeInsn32 (multiplyHighWord u rm rn rd)
      = some (.multiplyHigh (u.toNat = 0) rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (multiplyHighWord u rm rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 10) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h2 : bitMatches (multiplyHighWord u rm rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h3 : bitMatches (multiplyHighWord u rm rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h4 : bitMatches (multiplyHighWord u rm rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h5 : bitMatches (multiplyHighWord u rm rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h6 : bitMatches (multiplyHighWord u rm rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h7 : bitMatches (multiplyHighWord u rm rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h8 : bitMatches (multiplyHighWord u rm rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h9 : bitMatches (multiplyHighWord u rm rn rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 12) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have h10 : bitMatches (multiplyHighWord u rm rn rd) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 12) h
    simp only [multiplyHighWord] at hb
    simp at hb
  have hK : bitMatches (multiplyHighWord u rm rn rd) 0x9B600000 0x9B400000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyHighWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (multiplyHighWord u rm rn rd) 23 1 = u.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyHighWord]
    simp
    interval_cases i; simp

  have f2 : part (multiplyHighWord u rm rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyHighWord]
    simp
    interval_cases i <;> simp
  have f4 : part (multiplyHighWord u rm rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyHighWord]
    simp
    interval_cases i <;> simp
  have f5 : part (multiplyHighWord u rm rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyHighWord]
    simp
  simp only [f1, f2, f4, f5]

/-- The `multiplyHigh` instruction survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_multiplyHigh32 (u : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn), (5, rd)])
      = some (.multiplyHigh u rm rn rd) := by
  rw [fields_multiplyHigh u rm rn rd, decode_multiplyHigh_word]
  cases u <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm,
      Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `multiplyHigh`. -/
theorem encodeInsn_multiplyHigh (u : Bool) (rm rn rd : Nat) :
    encodeInsn (.multiplyHigh u rm rn rd) =
      some ((fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn),
        (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_multiplyHigh (u : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn),
      (5, rd)]).setWidth 64) = some (.multiplyHigh u rm rn rd) := by
  rw [show decodeInsn ((fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn),
      (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn),
          (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_multiplyHigh32 u rm rn rd hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `multiplyHigh`. -/
theorem decode_encode_multiplyHighInsn (u : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.multiplyHigh u rm rn rd)).getD 0)
      = some (.multiplyHigh u rm rn rd) := by
  rw [encodeInsn_multiplyHigh, Option.getD_some]
  exact decode_encode_multiplyHigh u rm rn rd hrm hrn hrd

/-- One machine step executes a `multiplyHigh` instruction whose bytes are at the PC. -/
theorem arm8Next_multiplyHigh (s : Arm8State) (d : BitVec 64 → Prop)
    (u : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.multiplyHigh u rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.multiplyHigh u rm rn rd) := by
  rw [arm8Next_encodeBytes s (.multiplyHigh u rm rn rd)
    ((fields [(8, 155), (1, bit (!u)), (2, 2), (5, rm), (6, 31), (5, rn),
      (5, rd)]).setWidth 64) d
    (encodeInsn_multiplyHigh u rm rn rd)
    (decode_encode_multiplyHighInsn u rm rn rd hrm hrn hrd) hbytes]

/-! ## `multiplyAddSub` -/

/-- The 32-bit word of a `multiplyAddSub` instruction, over width-typed atoms. -/
def multiplyAddSubWord (o0 : BitVec 1) (rm ra rn rd : BitVec 5) : BitVec 32 :=
  ((((((1240 : BitVec 32) <<< 5 ||| rm.setWidth 32) <<< 1 ||| o0.setWidth 32) <<< 5 |||
      ra.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `multiplyAddSub` is the width-typed word. -/
theorem fields_multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat) :
    fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn), (5, rd)]
      = multiplyAddSubWord (BitVec.ofNat 1 (bit o0)) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 5 ra) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `multiplyAddSub` word. -/
theorem decode_multiplyAddSub_word (o0 : BitVec 1) (rm ra rn rd : BitVec 5) :
    decodeInsn32 (multiplyAddSubWord o0 rm ra rn rd)
      = some (.multiplyAddSub (o0.toNat = 1) rm.toNat ra.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h2 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h3 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h4 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h5 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h6 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h7 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h8 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h9 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h10 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have h11 : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [multiplyAddSubWord] at hb
    simp at hb
  have hK : bitMatches (multiplyAddSubWord o0 rm ra rn rd) 0xFFE00000 0x9B000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (multiplyAddSubWord o0 rm ra rn rd) 15 1 = o0.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
    interval_cases i; simp

  have f2 : part (multiplyAddSubWord o0 rm ra rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
    interval_cases i <;> simp
  have f3 : part (multiplyAddSubWord o0 rm ra rn rd) 10 5 = ra.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
    interval_cases i <;> simp
  have f4 : part (multiplyAddSubWord o0 rm ra rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
    interval_cases i <;> simp
  have f5 : part (multiplyAddSubWord o0 rm ra rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [multiplyAddSubWord]
    simp
  simp only [f1, f2, f3, f4, f5]

/-- The `multiplyAddSub` instruction survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_multiplyAddSub32 (o0 : Bool) (rm ra rn rd : Nat)
    (hrm : rm < 32) (hra : ra < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn), (5, rd)])
      = some (.multiplyAddSub o0 rm ra rn rd) := by
  rw [fields_multiplyAddSub o0 rm ra rn rd, decode_multiplyAddSub_word]
  cases o0 <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm, Nat.mod_eq_of_lt hra,
      Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `multiplyAddSub`. -/
theorem encodeInsn_multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat) :
    encodeInsn (.multiplyAddSub o0 rm ra rn rd) =
      some ((fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn),
        (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_multiplyAddSub (o0 : Bool) (rm ra rn rd : Nat)
    (hrm : rm < 32) (hra : ra < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn),
      (5, rd)]).setWidth 64) = some (.multiplyAddSub o0 rm ra rn rd) := by
  rw [show decodeInsn ((fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn),
      (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn),
          (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_multiplyAddSub32 o0 rm ra rn rd hrm hra hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `multiplyAddSub`. -/
theorem decode_encode_multiplyAddSubInsn (o0 : Bool) (rm ra rn rd : Nat)
    (hrm : rm < 32) (hra : ra < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.multiplyAddSub o0 rm ra rn rd)).getD 0)
      = some (.multiplyAddSub o0 rm ra rn rd) := by
  rw [encodeInsn_multiplyAddSub, Option.getD_some]
  exact decode_encode_multiplyAddSub o0 rm ra rn rd hrm hra hrn hrd

/-- One machine step executes a `multiplyAddSub` instruction whose bytes are at the PC. -/
theorem arm8Next_multiplyAddSub (s : Arm8State) (d : BitVec 64 → Prop)
    (o0 : Bool) (rm ra rn rd : Nat)
    (hrm : rm < 32) (hra : ra < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.multiplyAddSub o0 rm ra rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.multiplyAddSub o0 rm ra rn rd) := by
  rw [arm8Next_encodeBytes s (.multiplyAddSub o0 rm ra rn rd)
    ((fields [(11, 1240), (5, rm), (1, bit o0), (5, ra), (5, rn),
      (5, rd)]).setWidth 64) d
    (encodeInsn_multiplyAddSub o0 rm ra rn rd)
    (decode_encode_multiplyAddSubInsn o0 rm ra rn rd hrm hra hrn hrd) hbytes]


/-! ## `addSubShiftedRegister` -/

/-- The 32-bit word of a `addSubShiftedRegister` instruction, over width-typed atoms. -/
def addSubShiftedRegisterWord (sub sf : BitVec 1) (sh : BitVec 2) (rm : BitVec 5)
    (imm6 : BitVec 6) (rn rd : BitVec 5) : BitVec 32 :=
  ((((((((((1 : BitVec 32) <<< 1 ||| sub.setWidth 32) <<< 1 ||| sf.setWidth 32) <<< 5 |||
      (11 : BitVec 32)) <<< 2 ||| sh.setWidth 32) <<< 1 ||| (0 : BitVec 32)) <<< 5 |||
      rm.setWidth 32) <<< 6 ||| imm6.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 |||
      rd.setWidth 32)

/-- The `fields` composition of a `addSubShiftedRegister` is the width-typed word. -/
theorem fields_addSubShiftedRegister (sub setFlags : Bool) (sh : ShiftType)
    (rm imm6 rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011), (2, shiftTypeBits sh),
      (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]
      = addSubShiftedRegisterWord (BitVec.ofNat 1 (bit sub)) (BitVec.ofNat 1 (bit setFlags))
          (BitVec.ofNat 2 (shiftTypeBits sh)) (BitVec.ofNat 5 rm) (BitVec.ofNat 6 imm6)
          (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `addSubShiftedRegister` word. -/
theorem decode_addSubShiftedRegister_word (sub : BitVec 1) (sf : BitVec 1) (sh : BitVec 2) (rm : BitVec 5) (imm6 : BitVec 6) (rn rd : BitVec 5) :
    decodeInsn32 (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) = some (.addSubShiftedRegister (sub.toNat = 1) (sf.toNat = 1) (decodeShift sh.toNat) rm.toNat imm6.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [addSubShiftedRegisterWord] at hb
    simp at hb
  have h2 : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubShiftedRegisterWord] at hb
    simp at hb
  have h3 : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [addSubShiftedRegisterWord] at hb
    simp at hb
  have h4 : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubShiftedRegisterWord] at hb
    simp at hb
  have h5 : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubShiftedRegisterWord] at hb
    simp at hb
  have hK : bitMatches (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0x9F200000 0x8B000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 30 1 = sub.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i; simp
  have f2 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 29 1 = sf.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i; simp
  have f3 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 22 2 = sh.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f4 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f5 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 10 6 = imm6.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f6 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
    interval_cases i <;> simp
  have f7 : part (addSubShiftedRegisterWord sub sf sh rm imm6 rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubShiftedRegisterWord]
    simp
  simp only [f1, f2, f3, f4, f5, f6, f7]


/-- The `addSubShiftedRegister` instruction survives a round trip through
`encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_addSubShiftedRegister32 (sub setFlags : Bool) (sh : ShiftType)
    (rm imm6 rn rd : Nat) (hrm : rm < 32) (himm6 : imm6 < 64) (hrn : rn < 32)
    (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
      (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)])
      = some (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd) := by
  rw [fields_addSubShiftedRegister sub setFlags sh rm imm6 rn rd,
    decode_addSubShiftedRegister_word]
  cases sub <;> cases setFlags <;> cases sh <;>
    simp [bit, shiftTypeBits, decodeShift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm,
      Nat.mod_eq_of_lt himm6, Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `addSubShiftedRegister`. -/
theorem encodeInsn_addSubShiftedRegister (sub setFlags : Bool) (sh : ShiftType)
    (rm imm6 rn rd : Nat) :
    encodeInsn (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd) =
      some ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
        (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_addSubShiftedRegister (sub setFlags : Bool) (sh : ShiftType)
    (rm imm6 rn rd : Nat) (hrm : rm < 32) (himm6 : imm6 < 64) (hrn : rn < 32)
    (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
      (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]).setWidth 64)
      = some (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
      (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
          (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_addSubShiftedRegister32 sub setFlags sh rm imm6 rn rd hrm himm6 hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `addSubShiftedRegister`. -/
theorem decode_encode_addSubShiftedRegisterInsn (sub setFlags : Bool) (sh : ShiftType)
    (rm imm6 rn rd : Nat) (hrm : rm < 32) (himm6 : imm6 < 64) (hrn : rn < 32)
    (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd)).getD 0)
      = some (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd) := by
  rw [encodeInsn_addSubShiftedRegister, Option.getD_some]
  exact decode_encode_addSubShiftedRegister sub setFlags sh rm imm6 rn rd hrm himm6 hrn hrd

/-- One machine step executes an `addSubShiftedRegister` instruction whose bytes are
at the PC. -/
theorem arm8Next_addSubShiftedRegister (s : Arm8State) (d : BitVec 64 → Prop)
    (sub setFlags : Bool) (sh : ShiftType) (rm imm6 rn rd : Nat)
    (hrm : rm < 32) (himm6 : imm6 < 64) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd) := by
  rw [arm8Next_encodeBytes s (.addSubShiftedRegister sub setFlags sh rm imm6 rn rd)
    ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (5, 0b01011),
      (2, shiftTypeBits sh), (1, 0), (5, rm), (6, imm6), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_addSubShiftedRegister sub setFlags sh rm imm6 rn rd)
    (decode_encode_addSubShiftedRegisterInsn sub setFlags sh rm imm6 rn rd hrm himm6 hrn hrd)
    hbytes]


/-! ## `addSubCarry` -/

/-- The 32-bit word of a `addSubCarry` instruction, over width-typed atoms. -/
def addSubCarryWord (sub sf : BitVec 1) (rm rn rd : BitVec 5) : BitVec 32 :=
  ((((((((1 : BitVec 32) <<< 1 ||| sub.setWidth 32) <<< 1 ||| sf.setWidth 32) <<< 8 |||
      (208 : BitVec 32)) <<< 5 ||| rm.setWidth 32) <<< 6 ||| (0 : BitVec 32)) <<< 5 |||
      rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `addSubCarry` is the width-typed word. -/
theorem fields_addSubCarry (sub setFlags : Bool) (rm rn rd : Nat) :
    fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm), (6, 0),
      (5, rn), (5, rd)]
      = addSubCarryWord (BitVec.ofNat 1 (bit sub)) (BitVec.ofNat 1 (bit setFlags))
          (BitVec.ofNat 5 rm) (BitVec.ofNat 5 rn) (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `addSubCarry` word. -/
theorem decode_addSubCarry_word (sub : BitVec 1) (sf : BitVec 1) (rm rn rd : BitVec 5) :
    decodeInsn32 (addSubCarryWord sub sf rm rn rd) = some (.addSubCarry (sub.toNat = 1) (sf.toNat = 1) rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 13) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h2 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h3 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h4 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h5 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h6 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h7 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h8 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h9 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 13) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h10 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h11 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h12 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h13 : bitMatches (addSubCarryWord sub sf rm rn rd) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have h14 : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [addSubCarryWord] at hb
    simp at hb
  have hK : bitMatches (addSubCarryWord sub sf rm rn rd) 0x9A000000 0x9A000000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (addSubCarryWord sub sf rm rn rd) 30 1 = sub.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
    interval_cases i; simp
  have f2 : part (addSubCarryWord sub sf rm rn rd) 29 1 = sf.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
    interval_cases i; simp
  have f3 : part (addSubCarryWord sub sf rm rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
    interval_cases i <;> simp
  have f4 : part (addSubCarryWord sub sf rm rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
    interval_cases i <;> simp
  have f5 : part (addSubCarryWord sub sf rm rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addSubCarryWord]
    simp
  simp only [f1, f2, f3, f4, f5]


/-- The `addSubCarry` instruction survives a round trip through `encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_addSubCarry32 (sub setFlags : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
      (6, 0), (5, rn), (5, rd)])
      = some (.addSubCarry sub setFlags rm rn rd) := by
  rw [fields_addSubCarry sub setFlags rm rn rd, decode_addSubCarry_word]
  cases sub <;> cases setFlags <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrm, Nat.mod_eq_of_lt hrn,
      Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `addSubCarry`. -/
theorem encodeInsn_addSubCarry (sub setFlags : Bool) (rm rn rd : Nat) :
    encodeInsn (.addSubCarry sub setFlags rm rn rd) =
      some ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
        (6, 0), (5, rn), (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_addSubCarry (sub setFlags : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
      (6, 0), (5, rn), (5, rd)]).setWidth 64)
      = some (.addSubCarry sub setFlags rm rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
      (6, 0), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
          (6, 0), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_addSubCarry32 sub setFlags rm rn rd hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `addSubCarry`. -/
theorem decode_encode_addSubCarryInsn (sub setFlags : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.addSubCarry sub setFlags rm rn rd)).getD 0)
      = some (.addSubCarry sub setFlags rm rn rd) := by
  rw [encodeInsn_addSubCarry, Option.getD_some]
  exact decode_encode_addSubCarry sub setFlags rm rn rd hrm hrn hrd

/-- One machine step executes an `addSubCarry` instruction whose bytes are at the PC. -/
theorem arm8Next_addSubCarry (s : Arm8State) (d : BitVec 64 → Prop)
    (sub setFlags : Bool) (rm rn rd : Nat)
    (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.addSubCarry sub setFlags rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.addSubCarry sub setFlags rm rn rd) := by
  rw [arm8Next_encodeBytes s (.addSubCarry sub setFlags rm rn rd)
    ((fields [(1, 1), (1, bit sub), (1, bit setFlags), (8, 208), (5, rm),
      (6, 0), (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_addSubCarry sub setFlags rm rn rd)
    (decode_encode_addSubCarryInsn sub setFlags rm rn rd hrm hrn hrd) hbytes]

/-! ## `conditionalSelect` -/

/-- The 32-bit word of a `conditionalSelect` instruction, over width-typed atoms. -/
def conditionalSelectWord (op : BitVec 1) (rm : BitVec 5) (cd : BitVec 4)
    (o2 : BitVec 1) (rn rd : BitVec 5) : BitVec 32 :=
  (((((((((1 : BitVec 32) <<< 1 ||| op.setWidth 32) <<< 9 ||| (212 : BitVec 32)) <<< 5 |||
      rm.setWidth 32) <<< 4 ||| cd.setWidth 32) <<< 1 ||| (0 : BitVec 32)) <<< 1 |||
      o2.setWidth 32) <<< 5 ||| rn.setWidth 32) <<< 5 ||| rd.setWidth 32)

/-- The `fields` composition of a `conditionalSelect` is the width-typed word. -/
theorem fields_conditionalSelect (op o2 : Bool) (cd rm rn rd : Nat) :
    fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0), (1, bit o2),
      (5, rn), (5, rd)]
      = conditionalSelectWord (BitVec.ofNat 1 (bit op)) (BitVec.ofNat 5 rm)
          (BitVec.ofNat 4 cd) (BitVec.ofNat 1 (bit o2)) (BitVec.ofNat 5 rn)
          (BitVec.ofNat 5 rd) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `conditionalSelect` word. -/
theorem decode_conditionalSelect_word (op : BitVec 1) (rm : BitVec 5) (cd : BitVec 4) (o2 : BitVec 1) (rn rd : BitVec 5) :
    decodeInsn32 (conditionalSelectWord op rm cd o2 rn rd) = some (.conditionalSelect (op.toNat = 1) (o2.toNat = 1) cd.toNat rm.toNat rn.toNat rd.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h2 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h3 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h4 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h5 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h6 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h7 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h8 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h9 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h10 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h11 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h12 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have h13 : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [conditionalSelectWord] at hb
    simp at hb
  have hK : bitMatches (conditionalSelectWord op rm cd o2 rn rd) 0x9A800800 0x9A800000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (conditionalSelectWord op rm cd o2 rn rd) 30 1 = op.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i; simp
  have f2 : part (conditionalSelectWord op rm cd o2 rn rd) 10 1 = o2.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i; simp
  have f3 : part (conditionalSelectWord op rm cd o2 rn rd) 12 4 = cd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i <;> simp
  have f4 : part (conditionalSelectWord op rm cd o2 rn rd) 16 5 = rm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i <;> simp
  have f5 : part (conditionalSelectWord op rm cd o2 rn rd) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
    interval_cases i <;> simp
  have f6 : part (conditionalSelectWord op rm cd o2 rn rd) 0 5 = rd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalSelectWord]
    simp
  simp only [f1, f2, f3, f4, f5, f6]


/-- The `conditionalSelect` instruction survives a round trip through
`encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_conditionalSelect32 (op o2 : Bool) (cd rm rn rd : Nat)
    (hcd : cd < 16) (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
      (1, bit o2), (5, rn), (5, rd)])
      = some (.conditionalSelect op o2 cd rm rn rd) := by
  rw [fields_conditionalSelect op o2 cd rm rn rd, decode_conditionalSelect_word]
  cases op <;> cases o2 <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcd, Nat.mod_eq_of_lt hrm,
      Nat.mod_eq_of_lt hrn, Nat.mod_eq_of_lt hrd]

/-- The 64-bit carrier word emitted for `conditionalSelect`. -/
theorem encodeInsn_conditionalSelect (op o2 : Bool) (cd rm rn rd : Nat) :
    encodeInsn (.conditionalSelect op o2 cd rm rn rd) =
      some ((fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
        (1, bit o2), (5, rn), (5, rd)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_conditionalSelect (op o2 : Bool) (cd rm rn rd : Nat)
    (hcd : cd < 16) (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
      (1, bit o2), (5, rn), (5, rd)]).setWidth 64)
      = some (.conditionalSelect op o2 cd rm rn rd) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
      (1, bit o2), (5, rn), (5, rd)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0),
          (1, bit o2), (5, rn), (5, rd)]) by
    simp [decodeInsn]]
  exact decode_encode_conditionalSelect32 op o2 cd rm rn rd hcd hrm hrn hrd

/-- `decodeInsn` inverts `encodeInsn` on `conditionalSelect`. -/
theorem decode_encode_conditionalSelectInsn (op o2 : Bool) (cd rm rn rd : Nat)
    (hcd : cd < 16) (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32) :
    decodeInsn ((encodeInsn (.conditionalSelect op o2 cd rm rn rd)).getD 0)
      = some (.conditionalSelect op o2 cd rm rn rd) := by
  rw [encodeInsn_conditionalSelect, Option.getD_some]
  exact decode_encode_conditionalSelect op o2 cd rm rn rd hcd hrm hrn hrd

/-- One machine step executes a `conditionalSelect` instruction whose bytes are at the PC. -/
theorem arm8Next_conditionalSelect (s : Arm8State) (d : BitVec 64 → Prop)
    (op o2 : Bool) (cd rm rn rd : Nat)
    (hcd : cd < 16) (hrm : rm < 32) (hrn : rn < 32) (hrd : rd < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.conditionalSelect op o2 cd rm rn rd)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.conditionalSelect op o2 cd rm rn rd) := by
  rw [arm8Next_encodeBytes s (.conditionalSelect op o2 cd rm rn rd)
    ((fields [(1, 1), (1, bit op), (9, 212), (5, rm), (4, cd), (1, 0), (1, bit o2),
      (5, rn), (5, rd)]).setWidth 64) d
    (encodeInsn_conditionalSelect op o2 cd rm rn rd)
    (decode_encode_conditionalSelectInsn op o2 cd rm rn rd hcd hrm hrn hrd) hbytes]


/-! ## `conditionalCompareImmediate` -/

/-- The 32-bit word of a `conditionalCompareImmediate` instruction, over width-typed atoms. -/
def conditionalCompareImmediateWord (opc : BitVec 1) (imm : BitVec 5) (cd : BitVec 4)
    (rn : BitVec 5) (nzcv : BitVec 4) : BitVec 32 :=
  (((((((((1 : BitVec 32) <<< 1 ||| opc.setWidth 32) <<< 9 ||| (466 : BitVec 32)) <<< 5 |||
      imm.setWidth 32) <<< 4 ||| cd.setWidth 32) <<< 2 ||| (2 : BitVec 32)) <<< 5 |||
      rn.setWidth 32) <<< 1 ||| (0 : BitVec 32)) <<< 4 ||| nzcv.setWidth 32)

/-- The `fields` composition of a `conditionalCompareImmediate` is the width-typed word. -/
theorem fields_conditionalCompareImmediate (opc : Bool) (imm cd rn : Nat)
    (n z c v : Bool) :
    fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2), (5, rn),
      (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]
      = conditionalCompareImmediateWord (BitVec.ofNat 1 (bit opc)) (BitVec.ofNat 5 imm)
          (BitVec.ofNat 4 cd) (BitVec.ofNat 5 rn)
          (BitVec.ofNat 4 (bit n * 8 + bit z * 4 + bit c * 2 + bit v)) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `conditionalCompareImmediate` word. -/
theorem decode_conditionalCompareImmediate_word (opc : BitVec 1) (imm : BitVec 5)
    (cd : BitVec 4) (rn : BitVec 5) (nzcv : BitVec 4) :
    decodeInsn32 (conditionalCompareImmediateWord opc imm cd rn nzcv)
      = some (.conditionalCompareImmediate (opc.toNat = 1)
          (BitVec.ofNat 64 imm.toNat) cd.toNat
          (nzcv.getLsbD 3, nzcv.getLsbD 2, nzcv.getLsbD 1, nzcv.getLsbD 0) rn.toNat) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 4) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h2 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h3 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h4 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h5 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 28) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h6 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h7 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h8 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h9 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h10 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h11 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have h12 : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 22) h
    simp only [conditionalCompareImmediateWord] at hb
    simp at hb
  have hK : bitMatches (conditionalCompareImmediateWord opc imm cd rn nzcv) 0xBA400810 0xBA400800 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalCompareImmediateWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (conditionalCompareImmediateWord opc imm cd rn nzcv) 30 1 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalCompareImmediateWord]
    simp
    interval_cases i; simp
  have f2 : part (conditionalCompareImmediateWord opc imm cd rn nzcv) 16 5 = imm.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalCompareImmediateWord]
    simp
    interval_cases i <;> simp
  have f3 : part (conditionalCompareImmediateWord opc imm cd rn nzcv) 12 4 = cd.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalCompareImmediateWord]
    simp
    interval_cases i <;> simp
  have f4 : part (conditionalCompareImmediateWord opc imm cd rn nzcv) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [conditionalCompareImmediateWord]
    simp
    interval_cases i <;> simp
  have g3 : (decide (part (conditionalCompareImmediateWord opc imm cd rn nzcv) 3 1 = 1)) = nzcv.getLsbD 3 := by
    have hx : ((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 3).setWidth 1 = BitVec.ofBool (nzcv.getLsbD 3) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [conditionalCompareImmediateWord]
      simp
      interval_cases i
      simp
    show decide ((((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 3).setWidth 1).toNat = 1) = nzcv.getLsbD 3
    rw [hx]
    cases nzcv.getLsbD 3 <;> rfl
  have g2 : (decide (part (conditionalCompareImmediateWord opc imm cd rn nzcv) 2 1 = 1)) = nzcv.getLsbD 2 := by
    have hx : ((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 2).setWidth 1 = BitVec.ofBool (nzcv.getLsbD 2) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [conditionalCompareImmediateWord]
      simp
      interval_cases i
      simp
    show decide ((((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 2).setWidth 1).toNat = 1) = nzcv.getLsbD 2
    rw [hx]
    cases nzcv.getLsbD 2 <;> rfl
  have g1 : (decide (part (conditionalCompareImmediateWord opc imm cd rn nzcv) 1 1 = 1)) = nzcv.getLsbD 1 := by
    have hx : ((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 1).setWidth 1 = BitVec.ofBool (nzcv.getLsbD 1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [conditionalCompareImmediateWord]
      simp
      interval_cases i
      simp
    show decide ((((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 1).setWidth 1).toNat = 1) = nzcv.getLsbD 1
    rw [hx]
    cases nzcv.getLsbD 1 <;> rfl
  have g0 : (decide (part (conditionalCompareImmediateWord opc imm cd rn nzcv) 0 1 = 1)) = nzcv.getLsbD 0 := by
    have hx : ((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 0).setWidth 1 = BitVec.ofBool (nzcv.getLsbD 0) := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [conditionalCompareImmediateWord]
      simp
      interval_cases i
      simp
    show decide ((((conditionalCompareImmediateWord opc imm cd rn nzcv) >>> 0).setWidth 1).toNat = 1) = nzcv.getLsbD 0
    rw [hx]
    cases nzcv.getLsbD 0 <;> rfl
  simp only [f1, f2, f3, f4, g3, g2, g1, g0]

/-- The `conditionalCompareImmediate` instruction survives a round trip through
`encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_conditionalCompareImmediate32 (opc : Bool) (imm cd rn : Nat)
    (n z c v : Bool) (himm : imm < 32) (hcd : cd < 16) (hrn : rn < 32) :
    decodeInsn32 (fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
      (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)])
      = some (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn) := by
  rw [fields_conditionalCompareImmediate opc imm cd rn n z c v,
    decode_conditionalCompareImmediate_word]
  rcases n <;> rcases z <;> rcases c <;> rcases v <;> cases opc <;>
    simp [bit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt himm, Nat.mod_eq_of_lt hcd,
      Nat.mod_eq_of_lt hrn]

/-- The 64-bit carrier word emitted for `conditionalCompareImmediate`.

Unlike the other forms this is not `rfl`: `encodeInsn32` guards the constructor
with `if imm.toNat < 32`, and the carrier field is `BitVec.ofNat 64 imm`, so the
guard needs the bound `himm`. -/
theorem encodeInsn_conditionalCompareImmediate (opc : Bool) (imm cd rn : Nat)
    (n z c v : Bool) (himm : imm < 32) :
    encodeInsn (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn) =
      some ((fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
        (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]).setWidth 64) := by
  have hmod : (BitVec.ofNat 64 imm).toNat = imm := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le himm (by norm_num))]
  unfold encodeInsn
  simp [encodeInsn32, hmod, himm]

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_conditionalCompareImmediate (opc : Bool) (imm cd rn : Nat)
    (n z c v : Bool) (himm : imm < 32) (hcd : cd < 16) (hrn : rn < 32) :
    decodeInsn ((fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
      (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]).setWidth 64)
      = some (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn) := by
  rw [show decodeInsn ((fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
      (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]).setWidth 64)
      = decodeInsn32 (fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
          (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]) by
    simp [decodeInsn]]
  exact decode_encode_conditionalCompareImmediate32 opc imm cd rn n z c v himm hcd hrn

/-- `decodeInsn` inverts `encodeInsn` on `conditionalCompareImmediate`. -/
theorem decode_encode_conditionalCompareImmediateInsn (opc : Bool) (imm cd rn : Nat)
    (n z c v : Bool) (himm : imm < 32) (hcd : cd < 16) (hrn : rn < 32) :
    decodeInsn ((encodeInsn (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd
      (n, z, c, v) rn)).getD 0)
      = some (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn) := by
  rw [encodeInsn_conditionalCompareImmediate opc imm cd rn n z c v himm, Option.getD_some]
  exact decode_encode_conditionalCompareImmediate opc imm cd rn n z c v himm hcd hrn

/-- One machine step executes a `conditionalCompareImmediate` instruction whose bytes are
at the PC. -/
theorem arm8Next_conditionalCompareImmediate (s : Arm8State) (d : BitVec 64 → Prop)
    (opc : Bool) (imm cd rn : Nat) (n z c v : Bool)
    (himm : imm < 32) (hcd : cd < 16) (hrn : rn < 32)
    (hbytes : bytesInMemoryHOL s.pc
      (encodeBytes (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn))
      s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 }
      (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn) := by
  rw [arm8Next_encodeBytes s
    (.conditionalCompareImmediate opc (BitVec.ofNat 64 imm) cd (n, z, c, v) rn)
    ((fields [(1, 1), (1, bit opc), (9, 466), (5, imm), (4, cd), (2, 2),
      (5, rn), (1, 0), (4, bit n * 8 + bit z * 4 + bit c * 2 + bit v)]).setWidth 64) d
    (encodeInsn_conditionalCompareImmediate opc imm cd rn n z c v himm)
    (decode_encode_conditionalCompareImmediate opc imm cd rn n z c v himm hcd hrn) hbytes]


/-! ## `branchRegister` -/

/-- The two-bit opcode of a `branchRegister` kind. -/
def branchKindBits : BranchKind → Nat
  | .jmp => 0
  | .call => 1
  | .ret => 2

/-- The 32-bit word of a `branchRegister` instruction, over width-typed atoms. -/
def branchRegisterWord (opc : BitVec 2) (rn : BitVec 5) : BitVec 32 :=
  (((((428 : BitVec 32) <<< 2 ||| opc.setWidth 32) <<< 11 ||| (1984 : BitVec 32)) <<< 5 |||
      rn.setWidth 32) <<< 5 ||| (0 : BitVec 32))

/-- The `fields` composition of a `branchRegister` is the width-typed word. -/
theorem fields_branchRegister (kind : BranchKind) (rn : Nat) :
    fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn), (5, 0)]
      = branchRegisterWord (BitVec.ofNat 2 (branchKindBits kind)) (BitVec.ofNat 5 rn) := by
  simp only [fields, List.foldl_cons, List.foldl_nil, ofNat_mod_self32]
  rfl

/-- Decode the width-typed `branchRegister` word. -/
theorem decode_branchRegister_word (opc : BitVec 2) (rn : BitVec 5)
    (h0 : opc = 0 ∨ opc = 1 ∨ opc = 2) :
    decodeInsn32 (branchRegisterWord opc rn)
      = some (.branchRegister rn.toNat
          (if opc = 0 then .jmp else if opc = 1 then .call else .ret)) := by
  simp only [decodeInsn32]
  have h1 : bitMatches (branchRegisterWord opc rn) 0xFFFFFFFF 0xD503201F = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 0) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h2 : bitMatches (branchRegisterWord opc rn) 0x9F800000 0x92800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h3 : bitMatches (branchRegisterWord opc rn) 0x9F800000 0x91000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h4 : bitMatches (branchRegisterWord opc rn) 0x9F800000 0x92000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h5 : bitMatches (branchRegisterWord opc rn) 0x9F000000 0x8A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 26) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h6 : bitMatches (branchRegisterWord opc rn) 0x9F200000 0x8B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h7 : bitMatches (branchRegisterWord opc rn) 0x9FC00000 0x93400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h8 : bitMatches (branchRegisterWord opc rn) 0xFFE00000 0x93C00000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h9 : bitMatches (branchRegisterWord opc rn) 0xFFE0F000 0x9AC02000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 13) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h10 : bitMatches (branchRegisterWord opc rn) 0xFFE0F800 0x9AC00800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h11 : bitMatches (branchRegisterWord opc rn) 0x9B600000 0x9B400000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h12 : bitMatches (branchRegisterWord opc rn) 0xFFE00000 0x9B000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h13 : bitMatches (branchRegisterWord opc rn) 0xBA400810 0xBA400800 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 11) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h14 : bitMatches (branchRegisterWord opc rn) 0x9A800800 0x9A800000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 23) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h15 : bitMatches (branchRegisterWord opc rn) 0x9A000000 0x9A000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 27) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h16 : bitMatches (branchRegisterWord opc rn) 0x3D000000 0x39000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 24) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h17 : bitMatches (branchRegisterWord opc rn) 0x3F000000 0x38000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h18 : bitMatches (branchRegisterWord opc rn) 0x7C000000 0x14000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 30) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have h19 : bitMatches (branchRegisterWord opc rn) 0xFF000010 0x54000000 = false := by
    rw [bitMatches, decide_eq_false_iff_not]
    intro h
    have hb := congrArg (fun x : BitVec 32 => x.getLsbD 25) h
    simp only [branchRegisterWord] at hb
    simp at hb
  have hK : bitMatches (branchRegisterWord opc rn) 0xFF9FFC1F 0xD61F0000 = true := by
    rw [bitMatches, decide_eq_true_eq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchRegisterWord]
    simp
    interval_cases i <;> simp
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, hK, Bool.false_eq_true, if_true, if_false]
  have f1 : part (branchRegisterWord opc rn) 21 2 = opc.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchRegisterWord]
    simp
    interval_cases i <;> simp
  have f2 : part (branchRegisterWord opc rn) 5 5 = rn.toNat := by
    apply part_eq_of_setWidth
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [branchRegisterWord]
    simp
    interval_cases i <;> simp
  simp only [f1, f2]
  rcases h0 with rfl | rfl | rfl <;> rfl

/-- The `branchRegister` instruction survives a round trip through
`encodeInsn32`/`decodeInsn32`. -/
theorem decode_encode_branchRegister32 (kind : BranchKind) (rn : Nat) (hrn : rn < 32) :
    decodeInsn32 (fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn), (5, 0)])
      = some (.branchRegister rn kind) := by
  rw [fields_branchRegister kind rn,
    decode_branchRegister_word (BitVec.ofNat 2 (branchKindBits kind)) (BitVec.ofNat 5 rn)
      (by cases kind <;> decide)]
  cases kind <;> simp [branchKindBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hrn]

/-- The 64-bit carrier word emitted for `branchRegister`. -/
theorem encodeInsn_branchRegister (kind : BranchKind) (rn : Nat) :
    encodeInsn (.branchRegister rn kind) =
      some ((fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn),
        (5, 0)]).setWidth 64) := rfl

/-- The 64-bit carrier form of the decoder inverts the encoder's carrier form. -/
theorem decode_encode_branchRegister (kind : BranchKind) (rn : Nat) (hrn : rn < 32) :
    decodeInsn ((fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn),
      (5, 0)]).setWidth 64) = some (.branchRegister rn kind) := by
  rw [show decodeInsn ((fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn),
      (5, 0)]).setWidth 64)
      = decodeInsn32 (fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn),
          (5, 0)]) by
    simp [decodeInsn]]
  exact decode_encode_branchRegister32 kind rn hrn

/-- `decodeInsn` inverts `encodeInsn` on `branchRegister`. -/
theorem decode_encode_branchRegisterInsn (kind : BranchKind) (rn : Nat) (hrn : rn < 32) :
    decodeInsn ((encodeInsn (.branchRegister rn kind)).getD 0)
      = some (.branchRegister rn kind) := by
  rw [encodeInsn_branchRegister, Option.getD_some]
  exact decode_encode_branchRegister kind rn hrn

/-- One machine step executes a `branchRegister` instruction whose bytes are at the PC. -/
theorem arm8Next_branchRegister (s : Arm8State) (d : BitVec 64 → Prop)
    (kind : BranchKind) (rn : Nat) (hrn : rn < 32)
    (hbytes : bytesInMemoryHOL s.pc (encodeBytes (.branchRegister rn kind)) s.mem d) :
    arm8Next s = execInsn { s with pc := s.pc + 4 } (.branchRegister rn kind) := by
  rw [arm8Next_encodeBytes s (.branchRegister rn kind)
    ((fields [(9, 428), (2, branchKindBits kind), (11, 1984), (5, rn), (5, 0)]).setWidth 64) d
    (encodeInsn_branchRegister kind rn)
    (decode_encode_branchRegisterInsn kind rn hrn) hbytes]

end Flapjack.Compiler.Encoders.Arm8
