import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldCase
import Flapjack.Compiler.Encoders.Arm8.Machine.MemCase

set_option maxHeartbeats 12000000
set_option maxRecDepth 10000

/-!
# `LoadStoreImmediate`: the `Mem` lowering of `encoder_correct arm8TargetL3`

`arm8_ast` lowers `Mem` to one or two `LoadStoreImmediate` instructions, and
the `e_LoadStoreImmediate` rendering picks between the signed nine-bit and the
scaled twelve-bit forms.  This module records the two emitted words and their
`Encode` equations, for both `MemOp_LOAD` and `MemOp_STORE`; the `Decode`
inverse, the `Run` semantics and the case theorems follow.
-/

namespace Flapjack.Compiler.Encoders.Arm8.L3

open Flapjack Compiler.Encoders.Arm8 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The signed nine-bit `LoadStoreImmediate` word: HOL's `e_data` term
`sz ++ 0b111000 ++ opc ++ 0 ++ imm9 ++ acctype_bit ++ 0 ++ Rn ++ Rt`
(Flapjack infrastructure: a readable abbreviation for a mechanically rendered
term). -/
def arm8LoadStoreImm9Word (sz : BitVec 2) (opc : BitVec 2) (imm9 : BitVec 9)
    (acctypeBit : BitVec 1) (rn rt : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 (sz ++
    BitVec.setWidth 30 (BitVec.ofNat 6 56 ++
      BitVec.setWidth 24 (opc ++
        BitVec.setWidth 22 (BitVec.ofNat 1 0 ++
          BitVec.setWidth 21 (imm9 ++
            BitVec.setWidth 12 (acctypeBit ++
              BitVec.setWidth 11 (BitVec.ofNat 1 0 ++
                BitVec.setWidth 10 (rn ++ rt))))))))

/-- The scaled twelve-bit `LoadStoreImmediate` word: HOL's `e_data` term
`sz ++ 0b111001 ++ opc ++ imm12 ++ Rn ++ Rt` (Flapjack infrastructure). -/
def arm8LoadStoreImm12Word (sz : BitVec 2) (opc : BitVec 2) (imm12 : BitVec 12)
    (rn rt : BitVec 5) : BitVec 32 :=
  BitVec.setWidth 32 (sz ++
    BitVec.setWidth 30 (BitVec.ofNat 6 57 ++
      BitVec.setWidth 24 (opc ++
        BitVec.setWidth 22 (imm12 ++
          BitVec.setWidth 10 (rn ++ rt)))))


/-- `e_load_store` of `LoadStoreImmediate@64` on the scaled twelve-bit path:
the word `arm8LoadStoreImm12Word` (Flapjack infrastructure; the rendered
`e_LoadStoreImmediate` body at `wback = postindex = false`). -/
theorem arm8ELoadStoreImm12_load (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 3)) rn rt) := by
  have hs : BitVec.setWidth 2 (3 : BitVec 64) = (BitVec.ofNat 2 3) := by decide
  have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg


/-- `e_load_store` of `LoadStoreImmediate@64` on the scaled twelve-bit path for
`MemOp_STORE`. -/
theorem arm8ELoadStoreImm12_store (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 3)) rn rt) := by
  have hs : BitVec.setWidth 2 (3 : BitVec 64) = (BitVec.ofNat 2 3) := by decide
  have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

/-- `e_load_store` of `LoadStoreImmediate@64` on the signed nine-bit path for
`MemOp_LOAD`, for either value of the `unsigned_offset` field. -/
theorem arm8ELoadStoreImm9_load (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (3 : BitVec 64) = (BitVec.ofNat 2 3) := by decide
  have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hunpriv : (AccType.AccType_NORMAL == AccType.AccType_UNPRIV) = false := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hsx' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
    rw [beq_iff_eq]; exact hsx
  have hnf : ((!false : Bool) = true) := rfl
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm, hunpriv, hpref,
    hstore, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
    holV2w_one_false]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

/-- `e_load_store` of `LoadStoreImmediate@64` on the signed nine-bit path for
`MemOp_STORE`, for either value of the `unsigned_offset` field. -/
theorem arm8ELoadStoreImm9_store (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (3 : BitVec 64) = (BitVec.ofNat 2 3) := by decide
  have h3 : (BitVec.ofNat 2 3).toNat = 3 := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hunpriv : (AccType.AccType_NORMAL == AccType.AccType_UNPRIV) = false := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hsx' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
    rw [beq_iff_eq]; exact hsx
  have hnf : ((!false : Bool) = true) := rfl
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hnrm, hunpriv, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true, holV2w_one_false]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

/-- `Encode` of the twelve-bit `LoadStoreImmediate@64` load. -/
theorem arm8Encode_loadStoreImm12_load (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 3)) rn rt) :=
  arm8ELoadStoreImm12_load offset rn rt hoff

/-- `Encode` of the twelve-bit `LoadStoreImmediate@64` store. -/
theorem arm8Encode_loadStoreImm12_store (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 3)) rn rt) :=
  arm8ELoadStoreImm12_store offset rn rt hoff

/-- `Encode` of the nine-bit `LoadStoreImmediate@64` load. -/
theorem arm8Encode_loadStoreImm9_load (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_load offset unsigned_offset rn rt hfall hsx

/-- `Encode` of the nine-bit `LoadStoreImmediate@64` store. -/
theorem arm8Encode_loadStoreImm9_store (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_store offset unsigned_offset rn rt hfall hsx


/-- `holV2w` at nine bits roundtrips through the `getElem` bit list. -/
theorem arm8HolV2w_nine (w : BitVec 9) :
    holV2w 9 [w[8], w[7], w[6], w[5], w[4], w[3], w[2], w[1], w[0]] = w :=
  holV2w_holW2v w

/-- `holV2w` at twelve bits roundtrips through the `getElem` bit list. -/
theorem arm8HolV2w_twelve (w : BitVec 12) :
    holV2w 12 [w[11], w[10], w[9], w[8], w[7], w[6], w[5], w[4], w[3], w[2], w[1], w[0]] = w :=
  holV2w_holW2v w

/-- The rendered `Decode` inverts the twelve-bit `LoadStoreImmediate@64` load
word. -/
theorem arm8Decode_loadStoreImm12_load (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, ((BitVec.setWidth 64 imm12) <<< 3), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_one, holV2w_two_three, holV2w_five, arm8HolV2w_twelve,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, LoadStoreImmediate, LoadStoreImmediateN]


/-- The rendered `Decode` inverts the twelve-bit `LoadStoreImmediate@64` store
word. -/
theorem arm8Decode_loadStoreImm12_store (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, ((BitVec.setWidth 64 imm12) <<< 3), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_zero, holV2w_two_three, holV2w_five, arm8HolV2w_twelve,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, LoadStoreImmediate, LoadStoreImmediateN]

/-- The rendered `Decode` inverts the nine-bit `LoadStoreImmediate@64` load
word. -/
theorem arm8Decode_loadStoreImm9_load (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_one, holV2w_two_three, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

/-- The rendered `Decode` inverts the nine-bit `LoadStoreImmediate@64` store
word. -/
theorem arm8Decode_loadStoreImm9_store (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_zero, holV2w_two_three, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]


/-- `Run` of a `LoadStoreImmediate@64` instruction is HOL's
`dfn'LoadStoreImmediate`. -/
theorem arm8Run_loadStoreImmediate (size : BitVec 64) (regsize_word : Bool) (memop : MemOp)
    (acctype : AccType) (signed wb rtunk wback postindex unsigned : Bool)
    (offset : BitVec 64) (n t : BitVec 5) (st : arm8_state) :
    Run (.LoadStore (.«LoadStoreImmediate@64»
        (size, regsize_word, memop, acctype, signed, wb, rtunk, wback, postindex, unsigned,
         offset, n, t))) st =
      «dfn'LoadStoreImmediate» (TN := 64)
        (size, regsize_word, memop, acctype, signed, wb, rtunk, wback, postindex, unsigned,
         offset, n, t) st := by
  simp only [Run]


/-- `Mem` reads the eight little-endian bytes of a word load and returns their
word without changing the state (Flapjack infrastructure; the eight-byte
analogue of `arm8Mem_word` in `Bytes.lean`). -/
theorem arm8Mem_eight (ms : arm8_state) (address : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : ms.MEM address = b0)
    (h1 : ms.MEM (address + BitVec.ofNat 64 1) = b1)
    (h2 : ms.MEM (address + BitVec.ofNat 64 2) = b2)
    (h3 : ms.MEM (address + BitVec.ofNat 64 3) = b3)
    (h4 : ms.MEM (address + BitVec.ofNat 64 4) = b4)
    (h5 : ms.MEM (address + BitVec.ofNat 64 5) = b5)
    (h6 : ms.MEM (address + BitVec.ofNat 64 6) = b6)
    (h7 : ms.MEM (address + BitVec.ofNat 64 7) = b7)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 64) (address, (8, AccType.AccType_NORMAL)) ms =
      (holV2w 64 (holW2v b7 ++ (holW2v b6 ++ (holW2v b5 ++ (holW2v b4 ++
        (holW2v b3 ++ (holW2v b2 ++ (holW2v b1 ++ holW2v b0))))))), ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms address 8 AccType.AccType_NORMAL false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  · exact CheckAlignment_aligned ms address 8 AccType.AccType_NORMAL false hal


/-- The little-endian word of eight bytes, in the OR-of-shifts form `readBytes`
assembles (Flapjack infrastructure; the eight-byte analogue of
`holV2w_word_bytes` in `Bytes.lean`). -/
theorem holV2w_eight_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    holV2w 64 (holW2v b7 ++ (holW2v b6 ++ (holW2v b5 ++ (holW2v b4 ++
      (holW2v b3 ++ (holW2v b2 ++ (holW2v b1 ++ holW2v b0))))))) =
      (BitVec.setWidth 64 b7) <<< (56 : Nat) ||| (BitVec.setWidth 64 b6) <<< (48 : Nat) |||
      (BitVec.setWidth 64 b5) <<< (40 : Nat) ||| (BitVec.setWidth 64 b4) <<< (32 : Nat) |||
      (BitVec.setWidth 64 b3) <<< (24 : Nat) ||| (BitVec.setWidth 64 b2) <<< (16 : Nat) |||
      (BitVec.setWidth 64 b1) <<< (8 : Nat) ||| (BitVec.setWidth 64 b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Flapjack.RiscV.L3.holV2w, holW2v, List.length_append, List.length_map,
    List.length_range]
  rw [getLsbD_holFcpWord]
  simp only [hi, decide_true, Bool.true_and]
  interval_cases i <;> simp [List.getD_eq_getElem?_getD]


/-- The L3 eight-byte read is the source's `readMemWord` value, given the byte
agreement and little-endian addressing (Flapjack infrastructure). -/
theorem arm8Mem_eight_eq_readMemWord (ms : arm8_state) (s : AsmState 64)
    (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i : Nat, i < 8 →
      ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    (Mem (TN := 64) (address, (8, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) address 8 s).1 := by
  have h0 : ms.MEM address = s.mem address := by
    simpa using hmem 0 (by omega)
  have h1 : ms.MEM (address + BitVec.ofNat 64 1) = s.mem (address + BitVec.ofNat 64 1) :=
    hmem 1 (by omega)
  have h2 : ms.MEM (address + BitVec.ofNat 64 2) = s.mem (address + BitVec.ofNat 64 2) :=
    hmem 2 (by omega)
  have h3 : ms.MEM (address + BitVec.ofNat 64 3) = s.mem (address + BitVec.ofNat 64 3) :=
    hmem 3 (by omega)
  have h4 : ms.MEM (address + BitVec.ofNat 64 4) = s.mem (address + BitVec.ofNat 64 4) :=
    hmem 4 (by omega)
  have h5 : ms.MEM (address + BitVec.ofNat 64 5) = s.mem (address + BitVec.ofNat 64 5) :=
    hmem 5 (by omega)
  have h6 : ms.MEM (address + BitVec.ofNat 64 6) = s.mem (address + BitVec.ofNat 64 6) :=
    hmem 6 (by omega)
  have h7 : ms.MEM (address + BitVec.ofNat 64 7) = s.mem (address + BitVec.ofNat 64 7) :=
    hmem 7 (by omega)
  rw [arm8Mem_eight ms address
    (s.mem address)
    (s.mem (address + BitVec.ofNat 64 1))
    (s.mem (address + BitVec.ofNat 64 2))
    (s.mem (address + BitVec.ofNat 64 3))
    (s.mem (address + BitVec.ofNat 64 4))
    (s.mem (address + BitVec.ofNat 64 5))
    (s.mem (address + BitVec.ofNat 64 6))
    (s.mem (address + BitVec.ofNat 64 7))
    h0 h1 h2 h3 h4 h5 h6 h7 hal he0 hel]
  rw [readMemWord_fst address 8 s hbe, readBytes_eight]
  rw [holV2w_eight_bytes]
  simp only [BitVec.ofNat_eq_ofNat]


/-- `Run` of the `LoadStoreImmediate@64` load with no writeback: the machine
reads the eight bytes at `X base + offset` and writes the value into `dest`
(Flapjack infrastructure; the `LoadStoreSingle` clause at the L3 fields). -/
theorem arm8Run_loadStoreImmediate_load (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned, offset, base, dest))) ms =
      (match Mem (TN := 64) ((X (TN := 64) base ms) + offset, (8, .AccType_NORMAL)) ms with
        | (v, s') => «write'X» (TN := 64) ((BitVec.setWidth 64 v), dest) s') := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, ExtendWord, hbase,
    if_false, Bool.false_and, Bool.false_eq_true]

/-- `Run` of the `LoadStoreImmediate@64` store with no writeback: the machine
writes `X dest` into the eight bytes at `X base + offset`.  `unsigned` is the
encoding field only; `dfn'LoadStoreImmediate` ignores it. -/
theorem arm8Run_loadStoreImmediate_store (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned, offset, base, dest))) ms =
      «write'Mem» (TN := 64)
        ((X (TN := 64) dest ms), ((X (TN := 64) base ms) + offset, (8, .AccType_NORMAL))) ms := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, hbase,
    if_false, Bool.false_and, Bool.false_eq_true]

/-- `Run` of the `LoadStoreImmediate@32` load with no writeback: the machine
reads the four bytes at `X base + offset`, zero-extends them to 32 bits, and
writes the value into `dest` (Flapjack infrastructure; the `LoadStoreSingle`
clause at the L3 fields, `ExtendWord` with `TM = TN = 32`). -/
theorem arm8Run_loadStoreImmediate_load32 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'X» (TN := 32)
        ((BitVec.setWidth 32 (Mem (TN := 32) ((X (TN := 64) base ms) + offset, (4, .AccType_NORMAL)) ms).1), dest)
        (Mem (TN := 32) ((X (TN := 64) base ms) + offset, (4, .AccType_NORMAL)) ms).2 := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, ExtendWord, hbase,
    if_false, if_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

/-- `Run` of the `LoadStoreImmediate@32` store with no writeback: the machine
writes the low 32 bits of `X dest` into the four bytes at `X base + offset`
(Flapjack infrastructure). -/
theorem arm8Run_loadStoreImmediate_store32 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'Mem» (TN := 32)
        ((X (TN := 32) dest ms), ((X (TN := 64) base ms) + offset, (4, .AccType_NORMAL))) ms := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, hbase,
    if_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]


/-- `arm8_ast` lowers a load whose offset is its own signed nine-bit form to one
`LoadStoreImmediate@64` (Flapjack infrastructure; the `arm8_load_store_ast`
one-instruction branch). -/
theorem arm8Ast_load_single (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .load dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst]
  simp [h1]


/-- `arm8_ast` lowers a store whose offset is its own signed nine-bit form to one
`LoadStoreImmediate@64` (Flapjack infrastructure). -/
theorem arm8Ast_store_single (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .store dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst]
  simp [h1]


/-- The one-instruction load lowering encodes to four bytes. -/
theorem arm8Enc_load_single_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single dest base off hsx]
  simp [arm8Encode_length]

/-- The one-instruction store lowering encodes to four bytes. -/
theorem arm8Enc_store_single_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single dest base off hsx]
  simp [arm8Encode_length]

/-- The little-endian word of four bytes, in the OR-of-shifts form `readBytes`
assembles (Flapjack infrastructure; the four-byte analogue of
`holV2w_eight_bytes`). -/
theorem holV2w_four_bytes (b0 b1 b2 b3 : BitVec 8) :
    holV2w 32 (holW2v b3 ++ (holW2v b2 ++ (holW2v b1 ++ holW2v b0))) =
      (BitVec.setWidth 32 b3) <<< (24 : Nat) ||| (BitVec.setWidth 32 b2) <<< (16 : Nat) |||
      (BitVec.setWidth 32 b1) <<< (8 : Nat) ||| (BitVec.setWidth 32 b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Flapjack.RiscV.L3.holV2w, holW2v, List.length_append, List.length_map,
    List.length_range]
  rw [getLsbD_holFcpWord]
  simp only [hi, decide_true, Bool.true_and]
  interval_cases i <;> simp [List.getD_eq_getElem?_getD]

/-- The zero-extended four-byte read is the 64-bit OR-of-shifts form
(Flapjack infrastructure). -/
theorem arm8SetWidth64_four (b0 b1 b2 b3 : BitVec 8) :
    BitVec.setWidth 64 (holV2w 32 (holW2v b3 ++ (holW2v b2 ++ (holW2v b1 ++ holW2v b0)))) =
      (BitVec.setWidth 64 b3) <<< (24 : Nat) ||| (BitVec.setWidth 64 b2) <<< (16 : Nat) |||
      (BitVec.setWidth 64 b1) <<< (8 : Nat) ||| (BitVec.setWidth 64 b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w, holW2v, List.length_append, List.length_map,
    List.length_range]
  rw [BitVec.getLsbD_setWidth, getLsbD_holFcpWord]
  simp only [hj, decide_true, Bool.true_and]
  interval_cases j <;> simp [List.getD_eq_getElem?_getD]


/-- `Mem` reads the four little-endian bytes of a 32-bit load and returns their
word without changing the state (Flapjack infrastructure; the four-byte
analogue of `arm8Mem_eight`). -/
theorem arm8Mem_four (ms : arm8_state) (address : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (h0 : ms.MEM address = b0)
    (h1 : ms.MEM (address + BitVec.ofNat 64 1) = b1)
    (h2 : ms.MEM (address + BitVec.ofNat 64 2) = b2)
    (h3 : ms.MEM (address + BitVec.ofNat 64 3) = b3)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 32) (address, (4, AccType.AccType_NORMAL)) ms =
      (holV2w 32 (holW2v b3 ++ (holW2v b2 ++ (holW2v b1 ++ holW2v b0))), ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms address 4 AccType.AccType_NORMAL false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false]
    rw [h0, h1, h2, h3]
  · exact CheckAlignment_aligned ms address 4 AccType.AccType_NORMAL false hal

/-- The zero-extended four-byte L3 read is the source's `readMemWord` value,
given the byte agreement and little-endian addressing (Flapjack
infrastructure). -/
theorem arm8Mem_four_eq_readMemWord (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i, i < 4 → ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    BitVec.setWidth 64 (Mem (TN := 32) (address, (4, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) address 4 s).1 := by
  have h0 : ms.MEM address = s.mem address := by simpa using hmem 0 (by omega)
  have h1 : ms.MEM (address + BitVec.ofNat 64 1) = s.mem (address + BitVec.ofNat 64 1) :=
    hmem 1 (by omega)
  have h2 : ms.MEM (address + BitVec.ofNat 64 2) = s.mem (address + BitVec.ofNat 64 2) :=
    hmem 2 (by omega)
  have h3 : ms.MEM (address + BitVec.ofNat 64 3) = s.mem (address + BitVec.ofNat 64 3) :=
    hmem 3 (by omega)
  rw [arm8Mem_four ms address (s.mem address) (s.mem (address + BitVec.ofNat 64 1))
    (s.mem (address + BitVec.ofNat 64 2)) (s.mem (address + BitVec.ofNat 64 3)) h0 h1 h2 h3
    hal he0 hel]
  rw [readMemWord_fst address 4 s hbe]
  rw [readBytes_four]
  exact arm8SetWidth64_four _ _ _ _


/-- The L3 eight-byte read is the source's `readMemWord` value, from the state
relation and the eight-address domain fact alone (Flapjack infrastructure). -/
theorem arm8Mem_eight_value (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hrel : ∀ a, s.memDomain a → ms.MEM a = s.mem a)
    (hdom : ∀ k, k < 8 → s.memDomain (address + BitVec.ofNat 64 k)) :
    (Mem (TN := 64) (address, (8, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) address 8 s).1 :=
  arm8Mem_eight_eq_readMemWord ms s address hal he0 hel hbe
    (fun i hi => hrel _ (hdom i hi))


/-- The rendered `Aligned` at eight bytes is `8 ∣ a.toNat`. -/
theorem arm8Aligned_eight_iff (a : BitVec 64) :
    Aligned (TN := 64) (a, 8) = true ↔ a.toNat % 8 = 0 := by
  simp only [Aligned, Align, beq_iff_eq]
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at h1
    have hle : 8 * (a.toNat / 8) ≤ a.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_mul_le_self a.toNat 8
    have hlt : 8 * (a.toNat / 8) < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hlt] at h1
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    have hdvd : 8 ∣ a.toNat := Nat.dvd_of_mod_eq_zero h
    have heq : 8 * (a.toNat / 8) = a.toNat := by
      rw [Nat.mul_comm]; exact Nat.div_mul_cancel hdvd
    have hlt : 8 * (a.toNat / 8) < 2 ^ 64 := by rw [heq]; exact a.isLt
    rw [Nat.mod_eq_of_lt hlt, heq]

/-- `holAligned` at three bits is the rendered `Aligned` at eight bytes. -/
theorem arm8Aligned_eight_of_holAligned (a : BitVec 64)
    (h : holAligned 3 a = true) : Aligned (TN := 64) (a, 8) = true := by
  rw [arm8Aligned_eight_iff]
  have h' := (holAligned_iff 3 a).mp h
  simpa using h'


/-- A successful eight-byte store has its effective address eight-byte aligned,
derived from `asm_step`'s `¬ s2.failed` (Flapjack infrastructure). -/
theorem arm8MemStore_aligned (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 8) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h3 : holLOG2 8 = 3 := holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩
  rw [h3] at hal
  exact arm8Aligned_eight_of_holAligned _ (by simpa using hal)

/-- A successful eight-byte store has its eight addresses in the source memory
domain (Flapjack infrastructure; the store analogue of `arm8MemLoad_domain`). -/
theorem arm8MemStore_domain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact writeMemWord_domain (s1.regs base + off) 8 (s1.regs r) s1 hbe (not_of_eq_false hf)

/-- A successful eight-byte load has its effective address aligned: the source
`mem_load` asserts `aligned (LOG2 n)`, and `asm_step` carries `¬ s2.failed`
(Flapjack infrastructure; the alignment half of `memLoadDomain`). -/
theorem arm8MemLoad_aligned (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 8) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h3 : holLOG2 8 = 3 := holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩
  rw [h3] at hal
  exact arm8Aligned_eight_of_holAligned _ (by simpa using hal)


/-- A successful eight-byte load has its eight addresses in the source memory
domain (Flapjack infrastructure; the domain half of `memLoadDomain`, at the
L3 `asmUpd` shape). -/
theorem arm8MemLoad_domain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have h := memLoadDomain op r base off s1 s2 3 pc (by simpa using hspec) hupd hbe hok
  simpa using h


/-- Extracting the low nine bits of a 64-bit word is its nine-bit truncation. -/
theorem arm8HolWordExtract_nine (off : BitVec 64) :
    holWordExtract 9 8 0 off = BitVec.ofNat 9 off.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [Flapjack.RiscV.L3.holWordExtract, BitVec.toNat_ofNat, BitVec.toNat_setWidth]

/-- An offset that is its own signed nine-bit form is recovered from the nine
bits `e_LoadStoreImmediate` extracts. -/
theorem arm8SignExtend_nine (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    BitVec.signExtend 64 (holWordExtract 9 8 0 off) = off := by
  rw [arm8HolWordExtract_nine, ← hsx]



/-- The `asm_ok` facts a `.mem` instruction carries: both registers and the
offset are accepted by `arm8ConfigL3`. -/
theorem arm8MemLoadOkExact (destination base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem .load destination (.addr base off))) arm8ConfigL3 = true) :
    asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
  have h' := h
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩

/-- `arm8Mem_eight` fed by a per-index byte hypothesis rather than eight
explicit byte terms (Flapjack infrastructure). -/
theorem arm8Mem_eight_of_bytes (ms : arm8_state) (address : BitVec 64)
    (m : BitVec 64 → BitVec 8)
    (hbytes : ∀ i, i < 8 →
      ms.MEM (address + BitVec.ofNat 64 i) = m (address + BitVec.ofNat 64 i))
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 64) (address, (8, AccType.AccType_NORMAL)) ms =
      (holV2w 64 (holW2v (m (address + BitVec.ofNat 64 7)) ++
        (holW2v (m (address + BitVec.ofNat 64 6)) ++
        (holW2v (m (address + BitVec.ofNat 64 5)) ++
        (holW2v (m (address + BitVec.ofNat 64 4)) ++
        (holW2v (m (address + BitVec.ofNat 64 3)) ++
        (holW2v (m (address + BitVec.ofNat 64 2)) ++
        (holW2v (m (address + BitVec.ofNat 64 1)) ++
        holW2v (m address)))))))), ms) := by
  have h0 : ms.MEM address = m address := by simpa using hbytes 0 (by omega)
  exact arm8Mem_eight ms address (m address) (m (address + BitVec.ofNat 64 1))
    (m (address + BitVec.ofNat 64 2)) (m (address + BitVec.ofNat 64 3))
    (m (address + BitVec.ofNat 64 4)) (m (address + BitVec.ofNat 64 5))
    (m (address + BitVec.ofNat 64 6)) (m (address + BitVec.ofNat 64 7))
    h0 (hbytes 1 (by omega)) (hbytes 2 (by omega)) (hbytes 3 (by omega))
    (hbytes 4 (by omega)) (hbytes 5 (by omega)) (hbytes 6 (by omega))
    (hbytes 7 (by omega)) hal he0 hel

/-- The eight-byte `Mem` pair at an address whose bytes agree with the source
(Flapjack infrastructure). -/
theorem arm8Mem_eight_pair (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i, i < 8 →
      ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    Mem (TN := 64) (address, (8, AccType.AccType_NORMAL)) ms =
      ((readMemWord (resultWidth := 64) address 8 s).1, ms) := by
  have hp := arm8Mem_eight_of_bytes ms address s.mem hmem hal he0 hel
  have hv := arm8Mem_eight_eq_readMemWord ms s address hal he0 hel hbe hmem
  rw [hp] at hv ⊢
  exact Prod.ext hv rfl

/-! ## The eight-byte write

`write'Mem` writes each byte from the bit field `holField (8i+7) (8i)` of the
value, while the source's `writeMemWord` shifts the value by eight bits per
step.  `arm8HolByte` identifies the two byte extractions; `holUpdate_eight`
identifies the nested `holUpdate` chain with the if-chain `writeMemN` uses. -/

/-- `holUpdate` at its application form (Flapjack infrastructure: the rendered
`holUpdate` is an abbreviation, so `rw [holUpdate]` does not fire). -/
theorem holUpdate_apply (a : BitVec 64) (b : BitVec 8) (f : BitVec 64 → BitVec 8)
    (c : BitVec 64) :
    holUpdate a b f c = if a = c then b else f c := rfl

/-- Distinct small offsets give distinct addresses (Flapjack infrastructure). -/
theorem arm8Add_ne_add {address : BitVec 64} {i j : Nat} (hi : i < 8) (hj : j < 8)
    (hij : i ≠ j) : address + BitVec.ofNat 64 i ≠ address + BitVec.ofNat 64 j := by
  intro h
  apply hij
  bv_omega

/-- A non-zero offset below eight moves the address (Flapjack infrastructure). -/
theorem arm8Add_ne {address : BitVec 64} {k : Nat} (hk : k < 8) (h : k ≠ 0) :
    address + BitVec.ofNat 64 k ≠ address := by
  intro hh
  have hz : address + BitVec.ofNat 64 k = address + BitVec.ofNat 64 0 := by
    simpa using hh
  have := (BitVec.add_right_inj address).mp hz
  have hto := congrArg BitVec.toNat this
  simp only [BitVec.toNat_ofNat] at hto
  omega

/-- The eight nested `holUpdate`s `write'Mem` builds are the if-chain
`writeMemN` uses (Flapjack infrastructure). -/
theorem holUpdate_eight (address : BitVec 64) (f : BitVec 64 → BitVec 8)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (x : BitVec 64) :
    holUpdate (address + 7#64) b7
      (holUpdate (address + 6#64) b6
        (holUpdate (address + 5#64) b5
          (holUpdate (address + 4#64) b4
            (holUpdate (address + 3#64) b3
              (holUpdate (address + 2#64) b2
                (holUpdate (address + 1#64) b1
                  (holUpdate address b0 f))))))) x =
      if x = address then b0
      else if x = address + 1#64 then b1
      else if x = address + 2#64 then b2
      else if x = address + 3#64 then b3
      else if x = address + 4#64 then b4
      else if x = address + 5#64 then b5
      else if x = address + 6#64 then b6
      else if x = address + 7#64 then b7 else f x := by
  simp only [holUpdate_apply]
  by_cases e0 : x = address
  · subst e0; simp
  by_cases e1 : x = address + 1#64
  · subst e1; simp
  by_cases e2 : x = address + 2#64
  · subst e2; simp
  by_cases e3 : x = address + 3#64
  · subst e3; simp
  by_cases e4 : x = address + 4#64
  · subst e4; simp
  by_cases e5 : x = address + 5#64
  · subst e5; simp
  by_cases e6 : x = address + 6#64
  · subst e6; simp
  by_cases e7 : x = address + 7#64
  · subst e7; simp
  · have h0 : address ≠ x := fun h => e0 h.symm
    have h1 : address + 1#64 ≠ x := fun h => e1 h.symm
    have h2 : address + 2#64 ≠ x := fun h => e2 h.symm
    have h3 : address + 3#64 ≠ x := fun h => e3 h.symm
    have h4 : address + 4#64 ≠ x := fun h => e4 h.symm
    have h5 : address + 5#64 ≠ x := fun h => e5 h.symm
    have h6 : address + 6#64 ≠ x := fun h => e6 h.symm
    have h7 : address + 7#64 ≠ x := fun h => e7 h.symm
    simp [e0, e1, e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7]

/-- The `m`-th entry of `holW2v value` is the `63 - m`-th bit. -/
theorem holW2v_getElem? (value : BitVec 64) (m : Nat) :
    (holW2v value)[m]? = if m < 64 then some (value.getLsbD (63 - m)) else none := by
  simp only [holW2v, List.getElem?_map]
  by_cases hm : m < 64
  · simp [hm]
  · simp [hm]

/-- `holField` at eight bits has length eight (Flapjack infrastructure). -/
theorem holField_eight_length (value : BitVec 64) (i : Nat) (hi : i < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (64 - 8 * i < 8) := by omega
  have hmin : min (64 - 8 * i) 64 = 64 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length, hmin, hge, if_false,
    List.length_take, List.length_drop]
  omega

/-- The `7 - j`-th entry of the eight-bit field is the `8i + j`-th bit of the
value (Flapjack infrastructure). -/
theorem holField_eight_getElem? (value : BitVec 64) (i j : Nat) (hi : i < 8) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (64 - 8 * i < 8) := by omega
  have hmin : min (64 - 8 * i) 64 = 64 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length, List.length_take, hmin, hge,
    if_false]
  rw [List.getElem?_drop]
  rw [show 64 - 8 * i - 8 + (7 - j) = 63 - 8 * i - j by omega]
  rw [List.getElem?_take_of_lt (by omega : 63 - 8 * i - j < 64 - 8 * i)]
  rw [holW2v_getElem?]
  have hlt : 63 - 8 * i - j < 64 := by omega
  have hidx : 63 - (63 - 8 * i - j) = 8 * i + j := by omega
  simp only [hlt, if_true, hidx]

/-- The byte `write'Mem` stores at `address + i` is the byte `writeMemN` stores
there (Flapjack infrastructure). -/
theorem arm8HolByte (value : BitVec 64) (i : Nat) (hi : i < 8) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w]
  rw [getLsbD_holFcpWord]
  have hlen := holField_eight_length value i hi
  simp only [hj, decide_true, Bool.true_and, hlen, show 8 - 1 - j = 7 - j by omega]
  rw [List.getD_eq_getElem?_getD, holField_eight_getElem? value i j hi hj]
  simp only [Option.getD_some, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]


/-- The L3 eight-byte write agrees with the machine's eight-byte write at every
byte (Flapjack infrastructure; the write analogue of `arm8Mem_eight_pair`). -/
theorem arm8WriteMem_eight (ms : arm8_state) (address : BitVec 64) (value : BitVec 64)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) :
    («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms).MEM x =
      (writeMemN (memState ms.MEM) 8 address value).mem x := by
  simp only [«write'Mem», writeMemN, memState]
  simp [holFor, CheckAlignment_aligned ms address 8 acctype true hal,
    BigEndian_false ms hel he0]
  have hb0 : holV2w 8 (holField 7 0 (holW2v value)) = BitVec.setWidth 8 value := by
    simpa using arm8HolByte value 0 (by decide)
  have hb1 : holV2w 8 (holField 15 8 (holW2v value)) = BitVec.setWidth 8 (value >>> 8) := by
    simpa using arm8HolByte value 1 (by decide)
  have hb2 : holV2w 8 (holField 23 16 (holW2v value)) = BitVec.setWidth 8 (value >>> 16) := by
    simpa using arm8HolByte value 2 (by decide)
  have hb3 : holV2w 8 (holField 31 24 (holW2v value)) = BitVec.setWidth 8 (value >>> 24) := by
    simpa using arm8HolByte value 3 (by decide)
  have hb4 : holV2w 8 (holField 39 32 (holW2v value)) = BitVec.setWidth 8 (value >>> 32) := by
    simpa using arm8HolByte value 4 (by decide)
  have hb5 : holV2w 8 (holField 47 40 (holW2v value)) = BitVec.setWidth 8 (value >>> 40) := by
    simpa using arm8HolByte value 5 (by decide)
  have hb6 : holV2w 8 (holField 55 48 (holW2v value)) = BitVec.setWidth 8 (value >>> 48) := by
    simpa using arm8HolByte value 6 (by decide)
  have hb7 : holV2w 8 (holField 63 56 (holW2v value)) = BitVec.setWidth 8 (value >>> 56) := by
    simpa using arm8HolByte value 7 (by decide)
  rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  exact holUpdate_eight address ms.MEM _ _ _ _ _ _ _ _ x


/-- The L3 eight-byte write leaves memory outside its eight addresses alone
(Flapjack infrastructure). -/
theorem arm8WriteMem_eight_out (ms : arm8_state) (address : BitVec 64) (value : BitVec 64)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) (hx : ∀ k, k < 8 → x ≠ address + BitVec.ofNat 64 k) :
    («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms).MEM x = ms.MEM x := by
  rw [arm8WriteMem_eight ms address value acctype hal he0 hel x]
  have h0 : x ≠ address := by simpa using hx 0 (by omega)
  have h1 : x ≠ address + 1#64 := by simpa using hx 1 (by omega)
  have h2 : x ≠ address + 2#64 := by simpa using hx 2 (by omega)
  have h3 : x ≠ address + 3#64 := by simpa using hx 3 (by omega)
  have h4 : x ≠ address + 4#64 := by simpa using hx 4 (by omega)
  have h5 : x ≠ address + 5#64 := by simpa using hx 5 (by omega)
  have h6 : x ≠ address + 6#64 := by simpa using hx 6 (by omega)
  have h7 : x ≠ address + 7#64 := by simpa using hx 7 (by omega)
  simp only [writeMemN, memState]
  simp [h0, h1, h2, h3, h4, h5, h6, h7]


/-- `write'Mem` changes only `MEM` (Flapjack infrastructure). -/
theorem arm8WriteMem_only_mem (ms : arm8_state) (value : BitVec 64) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 8) = true) :
    («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 8 acctype true hal]

/-- The `.mem .store` `asm_ok` facts: both registers and the offset are
accepted by `arm8ConfigL3`. -/
theorem arm8MemStoreOkExact (destination base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem .store destination (.addr base off))) arm8ConfigL3 = true) :
    asmRegOkExact destination arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
  have h' := h
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
  exact ⟨h'.1.1, h'.1.2, h'.2⟩


/-! ## The four-byte `Mem` helpers -/

theorem holW2v_length32 (value : BitVec 32) : (holW2v value).length = 32 := by
  simp [holW2v]

theorem holW2v_getElem?_32 (value : BitVec 32) (m : Nat) :
    (holW2v value)[m]? = if m < 32 then some (value.getLsbD (31 - m)) else none := by
  simp only [holW2v, List.getElem?_map]
  by_cases hm : m < 32
  · simp [hm]
  · simp [hm]

theorem holField_four_length (value : BitVec 32) (i : Nat) (hi : i < 4) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (32 - 8 * i < 8) := by omega
  have hmin : min (32 - 8 * i) 32 = 32 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length32, hmin, hge, if_false,
    List.length_take, List.length_drop]
  omega

theorem holField_four_getElem? (value : BitVec 32) (i j : Nat) (hi : i < 4) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (32 - 8 * i < 8) := by omega
  have hmin : min (32 - 8 * i) 32 = 32 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length32, List.length_take, hmin, hge,
    if_false]
  rw [List.getElem?_drop]
  rw [show 32 - 8 * i - 8 + (7 - j) = 31 - 8 * i - j by omega]
  rw [List.getElem?_take_of_lt (by omega : 31 - 8 * i - j < 32 - 8 * i)]
  rw [holW2v_getElem?_32]
  have hlt : 31 - 8 * i - j < 32 := by omega
  have hidx : 31 - (31 - 8 * i - j) = 8 * i + j := by omega
  simp only [hlt, if_true, hidx]

/-- The byte `write'Mem` stores at `address + i` for a 32-bit value
(Flapjack infrastructure; the four-byte analogue of `arm8HolByte`). -/
theorem arm8HolByte32 (value : BitVec 32) (i : Nat) (hi : i < 4) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w]
  rw [getLsbD_holFcpWord]
  have hlen := holField_four_length value i hi
  simp only [hj, decide_true, Bool.true_and, hlen, show 8 - 1 - j = 7 - j by omega]
  rw [List.getD_eq_getElem?_getD, holField_four_getElem? value i j hi hj]
  simp only [Option.getD_some, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]

/-- The low four bytes of `setWidth 64 (setWidth 32 w)` are those of `w`
(Flapjack infrastructure). -/
theorem arm8ByteSetWidth32_64 (w : BitVec 64) (i : Nat) (hi : i < 4) :
    (((BitVec.setWidth 64 (BitVec.setWidth 32 w)) >>> (8 * i : Nat)).setWidth 8) =
      ((w >>> (8 * i : Nat)).setWidth 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  have hk : 8 * i + j < 32 := by omega
  have h64 : 8 * i + j < 64 := by omega
  simp [hk, h64]

/-- A four-byte machine write ignores the `setWidth 32`-then-`setWidth 64`
round trip of its value (Flapjack infrastructure). -/
theorem writeMemN_four_setWidth32 (s : Arm8State) (a w : BitVec 64) (x : BitVec 64) :
    (writeMemN s 4 a (BitVec.setWidth 64 (BitVec.setWidth 32 w))).mem x =
      (writeMemN s 4 a w).mem x := by
  simp only [writeMemN]
  rw [arm8ByteSetWidth32_64 w 0 (by decide), arm8ByteSetWidth32_64 w 1 (by decide),
    arm8ByteSetWidth32_64 w 2 (by decide), arm8ByteSetWidth32_64 w 3 (by decide)]

theorem holUpdate_four (address : BitVec 64) (f : BitVec 64 → BitVec 8)
    (b0 b1 b2 b3 : BitVec 8) (x : BitVec 64) :
    holUpdate (address + 3#64) b3
      (holUpdate (address + 2#64) b2
        (holUpdate (address + 1#64) b1
          (holUpdate address b0 f))) x =
      if x = address then b0
      else if x = address + 1#64 then b1
      else if x = address + 2#64 then b2
      else if x = address + 3#64 then b3 else f x := by
  simp only [holUpdate_apply]
  by_cases e0 : x = address
  · subst e0; simp
  by_cases e1 : x = address + 1#64
  · subst e1; simp
  by_cases e2 : x = address + 2#64
  · subst e2; simp
  by_cases e3 : x = address + 3#64
  · subst e3; simp
  · have h0 : address ≠ x := fun h => e0 h.symm
    have h1 : address + 1#64 ≠ x := fun h => e1 h.symm
    have h2 : address + 2#64 ≠ x := fun h => e2 h.symm
    have h3 : address + 3#64 ≠ x := fun h => e3 h.symm
    simp [e0, e1, e2, e3, h0, h1, h2, h3]

theorem arm8WriteMem_four (ms : arm8_state) (address : BitVec 64) (value : BitVec 32)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) :
    («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms).MEM x =
      (writeMemN (memState ms.MEM) 4 address (BitVec.setWidth 64 value)).mem x := by
  simp only [«write'Mem», writeMemN, memState]
  simp [holFor, CheckAlignment_aligned ms address 4 acctype true hal,
    BigEndian_false ms hel he0]
  have hb0 : holV2w 8 (holField 7 0 (holW2v value)) = BitVec.setWidth 8 value := by
    simpa using arm8HolByte32 value 0 (by decide)
  have hb1 : holV2w 8 (holField 15 8 (holW2v value)) = BitVec.setWidth 8 (value >>> 8) := by
    simpa using arm8HolByte32 value 1 (by decide)
  have hb2 : holV2w 8 (holField 23 16 (holW2v value)) = BitVec.setWidth 8 (value >>> 16) := by
    simpa using arm8HolByte32 value 2 (by decide)
  have hb3 : holV2w 8 (holField 31 24 (holW2v value)) = BitVec.setWidth 8 (value >>> 24) := by
    simpa using arm8HolByte32 value 3 (by decide)
  rw [hb0, hb1, hb2, hb3]
  exact holUpdate_four address ms.MEM _ _ _ _ x

theorem arm8WriteMem_four_out (ms : arm8_state) (address : BitVec 64) (value : BitVec 32)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) (hx : ∀ k, k < 4 → x ≠ address + BitVec.ofNat 64 k) :
    («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms).MEM x = ms.MEM x := by
  rw [arm8WriteMem_four ms address value acctype hal he0 hel x]
  have h0 : x ≠ address := by simpa using hx 0 (by omega)
  have h1 : x ≠ address + 1#64 := by simpa using hx 1 (by omega)
  have h2 : x ≠ address + 2#64 := by simpa using hx 2 (by omega)
  have h3 : x ≠ address + 3#64 := by simpa using hx 3 (by omega)
  simp only [writeMemN, memState]
  simp [h0, h1, h2, h3]

theorem arm8WriteMem_only_mem_four (ms : arm8_state) (value : BitVec 32) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 4) = true) :
    («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 4 acctype true hal]

theorem arm8Aligned_four_of_holAligned (a : BitVec 64)
    (h : holAligned 2 a = true) : Aligned (TN := 64) (a, 4) = true := by
  rw [Aligned_four_iff]
  have h' := (holAligned_iff 2 a).mp h
  simpa using h'

theorem arm8MemStore_aligned_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 4) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h2 : holLOG2 4 = 2 := holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩
  rw [h2] at hal
  exact arm8Aligned_four_of_holAligned _ (by simpa using hal)

theorem arm8MemStore_domain_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact writeMemWord_domain (s1.regs base + off) 4 (s1.regs r) s1 hbe (not_of_eq_false hf)

theorem arm8MemLoad_aligned_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 4) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h2 : holLOG2 4 = 2 := holLOG_UNIQUE 2 4 2 ⟨by decide, by decide⟩
  rw [h2] at hal
  exact arm8Aligned_four_of_holAligned _ (by simpa using hal)

theorem arm8MemLoad_domain_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have h := memLoadDomain op r base off s1 s2 2 pc (by simpa using hspec) hupd hbe hok
  simpa using h

theorem arm8Mem_four_of_bytes (ms : arm8_state) (address : BitVec 64)
    (m : BitVec 64 → BitVec 8)
    (hbytes : ∀ i, i < 4 →
      ms.MEM (address + BitVec.ofNat 64 i) = m (address + BitVec.ofNat 64 i))
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 32) (address, (4, AccType.AccType_NORMAL)) ms =
      (holV2w 32 (holW2v (m (address + BitVec.ofNat 64 3)) ++
        (holW2v (m (address + BitVec.ofNat 64 2)) ++
        (holW2v (m (address + BitVec.ofNat 64 1)) ++ holW2v (m address)))), ms) := by
  have h0 : ms.MEM address = m address := by simpa using hbytes 0 (by omega)
  exact arm8Mem_four ms address (m address) (m (address + BitVec.ofNat 64 1))
    (m (address + BitVec.ofNat 64 2)) (m (address + BitVec.ofNat 64 3))
    h0 (hbytes 1 (by omega)) (hbytes 2 (by omega)) (hbytes 3 (by omega)) hal he0 hel

theorem arm8X32_of_valid (ms : arm8_state) {n : Nat} (hn : n ≠ 31) (hlt : n < 32) :
    X (TN := 32) (BitVec.ofNat 5 n) ms = BitVec.setWidth 32 (ms.REG (BitVec.ofNat 5 n)) := by
  have hne : BitVec.ofNat 5 n ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hn32 : n % 2 ^ 5 = n := Nat.mod_eq_of_lt (by omega)
    omega
  simp only [X]
  split
  · exact absurd (by simpa using ‹(BitVec.ofNat 5 n == 31#5) = true›) hne
  · rfl

theorem arm8WriteX32_of_valid (s : arm8_state) (v : BitVec 32) {n : Nat}
    (hn : n ≠ 31) (hlt : n < 32) :
    «write'X» (TN := 32) (v, BitVec.ofNat 5 n) s =
      { s with REG := holUpdate (BitVec.ofNat 5 n) (BitVec.setWidth 64 v) s.REG } := by
  have hne : BitVec.ofNat 5 n ≠ 31#5 := by
    intro hh
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hn32 : n % 2 ^ 5 = n := Nat.mod_eq_of_lt (by omega)
    omega
  have hcond : (!(BitVec.ofNat 5 n == 31#5)) = true := by
    cases hb : (BitVec.ofNat 5 n == 31#5)
    · rfl
    · exact absurd (by simpa using hb) hne
  simp only [«write'X», hcond, if_true]

/-! ## The 32-bit `LoadStoreImmediate@32` layer

The `.load32`/`.store32` lowering emits `LoadStoreImmediate@32` (`size = 2`,
`regsize_word = true`).  Its word shapes are the same `arm8LoadStoreImm12Word`/
`arm8LoadStoreImm9Word` at `sz = 2`, and the scaled form shifts by two rather
than three bits. -/

theorem arm8ELoadStoreImm12_load32 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) :
    e_load_store (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 2)) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = (BitVec.ofNat 2 2) := by decide
  have h2 : (BitVec.ofNat 2 2).toNat = 2 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hload, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_load32 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) :
    Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 2)) rn rt) :=
  arm8ELoadStoreImm12_load32 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_load32 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 2), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_one, holV2w_two_two, holV2w_five, arm8HolV2w_twelve,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm12_store32 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) :
    e_load_store (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 2)) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = (BitVec.ofNat 2 2) := by decide
  have h2 : (BitVec.ofNat 2 2).toNat = 2 := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_store32 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2) :
    Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 2)) rn rt) :=
  arm8ELoadStoreImm12_store32 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_store32 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 2), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_zero, holV2w_two_two, holV2w_five, arm8HolV2w_twelve,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm9_load32 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = (BitVec.ofNat 2 2) := by decide
  have h2 : (BitVec.ofNat 2 2).toNat = 2 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hunpriv : (AccType.AccType_NORMAL == AccType.AccType_UNPRIV) = false := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hsx' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
    rw [beq_iff_eq]; exact hsx
  have hnf : ((!false : Bool) = true) := rfl
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hload, hnrm, hunpriv, hpref,
    hstore, Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
    holV2w_one_false]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_load32 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_load32 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_load32 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_one, holV2w_two_two, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm9_store32 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 32 2) = (BitVec.ofNat 2 2) := by decide
  have h2 : (BitVec.ofNat 2 2).toNat = 2 := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hsx' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
    rw [beq_iff_eq]; exact hsx
  have hnf : ((!false : Bool) = true) := rfl
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hstore, hnrm, hpref,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_store32 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 2))) <<< 2)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_store32 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_store32 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_zero, holV2w_two_two, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8Ast_load_single32 (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .load32 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst32]
  simp [h1]

theorem arm8Ast_store_single32 (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .store32 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst32]
  simp [h1]

theorem arm8Enc_load_single32_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single32 dest base off hsx]
  simp [arm8Encode_length]

theorem arm8Enc_store_single32_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single32 dest base off hsx]
  simp [arm8Encode_length]
/-- The `.mem .load32` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path: `arm8_ast`'s `load32` lowering emits one
`LoadStoreImmediate@32` (`size = 2`, `regsize_word = true`), and
`e_LoadStoreImmediate` reaches its `imm9` clause only when the scaled twelve-bit
clause does not fire (`hfall`) and `off` is its own signed nine-bit form (`hsx`).
The machine reads four bytes and zero-extends them to the register width.  The
statement awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load32_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2)) = false) :
    CaseGoal (.inst (.mem .load32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd : asmRegOkExact dest arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2, h'.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load32 = memLoad (width := 64) 4 := rfl
  have hal4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemLoad_aligned_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_load_single32 dest base off hsx
  have henc : arm8Enc (.inst (.mem .load32 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_load32 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single32_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
    (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 off)
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [arm8SignExtend_nine off hsx] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 :=
    BitVec.setWidth 64 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_four_eq_readMemWord ms s1 (s1.regs base + off) hal4 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
  have hpairbh : Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    have h1 := arm8Mem_four_of_bytes { ms with branch_hint := none } (s1.regs base + off)
      ms.MEM (fun i hi => rfl) hal4 he0 hel
    have h2 := arm8Mem_four_of_bytes ms (s1.regs base + off) ms.MEM
      (fun i hi => rfl) hal4 he0 hel
    rw [h1, h2]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load32 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [show BitVec.setWidth 32 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 =
        (Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 by simp]
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .load32 dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd4]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [hv]
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .load32 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom hs2regs
  · rfl
  · intro x hx
    show ms.MEM x = s2.mem x
    rw [hs2mem x]
    exact hmem x hx
  · intro x hx
    show ms.MEM x = ms.MEM x
    rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 dest) then v
      else ms.REG (BitVec.ofNat 5 dest)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4' : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4'

/-- The `.mem .store32` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path: the `store32` lowering emits one `LoadStoreImmediate@32`
with `opc = 0`, and the branch conditions are the load case's (`hsx`, `hfall`)
with the four-byte write in place of the eight-byte one.  The statement awaits
source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store32_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2)) = false) :
    CaseGoal (.inst (.mem .store32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd : asmRegOkExact dest arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2, h'.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store32 = memStore (width := 64) 4 := rfl
  have hal4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemStore_aligned_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single32 dest base off hsx
  have henc : arm8Enc (.inst (.mem .store32 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_store32 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single32_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
    (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 off)
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [arm8SignExtend_nine off hsx] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := s1.regs dest
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hXd : X (TN := 32) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 32 (s1.regs dest) := by
    rw [arm8X32_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store32 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_four _ _ _ _ hal4]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store32 dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 4 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store32 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_four { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL hal4 he0 hel x]
    rw [writeMemN_four_setWidth32 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_four s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_four_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL hal4 he0 hel x
      (fun k hk h => hx (h ▸ hdom k hk))
  · intro k hk hkne
    show ms.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k)
    rfl
  · show ms.REG (BitVec.ofNat 5 dest) = v
    exact hreg dest ⟨hdlt, hdav⟩
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4' : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4'
  · intro k
    rw [hs2regs k]
    by_cases hk : k = dest
    · subst hk
      rw [if_pos rfl]
    · rw [if_neg hk]


/-- The `.mem .load32` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path of `e_LoadStoreImmediate` (`sz = 2`): the branch
conditions are `hsx`, `hmsb` and `hoff`, as in the eight-byte scaled case, with
the four-byte read.  The statement awaits source review against
`arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load32_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2) :
    CaseGoal (.inst (.mem .load32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd : asmRegOkExact dest arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2, h'.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load32 = memLoad (width := 64) 4 := rfl
  have hal4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemLoad_aligned_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_load_single32 dest base off hsx
  have henc : arm8Enc (.inst (.mem .load32 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
    (holWordExtract 12 11 0 (off >>> 2)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_load32 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single32_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
    (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_load32 (holWordExtract 12 11 0 (off >>> 2))
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [← hoff] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 :=
    BitVec.setWidth 64 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_four_eq_readMemWord ms s1 (s1.regs base + off) hal4 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
  have hpairbh : Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    have h1 := arm8Mem_four_of_bytes { ms with branch_hint := none } (s1.regs base + off)
      ms.MEM (fun i hi => rfl) hal4 he0 hel
    have h2 := arm8Mem_four_of_bytes ms (s1.regs base + off) ms.MEM
      (fun i hi => rfl) hal4 he0 hel
    rw [h1, h2]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load32 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [show BitVec.setWidth 32 (Mem (TN := 32)
      ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 =
        (Mem (TN := 32) ((s1.regs base + off), (4, AccType.AccType_NORMAL)) ms).1 by simp]
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .load32 dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd4]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [hv]
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .load32 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom hs2regs
  · rfl
  · intro x hx
    show ms.MEM x = s2.mem x
    rw [hs2mem x]
    exact hmem x hx
  · intro x hx
    show ms.MEM x = ms.MEM x
    rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 dest) then v
      else ms.REG (BitVec.ofNat 5 dest)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4' : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4'

/-- The `.mem .store32` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path (`sz = 2`, `opc = 0`), with the four-byte write.  The
statement awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store32_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 2))) <<< 2) :
    CaseGoal (.inst (.mem .store32 dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd : asmRegOkExact dest arm8ConfigL3 = true ∧
      asmRegOkExact base arm8ConfigL3 = true ∧
      asmAddrOffsetOkExact arm8ConfigL3 off = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2, h'.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store32 = memStore (width := 64) 4 := rfl
  have hal4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemStore_aligned_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single32 dest base off hsx
  have henc : arm8Enc (.inst (.mem .store32 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
    (holWordExtract 12 11 0 (off >>> 2)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_store32 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single32_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@32»
    (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_store32 (holWordExtract 12 11 0 (off >>> 2))
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [← hoff] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := s1.regs dest
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hXd : X (TN := 32) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 32 (s1.regs dest) := by
    rw [arm8X32_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store32 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_four _ _ _ _ hal4]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store32 dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 4 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store32 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_four { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL hal4 he0 hel x]
    rw [writeMemN_four_setWidth32 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_four s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_four_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL hal4 he0 hel x
      (fun k hk h => hx (h ▸ hdom k hk))
  · intro k hk hkne
    show ms.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k)
    rfl
  · show ms.REG (BitVec.ofNat 5 dest) = v
    exact hreg dest ⟨hdlt, hdav⟩
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4' : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4'
  · intro k
    rw [hs2regs k]
    by_cases hk : k = dest
    · subst hk
      rw [if_pos rfl]
    · rw [if_neg hk]


/-- The `.mem .load` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path of `e_LoadStoreImmediate`.

`hsx` and `hfall` are the two branch conditions the lowering inspects:
`arm8_ast` emits the single instruction only when `off` is its own signed
nine-bit form (`hsx`), and `e_LoadStoreImmediate` reaches the `imm9` clause
only when its scaled twelve-bit clause does not fire (`hfall`).  They are case
hypotheses of the `Mem` branch, not part of `CaseGoal`; `hsx` is also a
hypothesis of `arm8Ast_load_single`, and `hfall` of
`arm8Encode_loadStoreImm9_load`.  The negative and non-negative unscaled
branches are the two corollaries below. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3)) = false) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd := arm8MemLoadOkExact dest base off hs.2.2.2.2.2.2
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load = memLoad (width := 64) 8 := by
    show memLoad (width := 64) (64 / 8) = memLoad (width := 64) 8
    norm_num
  have hal8 : Aligned (TN := 64) (s1.regs base + off, 8) = true :=
    arm8MemLoad_aligned .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hmemv : (Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1 :=
    arm8Mem_eight_value ms s1 (s1.regs base + off) hal8 he0 hel hbe hmem hdom
  have hast := arm8Ast_load_single dest base off hsx
  have henc : arm8Enc (.inst (.mem .load dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_load off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have hoff : BitVec.signExtend 64 (holWordExtract 9 8 0 off) = off :=
    arm8SignExtend_nine off hsx
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
    (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
     false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 off)
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [hoff] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1
  have hpair : Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL)) ms =
      (v, ms) := by
    have hp := arm8Mem_eight_pair ms s1 (s1.regs base + off) hal8 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
    rw [hp]
  have hpairbh : Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL))
      { ms with branch_hint := none } = (v, { ms with branch_hint := none }) := by
    have h8 := arm8Mem_eight_of_bytes { ms with branch_hint := none }
      (s1.regs base + off) ms.MEM (fun i hi => rfl) hal8 he0 hel
    have hpms := arm8Mem_eight_of_bytes ms (s1.regs base + off) ms.MEM
      (fun i hi => rfl) hal8 he0 hel
    rw [hpms] at hpair
    rw [h8]
    exact Prod.ext (Prod.ext_iff.mp hpair).1 rfl
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [show BitVec.setWidth 64 v = v by simp]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .load dest (.addr base off))) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd4]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  refine asmCaseOneMem (.mem .load dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom hs2regs
  · rfl
  · intro x hx
    show ms.MEM x = s2.mem x
    rw [hs2mem x]
    exact hmem x hx
  · intro x hx
    show ms.MEM x = ms.MEM x
    rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 dest) then v
      else ms.REG (BitVec.ofNat 5 dest)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4 : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4

/-- The negative-offset `imm9` load branch: a negative offset makes the
`unsigned_offset` field `false`, so `e_LoadStoreImmediate`'s scaled twelve-bit
clause cannot fire. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = true) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms :=
  arm8_encoder_correct_mem_load_imm9 dest base off s1 s2 ms h hsx (by rw [hmsb]; rfl)

/-- The non-negative offset that fits signed nine bits but is not the scaled
twelve-bit form: `e_LoadStoreImmediate` falls through its scaled clause to the
`imm9` clause. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_pos_unscaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = false)
    (hscaled : (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3) = false) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms :=
  arm8_encoder_correct_mem_load_imm9 dest base off s1 s2 ms h hsx (by
    rw [hmsb]
    exact hscaled)


@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd := arm8MemLoadOkExact dest base off hs.2.2.2.2.2.2
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load = memLoad (width := 64) 8 := by
    show memLoad (width := 64) (64 / 8) = memLoad (width := 64) 8
    norm_num
  have hal8 : Aligned (TN := 64) (s1.regs base + off, 8) = true :=
    arm8MemLoad_aligned .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hmemv : (Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1 :=
    arm8Mem_eight_value ms s1 (s1.regs base + off) hal8 he0 hel hbe hmem hdom
  have hast := arm8Ast_load_single dest base off hsx
  have henc : arm8Enc (.inst (.mem .load dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
    (holWordExtract 12 11 0 (off >>> 3)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_load off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
    (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
     true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_load (holWordExtract 12 11 0 (off >>> 3))
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [← hoff] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1
  have hpair : Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL)) ms =
      (v, ms) := by
    have hp := arm8Mem_eight_pair ms s1 (s1.regs base + off) hal8 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
    rw [hp]
  have hpairbh : Mem (TN := 64) ((s1.regs base + off), (8, AccType.AccType_NORMAL))
      { ms with branch_hint := none } = (v, { ms with branch_hint := none }) := by
    have h8 := arm8Mem_eight_of_bytes { ms with branch_hint := none }
      (s1.regs base + off) ms.MEM (fun i hi => rfl) hal8 he0 hel
    have hpms := arm8Mem_eight_of_bytes ms (s1.regs base + off) ms.MEM
      (fun i hi => rfl) hal8 he0 hel
    rw [hpms] at hpair
    rw [h8]
    exact Prod.ext (Prod.ext_iff.mp hpair).1 rfl
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [show BitVec.setWidth 64 v = v by simp]
    rw [arm8WriteX_of_valid _ _ hd31 hdlt]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .load dest (.addr base off))) (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd4]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  refine asmCaseOneMem (.mem .load dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom hs2regs
  · rfl
  · intro x hx
    show ms.MEM x = s2.mem x
    rw [hs2mem x]
    exact hmem x hx
  · intro x hx
    show ms.MEM x = ms.MEM x
    rfl
  · intro k hk hkne
    show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k) then v
      else ms.REG (BitVec.ofNat 5 k)) = ms.REG (BitVec.ofNat 5 k)
    rw [if_neg]
    intro hh
    apply hkne
    have := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
    have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
    have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
    omega
  · show (if (BitVec.ofNat 5 dest) = (BitVec.ofNat 5 dest) then v
      else ms.REG (BitVec.ofNat 5 dest)) = v
    rw [if_pos rfl]
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4 : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4

/-- The `.mem .store` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path of `e_LoadStoreImmediate`.  `hsx` and `hfall` are the
branch conditions of `arm8_ast` and `e_LoadStoreImmediate`, as in the load
case; the store additionally carries memory obligations, so the source's
`writeMemWord` is matched to the target's `write'Mem` by
`arm8WriteMem_eight`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3)) = false) :
    CaseGoal (.inst (.mem .store dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd := arm8MemStoreOkExact dest base off hs.2.2.2.2.2.2
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store = memStore (width := 64) 8 := by
    show memStore (width := 64) (64 / 8) = memStore (width := 64) 8
    norm_num
  have hal8 : Aligned (TN := 64) (s1.regs base + off, 8) = true :=
    arm8MemStore_aligned .store dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain .store dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single dest base off hsx
  have henc : arm8Enc (.inst (.mem .store dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_store off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
    (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
     false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 off)
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [arm8SignExtend_nine off hsx] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := s1.regs dest
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hXd : X (TN := 64) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      s1.regs dest := by
    rw [arm8X_of_valid _ hd31 hdlt]
    exact hreg dest ⟨hdlt, hdav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem _ _ _ _ hal8]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 8 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_eight { ms with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x]
    rw [← writeMemWord_mem_eight s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_eight_out { ms with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x
      (fun k hk h => hx (h ▸ hdom k hk))
  · intro k hk hkne
    show ms.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k)
    rfl
  · show ms.REG (BitVec.ofNat 5 dest) = v
    exact hreg dest ⟨hdlt, hdav⟩
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4 : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4
  · intro k
    rw [hs2regs k]
    by_cases hk : k = dest
    · subst hk
      rw [if_pos rfl]
    · rw [if_neg hk]


/-- The `.mem .store` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path of `e_LoadStoreImmediate`.  The branch conditions are the
same three the load case uses (`hsx`, `hmsb`, `hoff`); the memory obligations
are discharged as in the `imm9` store case. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3) :
    CaseGoal (.inst (.mem .store dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  obtain ⟨hok, hpc, hmem, hreg, hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  have hokd := arm8MemStoreOkExact dest base off hs.2.2.2.2.2.2
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2.1
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store = memStore (width := 64) 8 := by
    show memStore (width := 64) (64 / 8) = memStore (width := 64) 8
    norm_num
  have hal8 : Aligned (TN := 64) (s1.regs base + off, 8) = true :=
    arm8MemStore_aligned .store dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain .store dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single dest base off hsx
  have henc : arm8Enc (.inst (.mem .store dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
    (holWordExtract 12 11 0 (off >>> 3)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_store off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hb, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w >>> 0).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 0 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w >>> 8).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 1 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w >>> 16).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 2 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w >>> 24).toNat) := by
    have hh := bytesInMemoryHOL_get hbms 3 (by rw [hlen]; omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw] at hh
    simp at hh
    simpa [w] using hh
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@64»
    (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
     true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_store (holWordExtract 12 11 0 (off >>> 3))
      (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
    rw [← hoff] at hd
    simpa [ins, w] using hd
  have hbase : (BitVec.ofNat 5 base == (BitVec.ofNat 5 31)) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat (beq_iff_eq.mp hh)
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    have h31 : 31 % 2 ^ 5 = 31 := by decide
    omega
  let v : BitVec 64 := s1.regs dest
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hXd : X (TN := 64) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      s1.regs dest := by
    rw [arm8X_of_valid _ hd31 hdlt]
    exact hreg dest ⟨hdlt, hdav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem _ _ _ _ hal8]
  have hbr : (Run ins { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun]
  have hexc : (Run ins { ms with branch_hint := none }).exception = exception.NoException := by
    rw [hrun]
    show ms.exception = exception.NoException
    exact hexc0
  have hn := arm8Next_word ms w ins hdec hbr hexc h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store dest (.addr base off)))
      (s1.pc + BitVec.ofNat 64 4) s1 = s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 8 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_eight { ms with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x]
    rw [← writeMemWord_mem_eight s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_eight_out { ms with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x
      (fun k hk h => hx (h ▸ hdom k hk))
  · intro k hk hkne
    show ms.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k)
    rfl
  · show ms.REG (BitVec.ofNat 5 dest) = v
    exact hreg dest ⟨hdlt, hdav⟩
  · rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · show ms.exception = exception.NoException
      exact hexc0
    · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      have hal4 : holAligned 2 (ms.PC + 4) = true := by
        rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
      change holAligned 2 (ms.PC + 4) = true
      exact hal4
  · intro k
    rw [hs2regs k]
    by_cases hk : k = dest
    · subst hk
      rw [if_pos rfl]
    · rw [if_neg hk]
end Flapjack.Compiler.Encoders.Arm8.L3
