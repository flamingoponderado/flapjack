import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.AddSubImmediate
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

/-- The scaled twelve-bit form of `arm8_load_store_ast` (a zero-extended
 twelve-bit slice shifted into place) is the `hoff` form the case theorems use:
 `setWidth 64` of the low twelve bits of the shifted offset. -/
theorem arm8ScaledForm_eq (off : BitVec 64) (shift : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> shift).toNat))) =
      BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> shift)) := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract]

/-- The one-instruction branch of `arm8_load_store_ast` for `.mem .load`: when
 the offset is either its own signed nine-bit form or the scaled twelve-bit form
 at a non-negative offset, `arm8_ast` emits a single `LoadStoreImmediate@64`.
 This is the negation of the two-instruction condition `arm8_ast` tests, so it
 also covers scaled offsets beyond the nine-bit range. -/
theorem arm8Ast_load_single_of_single (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true) :
    arm8Ast (.inst (.mem .load dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction branch of `arm8_load_store_ast` for `.mem .store`
 (`arm8_load_store_ast` at `arm8_targetScript.sml:78-96`). -/
theorem arm8Ast_store_single_of_single (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true) :
    arm8Ast (.inst (.mem .store dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction branch of `arm8_load_store_ast32` for `.mem .load32`. -/
theorem arm8Ast_load_single_of_single32 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true) :
    arm8Ast (.inst (.mem .load32 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst32]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction branch of `arm8_load_store_ast32` for `.mem .store32`. -/
theorem arm8Ast_store_single_of_single32 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true) :
    arm8Ast (.inst (.mem .store32 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst32]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction branch of `arm8_load_store_ast16` for `.mem .load16`. -/
theorem arm8Ast_load_single_of_single16 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true) :
    arm8Ast (.inst (.mem .load16 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst16]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction branch of `arm8_load_store_ast16` for `.mem .store16`. -/
theorem arm8Ast_store_single_of_single16 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true) :
    arm8Ast (.inst (.mem .store16 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst16]
  split
  · rename_i hcond
    rw [Bool.and_eq_true] at hcond
    obtain ⟨hne, hrest⟩ := hcond
    have hne' : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by simpa using hne
    rcases hsingle with hsx | hscaled
    · exact absurd hsx hne'
    · rw [Bool.and_eq_true] at hscaled
      obtain ⟨hunsigned, hbeq⟩ := hscaled
      rw [beq_iff_eq] at hbeq
      rw [Bool.or_eq_true] at hrest
      rcases hrest with hmsb | hne''
      · have hmsbt : off.msb = true := by simpa using hmsb
        rw [hmsbt] at hunsigned
        exact absurd hunsigned (by decide)
      · have hne : off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1 := by
          simpa using hne''
        exact (hne hbeq).elim
  · rfl

/-- The one-instruction load lowering encodes to four bytes on the whole
 single-instruction branch of `arm8_load_store_ast`. -/
theorem arm8Enc_load_single_length_of_single (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true) :
    (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single_of_single dest base off hsingle]
  simp [arm8Encode_length]

/-- The one-instruction store lowering encodes to four bytes on the whole
 single-instruction branch of `arm8_load_store_ast`. -/
theorem arm8Enc_store_single_length_of_single (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true) :
    (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single_of_single dest base off hsingle]
  simp [arm8Encode_length]

/-- The one-instruction `LoadStoreImmediate@32` lowering encodes to four bytes. -/
theorem arm8Enc_load_single_length_of_single32 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true) :
    (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single_of_single32 dest base off hsingle]
  simp [arm8Encode_length]

/-- The one-instruction `LoadStoreImmediate@32` store lowering encodes to four
 bytes. -/
theorem arm8Enc_store_single_length_of_single32 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true) :
    (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single_of_single32 dest base off hsingle]
  simp [arm8Encode_length]

/-- The one-instruction `LoadStoreImmediate@16` lowering encodes to four bytes. -/
theorem arm8Enc_load_single_length_of_single16 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true) :
    (arm8Enc (.inst (.mem .load16 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single_of_single16 dest base off hsingle]
  simp [arm8Encode_length]

/-- The one-instruction `LoadStoreImmediate@16` store lowering encodes to four
 bytes. -/
theorem arm8Enc_store_single_length_of_single16 (dest base : Nat) (off : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true) :
    (arm8Enc (.inst (.mem .store16 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single_of_single16 dest base off hsingle]
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
scaled twelve-bit path of `e_LoadStoreImmediate` (`sz = 2`): a non-negative
offset equal to its scaled twelve-bit form (`hmsb`, `hoff`), which is the whole
unsigned scaled branch of `arm8_load_store_ast`, whether or not the offset also
fits signed nine bits, with the four-byte read.  The statement awaits source
review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load32_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
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
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 2]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_load_single_of_single32 dest base off hsingle
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
    arm8Enc_load_single_length_of_single32 dest base off hsingle
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
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 2).toNat))) <<< 2) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 2]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_store_single_of_single32 dest base off hsingle
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
    arm8Enc_store_single_length_of_single32 dest base off hsingle
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


/-! ## The one-byte `Mem` layer

The `load8`/`store8` lowerings emit one `LoadStoreImmediate@8`; its `Mem`
transfer is one byte, and the register write is the zero-extended byte.
-/

theorem arm8ShiftRight_zero (x : BitVec 64) : x >>> (0 : Nat) = x := rfl

/-! ## The one-byte `Mem` helpers -/

theorem holW2v_length8 (value : BitVec 8) : (holW2v value).length = 8 := by
  simp [holW2v]

theorem holField_eight_of_length (l : List Bool) (h : l.length = 8) : holField 7 0 l = l := by
  have ht : (l.take 8).length = 8 := by rw [List.length_take, h]; omega
  simp only [holField, holShiftr, holFixwidth, h, Nat.sub_zero, ht, Nat.sub_self]
  exact List.take_of_length_le (by omega)

theorem arm8HolByte8 (value : BitVec 8) :
    holV2w 8 (holField 7 0 (holW2v value)) = value := by
  rw [holField_eight_of_length _ (holW2v_length8 value), holV2w_holW2v]

theorem arm8Aligned_one_of_holAligned (a : BitVec 64)
    (_h : holAligned 0 a = true) : Aligned (TN := 64) (a, 1) = true := by
  simp [Aligned, Align]

theorem arm8Mem_one (ms : arm8_state) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 1) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 8) (address, (1, AccType.AccType_NORMAL)) ms = (ms.MEM address, ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms address 1 AccType.AccType_NORMAL false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false]
    exact arm8HolByte8 _
  · exact CheckAlignment_aligned ms address 1 AccType.AccType_NORMAL false hal

theorem arm8Mem_one_eq_readMemWord (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 1) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false) (hmem : ms.MEM address = s.mem address) :
    BitVec.setWidth 64 (Mem (TN := 8) (address, (1, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) address 1 s).1 := by
  rw [arm8Mem_one ms address hal he0 hel, hmem, readMemWord_fst address 1 s hbe]
  simp [readBytes]

theorem arm8WriteMem_one (ms : arm8_state) (address : BitVec 64) (value : BitVec 8)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 1) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) :
    («write'Mem» (TN := 8) (value, (address, (1, acctype))) ms).MEM x =
      (writeMemN (memState ms.MEM) 1 address (BitVec.setWidth 64 value)).mem x := by
  simp only [«write'Mem», writeMemN, memState]
  simp [holFor, CheckAlignment_aligned ms address 1 acctype true hal,
    BigEndian_false ms hel he0, arm8HolByte8, holUpdate_apply]
  by_cases h : x = address
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]


/-- A one-byte machine write ignores the `setWidth 8`-then-`setWidth 64` round
trip of its value (Flapjack infrastructure). -/
theorem writeMemN_one_setWidth8 (s : Arm8State) (a w x : BitVec 64) :
    (writeMemN s 1 a (BitVec.setWidth 64 (BitVec.setWidth 8 w))).mem x =
      (writeMemN s 1 a w).mem x := by
  simp only [writeMemN]
  by_cases h : x = a
  · simp [h]
  · simp [h]


theorem arm8WriteMem_one_out (ms : arm8_state) (address : BitVec 64) (value : BitVec 8)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 1) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) (hx : x ≠ address) :
    («write'Mem» (TN := 8) (value, (address, (1, acctype))) ms).MEM x = ms.MEM x := by
  rw [arm8WriteMem_one ms address value acctype hal he0 hel x]
  simp only [writeMemN, memState]
  simp [hx]

theorem arm8WriteMem_only_mem_one (ms : arm8_state) (value : BitVec 8) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 1) = true) :
    («write'Mem» (TN := 8) (value, (address, (1, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 8) (value, (address, (1, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 1 acctype true hal]

theorem arm8MemStore_aligned_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 1) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h0 : holLOG2 1 = 0 := holLOG_UNIQUE 2 1 0 ⟨by decide, by decide⟩
  rw [h0] at hal
  exact arm8Aligned_one_of_holAligned _ (by simpa using hal)

theorem arm8MemStore_domain_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact writeMemWord_domain (s1.regs base + off) 1 (s1.regs r) s1 hbe (not_of_eq_false hf)

theorem arm8MemLoad_aligned_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 1) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h0 : holLOG2 1 = 0 := holLOG_UNIQUE 2 1 0 ⟨by decide, by decide⟩
  rw [h0] at hal
  exact arm8Aligned_one_of_holAligned _ (by simpa using hal)

theorem arm8MemLoad_domain_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have h := memLoadDomain op r base off s1 s2 0 pc (by simpa using hspec) hupd hbe hok
  simpa using h

/-! ## The `LoadStoreImmediate@8` words -/

theorem arm8ELoadStoreImm9_load8 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = (BitVec.ofNat 2 0) := by decide
  have h2 : (BitVec.ofNat 2 0).toNat = 0 := by decide
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
    holV2w_one_false, arm8ShiftRight_zero]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 offset)) <<< 0)) = true := by
         simpa using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_load8 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_load8 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_load8 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_zero, holV2w_two_one, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm9_store8 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = (BitVec.ofNat 2 0) := by decide
  have h2 : (BitVec.ofNat 2 0).toNat = 0 := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hsx' : (offset == BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) = true := by
    rw [beq_iff_eq]; exact hsx
  have hnf : ((!false : Bool) = true) := rfl
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hstore, hnrm, hpref,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
    arm8ShiftRight_zero]
  split_ifs with hg
  all_goals first
    | rfl
    | exact absurd hsx' ‹_›
    | (exfalso
       have h1 : (unsigned_offset && (offset == (BitVec.setWidth 64
           (holWordExtract 12 11 0 offset)) <<< 0)) = true := by
         simpa using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_store8 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_store8 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_store8 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_zero, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm12_load8 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) :
    e_load_store (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 offset) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = (BitVec.ofNat 2 0) := by decide
  have h2 : (BitVec.ofNat 2 0).toNat = 0 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hload, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
    arm8ShiftRight_zero]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_load8 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) :
    Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 offset) rn rt) :=
  arm8ELoadStoreImm12_load8 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_load8 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 0), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_one, holV2w_two_zero, holV2w_five, arm8HolV2w_twelve,
    LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm12_store8 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) :
    e_load_store (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 offset) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 8 0) = (BitVec.ofNat 2 0) := by decide
  have h2 : (BitVec.ofNat 2 0).toNat = 0 := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true,
    arm8ShiftRight_zero]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_store8 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 offset)) <<< 0) :
    Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 offset) rn rt) :=
  arm8ELoadStoreImm12_store8 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_store8 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 0), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_zero, holV2w_five, arm8HolV2w_twelve,
    LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8Ast_load_single8 (dest base : Nat) (off : BitVec 64) :
    arm8Ast (.inst (.mem .load8 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp [arm8Ast]

theorem arm8Ast_store_single8 (dest base : Nat) (off : BitVec 64) :
    arm8Ast (.inst (.mem .store8 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  simp [arm8Ast]

theorem arm8Enc_load_single8_length (dest base : Nat) (off : BitVec 64) :
    (arm8Enc (.inst (.mem .load8 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single8 dest base off]
  simp [arm8Encode_length]

theorem arm8Enc_store_single8_length (dest base : Nat) (off : BitVec 64) :
    (arm8Enc (.inst (.mem .store8 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single8 dest base off]
  simp [arm8Encode_length]

theorem setWidth64_setWidth32 (x : BitVec 8) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x) = BitVec.setWidth 64 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h8 : i < 8
  · simp [h8, show i < 32 by omega, show i < 64 by omega]
  · have h8' : 8 ≤ i := by omega
    simp [h8', show i < 64 by omega]

theorem arm8Run_loadStoreImmediate_load8 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'X» (TN := 32)
        ((BitVec.setWidth 32 (Mem (TN := 8) ((X (TN := 64) base ms) + offset, (1, .AccType_NORMAL)) ms).1), dest)
        (Mem (TN := 8) ((X (TN := 64) base ms) + offset, (1, .AccType_NORMAL)) ms).2 := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, ExtendWord, hbase,
    if_false, if_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

theorem arm8Run_loadStoreImmediate_store8 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'Mem» (TN := 8)
        ((X (TN := 8) dest ms), ((X (TN := 64) base ms) + offset, (1, .AccType_NORMAL))) ms := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, hbase,
    if_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

theorem arm8X8_of_valid (ms : arm8_state) {n : Nat} (hn : n ≠ 31) (hlt : n < 32) :
    X (TN := 8) (BitVec.ofNat 5 n) ms = BitVec.setWidth 8 (ms.REG (BitVec.ofNat 5 n)) := by
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


/-- The `.mem .load8` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path: the `load8` lowering emits one `LoadStoreImmediate@8`, and
`e_LoadStoreImmediate` reaches its `imm9` clause only when the scaled twelve-bit
clause does not fire (`hfall`) and `off` is its own signed nine-bit form (`hsx`).
The machine reads one byte and zero-extends it to the register width.  The
statement awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load8_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0)) = false) :
    CaseGoal (.inst (.mem .load8 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load8 = memLoad (width := 64) 1 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 1) = true :=
    arm8MemLoad_aligned_one .load8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_one .load8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_load_single8 dest base off
  have henc : arm8Enc (.inst (.mem .load8 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_load8 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .load8 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single8_length dest base off
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load8 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
    (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_load8 (holWordExtract 9 8 0 off)
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
  let v : BitVec 64 := BitVec.setWidth 64 (Mem (TN := 8)
    ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 1 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 8)
      ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_one_eq_readMemWord ms s1 (s1.regs base + off) hal1 he0 hel hbe
      (by simpa using hmem _ (hdom 0 (by omega)))
  have hpairbh : Mem (TN := 8) ((s1.regs base + off), (1, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 8) ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    rw [arm8Mem_one { ms with branch_hint := none } (s1.regs base + off) hal1 he0 hel,
      arm8Mem_one ms (s1.regs base + off) hal1 he0 hel]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load8 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
    rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (Mem (TN := 8)
      ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1) = v by
      rw [setWidth64_setWidth32]]
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
  have hupd4 : asmUpd (.inst (.mem .load8 dest (.addr base off)))
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
  refine asmCaseOneMem (.mem .load8 dest (.addr base off)) dest v _ s1 s2 ms
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

/-- The `.mem .store8` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path (`opc = 0`), writing one byte.  The statement awaits source
review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store8_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0)) = false) :
    CaseGoal (.inst (.mem .store8 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store8 = memStore (width := 64) 1 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 1) = true :=
    arm8MemStore_aligned_one .store8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_one .store8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single8 dest base off
  have henc : arm8Enc (.inst (.mem .store8 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_store8 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .store8 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single8_length dest base off
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store8 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
    (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_store8 (holWordExtract 9 8 0 off)
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
  have hXd : X (TN := 8) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 8 (s1.regs dest) := by
    rw [arm8X8_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 8)
          (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store8 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_one _ _ _ _ hal1]
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
        MEM := («write'Mem» (TN := 8)
          (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store8 dest (.addr base off)))
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
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 1 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store8 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 8)
      (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_one { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 8 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x]
    rw [writeMemN_one_setWidth8 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_one s1 ms.MEM (s1.regs base + off) (s1.regs dest) x (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 8)
      (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_one_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 8 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x
      (fun h => hx (by
        have hd0 : s1.memDomain (s1.regs base + off) := by simpa using hdom 0 (by omega)
        rw [h]; exact hd0))
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

/-- The `.mem .load8` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path of `e_LoadStoreImmediate` (`sz = 0`): the branch
conditions are `hmsb` and `hoff`, with the one-byte read.  The statement awaits
source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load8_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0) :
    CaseGoal (.inst (.mem .load8 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load8 = memLoad (width := 64) 1 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 1) = true :=
    arm8MemLoad_aligned_one .load8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_one .load8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_load_single8 dest base off
  have henc : arm8Enc (.inst (.mem .load8 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 1)
    (holWordExtract 12 11 0 off) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_load8 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .load8 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single8_length dest base off
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load8 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
    (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_load8 (holWordExtract 12 11 0 off)
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
  let v : BitVec 64 := BitVec.setWidth 64 (Mem (TN := 8)
    ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 1 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 8)
      ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_one_eq_readMemWord ms s1 (s1.regs base + off) hal1 he0 hel hbe
      (by simpa using hmem _ (hdom 0 (by omega)))
  have hpairbh : Mem (TN := 8) ((s1.regs base + off), (1, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 8) ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    rw [arm8Mem_one { ms with branch_hint := none } (s1.regs base + off) hal1 he0 hel,
      arm8Mem_one ms (s1.regs base + off) hal1 he0 hel]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load8 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
    rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (Mem (TN := 8)
      ((s1.regs base + off), (1, AccType.AccType_NORMAL)) ms).1) = v by
      rw [setWidth64_setWidth32]]
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
  have hupd4 : asmUpd (.inst (.mem .load8 dest (.addr base off)))
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
  refine asmCaseOneMem (.mem .load8 dest (.addr base off)) dest v _ s1 s2 ms
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

/-- The `.mem .store8` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path (`sz = 0`, `opc = 0`), with the one-byte write.  The
statement awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store8_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store8 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 off)) <<< 0) :
    CaseGoal (.inst (.mem .store8 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store8 = memStore (width := 64) 1 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 1) = true :=
    arm8MemStore_aligned_one .store8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_one .store8 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single8 dest base off
  have henc : arm8Enc (.inst (.mem .store8 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 0) (BitVec.ofNat 2 0)
    (holWordExtract 12 11 0 off) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_store8 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .store8 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single8_length dest base off
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store8 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@8»
    (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_store8 (holWordExtract 12 11 0 off)
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
  have hXd : X (TN := 8) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 8 (s1.regs dest) := by
    rw [arm8X8_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 8)
          (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store8 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_one _ _ _ _ hal1]
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
        MEM := («write'Mem» (TN := 8)
          (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store8 dest (.addr base off)))
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
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 1 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store8 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 8)
      (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_one { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 8 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x]
    rw [writeMemN_one_setWidth8 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_one s1 ms.MEM (s1.regs base + off) (s1.regs dest) x (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 8)
      (BitVec.setWidth 8 (s1.regs dest), ((s1.regs base) + off, (1, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_one_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 8 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x
      (fun h => hx (by
        have hd0 : s1.memDomain (s1.regs base + off) := by simpa using hdom 0 (by omega)
        rw [h]; exact hd0))
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


/-! ## The two-byte `Mem` layer

The `load16`/`store16` lowerings emit one `LoadStoreImmediate@16`; its `Mem`
transfer is two bytes, and the register write is the zero-extended halfword.
-/

theorem holW2v_length16 (value : BitVec 16) : (holW2v value).length = 16 := by
  simp [holW2v]

theorem holW2v_getElem?_16 (value : BitVec 16) (m : Nat) :
    (holW2v value)[m]? = if m < 16 then some (value.getLsbD (15 - m)) else none := by
  simp only [holW2v, List.getElem?_map]
  by_cases hm : m < 16
  · simp [hm]
  · simp [hm]

theorem holField_two_length (value : BitVec 16) (i : Nat) (hi : i < 2) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (16 - 8 * i < 8) := by omega
  have hmin : min (16 - 8 * i) 16 = 16 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length16, hmin, hge, if_false,
    List.length_take, List.length_drop]
  omega

theorem holField_two_getElem? (value : BitVec 16) (i j : Nat) (hi : i < 2) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (16 - 8 * i < 8) := by omega
  have hmin : min (16 - 8 * i) 16 = 16 - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length16, List.length_take, hmin, hge,
    if_false]
  rw [List.getElem?_drop]
  rw [show 16 - 8 * i - 8 + (7 - j) = 15 - 8 * i - j by omega]
  rw [List.getElem?_take_of_lt (by omega : 15 - 8 * i - j < 16 - 8 * i)]
  rw [holW2v_getElem?_16]
  have hlt : 15 - 8 * i - j < 16 := by omega
  have hidx : 15 - (15 - 8 * i - j) = 8 * i + j := by omega
  simp only [hlt, if_true, hidx]

theorem arm8HolByte16 (value : BitVec 16) (i : Nat) (hi : i < 2) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w]
  rw [getLsbD_holFcpWord]
  have hlen := holField_two_length value i hi
  simp only [hj, decide_true, Bool.true_and, hlen, show 8 - 1 - j = 7 - j by omega]
  rw [List.getD_eq_getElem?_getD, holField_two_getElem? value i j hi hj]
  simp only [Option.getD_some, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]

theorem arm8ByteSetWidth16_64 (w : BitVec 64) (i : Nat) (hi : i < 2) :
    (((BitVec.setWidth 64 (BitVec.setWidth 16 w)) >>> (8 * i : Nat)).setWidth 8) =
      ((w >>> (8 * i : Nat)).setWidth 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  have hk : 8 * i + j < 16 := by omega
  have h64 : 8 * i + j < 64 := by omega
  simp [hk, h64]

theorem writeMemN_two_setWidth16 (s : Arm8State) (a w x : BitVec 64) :
    (writeMemN s 2 a (BitVec.setWidth 64 (BitVec.setWidth 16 w))).mem x =
      (writeMemN s 2 a w).mem x := by
  simp only [writeMemN]
  by_cases h : x = a
  · simp [h]
  · simp [h, arm8ByteSetWidth16_64 w 1 (by decide)]

theorem holUpdate_two (address : BitVec 64) (f : BitVec 64 → BitVec 8)
    (b0 b1 : BitVec 8) (x : BitVec 64) :
    holUpdate (address + 1#64) b1 (holUpdate address b0 f) x =
      if x = address then b0
      else if x = address + 1#64 then b1 else f x := by
  simp only [holUpdate_apply]
  by_cases e0 : x = address
  · subst e0; simp
  by_cases e1 : x = address + 1#64
  · subst e1; simp
  · have h0 : address ≠ x := fun h => e0 h.symm
    have h1 : address + 1#64 ≠ x := fun h => e1 h.symm
    simp [e0, e1, h0, h1]

theorem arm8WriteMem_two (ms : arm8_state) (address : BitVec 64) (value : BitVec 16)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) :
    («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms).MEM x =
      (writeMemN (memState ms.MEM) 2 address (BitVec.setWidth 64 value)).mem x := by
  simp only [«write'Mem», writeMemN, memState]
  simp [holFor, CheckAlignment_aligned ms address 2 acctype true hal,
    BigEndian_false ms hel he0]
  have hb0 : holV2w 8 (holField 7 0 (holW2v value)) = BitVec.setWidth 8 value := by
    simpa using arm8HolByte16 value 0 (by decide)
  have hb1 : holV2w 8 (holField 15 8 (holW2v value)) = BitVec.setWidth 8 (value >>> 8) := by
    simpa using arm8HolByte16 value 1 (by decide)
  rw [hb0, hb1]
  exact holUpdate_two address ms.MEM _ _ x

theorem arm8WriteMem_two_out (ms : arm8_state) (address : BitVec 64) (value : BitVec 16)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) (hx : ∀ k, k < 2 → x ≠ address + BitVec.ofNat 64 k) :
    («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms).MEM x = ms.MEM x := by
  rw [arm8WriteMem_two ms address value acctype hal he0 hel x]
  have h0 : x ≠ address := by simpa using hx 0 (by omega)
  have h1 : x ≠ address + 1#64 := by simpa using hx 1 (by omega)
  simp only [writeMemN, memState]
  simp [h0, h1]

theorem arm8WriteMem_only_mem_two (ms : arm8_state) (value : BitVec 16) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 2) = true) :
    («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 2 acctype true hal]

theorem arm8Aligned_two_of_holAligned (a : BitVec 64)
    (h : holAligned 1 a = true) : Aligned (TN := 64) (a, 2) = true := by
  have ha : a.toNat % 2 = 0 := by simpa using (holAligned_iff 1 a).mp h
  simp only [Aligned, Align]
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero ha)]
  rw [Nat.mod_eq_of_lt a.isLt]

theorem arm8MemStore_aligned_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h1 : holLOG2 2 = 1 := holLOG_UNIQUE 2 2 1 ⟨by decide, by decide⟩
  rw [h1] at hal
  exact arm8Aligned_two_of_holAligned _ (by simpa using hal)

theorem arm8MemStore_domain_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact writeMemWord_domain (s1.regs base + off) 2 (s1.regs r) s1 hbe (not_of_eq_false hf)

theorem arm8MemLoad_aligned_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2) = true := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  have h1 : holLOG2 2 = 1 := holLOG_UNIQUE 2 2 1 ⟨by decide, by decide⟩
  rw [h1] at hal
  exact arm8Aligned_two_of_holAligned _ (by simpa using hal)

theorem arm8MemLoad_domain_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  have h := memLoadDomain op r base off s1 s2 1 pc (by simpa using hspec) hupd hbe hok
  simpa using h

theorem arm8Mem_two (ms : arm8_state) (address : BitVec 64)
    (b0 b1 : BitVec 8)
    (h0 : ms.MEM address = b0)
    (h1 : ms.MEM (address + BitVec.ofNat 64 1) = b1)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 16) (address, (2, AccType.AccType_NORMAL)) ms =
      (holV2w 16 (holW2v b1 ++ holW2v b0), ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms address 2 AccType.AccType_NORMAL false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, if_false]
    rw [h0, h1]
  · exact CheckAlignment_aligned ms address 2 AccType.AccType_NORMAL false hal

theorem arm8Mem_two_of_bytes (ms : arm8_state) (address : BitVec 64)
    (m : BitVec 64 → BitVec 8)
    (hbytes : ∀ i, i < 2 →
      ms.MEM (address + BitVec.ofNat 64 i) = m (address + BitVec.ofNat 64 i))
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 16) (address, (2, AccType.AccType_NORMAL)) ms =
      (holV2w 16 (holW2v (m (address + BitVec.ofNat 64 1)) ++ holW2v (m address)), ms) := by
  have h0 : ms.MEM address = m address := by simpa using hbytes 0 (by omega)
  exact arm8Mem_two ms address (m address) (m (address + BitVec.ofNat 64 1))
    h0 (hbytes 1 (by omega)) hal he0 hel

theorem arm8SetWidth64_two (b0 b1 : BitVec 8) :
    BitVec.setWidth 64 (holV2w 16 (holW2v b1 ++ holW2v b0)) =
      (BitVec.setWidth 64 b1) <<< (8 : Nat) ||| (BitVec.setWidth 64 b0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w, holW2v, List.length_append, List.length_map,
    List.length_range]
  rw [BitVec.getLsbD_setWidth, getLsbD_holFcpWord]
  simp only [hj, decide_true, Bool.true_and]
  interval_cases j <;> simp [List.getD_eq_getElem?_getD]

theorem arm8Mem_two_eq_readMemWord (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i, i < 2 → ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    BitVec.setWidth 64 (Mem (TN := 16) (address, (2, AccType.AccType_NORMAL)) ms).1 =
      (readMemWord (resultWidth := 64) address 2 s).1 := by
  have h0 : ms.MEM address = s.mem address := by simpa using hmem 0 (by omega)
  have h1 : ms.MEM (address + BitVec.ofNat 64 1) = s.mem (address + BitVec.ofNat 64 1) :=
    hmem 1 (by omega)
  rw [arm8Mem_two ms address (s.mem address) (s.mem (address + BitVec.ofNat 64 1)) h0 h1
    hal he0 hel]
  rw [readMemWord_fst address 2 s hbe, readBytes_two]
  exact arm8SetWidth64_two _ _


/-! ## The `LoadStoreImmediate@16` words -/

theorem arm8ELoadStoreImm9_load16 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = (BitVec.ofNat 2 1) := by decide
  have h2 : (BitVec.ofNat 2 1).toNat = 1 := by decide
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
           (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_load16 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_load16 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_load16 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_one, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm9_store16 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = (BitVec.ofNat 2 1) := by decide
  have h2 : (BitVec.ofNat 2 1).toNat = 1 := by decide
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
           (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = true := by
         simpa [Bool.and_true] using hg
       rw [hfall] at h1
       simp at h1)

theorem arm8Encode_loadStoreImm9_store16 (offset : BitVec 64) (unsigned_offset : Bool)
    (rn rt : BitVec 5)
    (hfall : (unsigned_offset && (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1)) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned_offset, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_store16 offset unsigned_offset rn rt hfall hsx

theorem arm8Decode_loadStoreImm9_store16 (imm9 : BitVec 9) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0) imm9
        (BitVec.ofNat 1 0) rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, BitVec.signExtend 64 imm9, rn, rt)) := by
  simp only [arm8LoadStoreImm9Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_one_false, holV2w_two_zero, holV2w_two_one, holV2w_five,
    arm8HolV2w_nine, LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm12_load16 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) :
    e_load_store (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 1)) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = (BitVec.ofNat 2 1) := by decide
  have h2 : (BitVec.ofNat 2 1).toNat = 1 := by decide
  have hload : (MemOp.MemOp_LOAD == MemOp.MemOp_LOAD) = true := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_LOAD == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_LOAD == MemOp.MemOp_STORE) = false := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hload, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_load16 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) :
    Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
        (holWordExtract 12 11 0 (offset >>> 1)) rn rt) :=
  arm8ELoadStoreImm12_load16 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_load16 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 1), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_one, holV2w_five, arm8HolV2w_twelve,
    LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8ELoadStoreImm12_store16 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) :
    e_load_store (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt)) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 1)) rn rt) := by
  have hs : BitVec.setWidth 2 (BitVec.ofNat 16 1) = (BitVec.ofNat 2 1) := by decide
  have h2 : (BitVec.ofNat 2 1).toNat = 1 := by decide
  have hnrm : (AccType.AccType_NORMAL == AccType.AccType_NORMAL) = true := by decide
  have hpref : (MemOp.MemOp_STORE == MemOp.MemOp_PREFETCH) = false := by decide
  have hstore : (MemOp.MemOp_STORE == MemOp.MemOp_STORE) = true := by decide
  have hnf : ((!false : Bool) = true) := rfl
  have hguard : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) = true := by
    rw [beq_iff_eq]; exact hoff
  simp only [e_load_store, e_LoadStoreImmediate, hs, h2, hnrm, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.and_true]
  split_ifs with hg
  all_goals first | rfl | exact absurd hguard hg

theorem arm8Encode_loadStoreImm12_store16 (offset : BitVec 64) (rn rt : BitVec 5)
    (hoff : offset =
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 1))) <<< 1) :
    Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
        (holWordExtract 12 11 0 (offset >>> 1)) rn rt) :=
  arm8ELoadStoreImm12_store16 offset rn rt hoff

theorem arm8Decode_loadStoreImm12_store16 (imm12 : BitVec 12) (rn rt : BitVec 5) :
    Decode (arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0) imm12 rn rt) =
      instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, ((BitVec.setWidth 64 imm12) <<< 1), rn, rt)) := by
  simp only [arm8LoadStoreImm12Word, Decode, boolify32, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth]
  simp [holV2w_two_zero, holV2w_two_one, holV2w_five, arm8HolV2w_twelve,
    LoadStoreImmediate, LoadStoreImmediateN]

theorem arm8Ast_load_single16 (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .load16 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst16]
  simp [h1]

theorem arm8Ast_store_single16 (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    arm8Ast (.inst (.mem .store16 dest (.addr base off))) =
      [.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))] := by
  rw [BitVec.ofNat_toNat] at hsx
  have h1 : ¬(off ≠ BitVec.signExtend 64 (BitVec.setWidth 9 off)) := fun h => h hsx
  simp only [arm8Ast, arm8LoadStoreAst16]
  simp [h1]

theorem arm8Enc_load_single16_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .load16 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_load_single16 dest base off hsx]
  simp [arm8Encode_length]

theorem arm8Enc_store_single16_length (dest base : Nat) (off : BitVec 64)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) :
    (arm8Enc (.inst (.mem .store16 dest (.addr base off)))).length = 4 := by
  rw [arm8Enc, arm8Ast_store_single16 dest base off hsx]
  simp [arm8Encode_length]

theorem setWidth64_setWidth32_of_16 (x : BitVec 16) :
    BitVec.setWidth 64 (BitVec.setWidth 32 x) = BitVec.setWidth 64 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h16 : i < 16
  · simp [h16, show i < 32 by omega, show i < 64 by omega]
  · have h16' : 16 ≤ i := by omega
    simp [h16', show i < 64 by omega]

theorem arm8Run_loadStoreImmediate_load16 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'X» (TN := 32)
        ((BitVec.setWidth 32 (Mem (TN := 16) ((X (TN := 64) base ms) + offset, (2, .AccType_NORMAL)) ms).1), dest)
        (Mem (TN := 16) ((X (TN := 64) base ms) + offset, (2, .AccType_NORMAL)) ms).2 := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, ExtendWord, hbase,
    if_false, if_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

theorem arm8Run_loadStoreImmediate_store16 (ms : arm8_state) (offset : BitVec 64)
    (unsigned : Bool) (base dest : BitVec 5)
    (hbase : (base == (BitVec.ofNat 5 31)) = false) :
    Run (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, unsigned, offset, base, dest))) ms =
      «write'Mem» (TN := 16)
        ((X (TN := 16) dest ms), ((X (TN := 64) base ms) + offset, (2, .AccType_NORMAL))) ms := by
  have hne : ¬(base = BitVec.ofNat 5 31) := by
    intro h; rw [h] at hbase; simp at hbase
  simp only [Run, «dfn'LoadStoreImmediate», LoadStoreSingle, hbase,
    if_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

theorem arm8X16_of_valid (ms : arm8_state) {n : Nat} (hn : n ≠ 31) (hlt : n < 32) :
    X (TN := 16) (BitVec.ofNat 5 n) ms = BitVec.setWidth 16 (ms.REG (BitVec.ofNat 5 n)) := by
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


/-- The `.mem .load16` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path: the `load16` lowering emits one `LoadStoreImmediate@16`,
and `e_LoadStoreImmediate` reaches its `imm9` clause only when the scaled
twelve-bit clause does not fire (`hfall`) and `off` is its own signed nine-bit
form (`hsx`).  The machine reads two bytes and zero-extends them.  The statement
awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load16_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1)) = false) :
    CaseGoal (.inst (.mem .load16 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load16 = memLoad (width := 64) 2 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 2) = true :=
    arm8MemLoad_aligned_two .load16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_two .load16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_load_single16 dest base off hsx
  have henc : arm8Enc (.inst (.mem .load16 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_load16 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .load16 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single16_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load16 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
    (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_load16 (holWordExtract 9 8 0 off)
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
  let v : BitVec 64 := BitVec.setWidth 64 (Mem (TN := 16)
    ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 2 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 16)
      ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_two_eq_readMemWord ms s1 (s1.regs base + off) hal1 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
  have hpairbh : Mem (TN := 16) ((s1.regs base + off), (2, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 16) ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    rw [arm8Mem_two { ms with branch_hint := none } (s1.regs base + off)
        (ms.MEM (s1.regs base + off)) (ms.MEM (s1.regs base + off + 1#64))
        rfl rfl hal1 he0 hel,
      arm8Mem_two ms (s1.regs base + off)
        (ms.MEM (s1.regs base + off)) (ms.MEM (s1.regs base + off + 1#64))
        rfl rfl hal1 he0 hel]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load16 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
    rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (Mem (TN := 16)
      ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1) = v by
      rw [setWidth64_setWidth32_of_16]]
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
  have hupd4 : asmUpd (.inst (.mem .load16 dest (.addr base off)))
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
  refine asmCaseOneMem (.mem .load16 dest (.addr base off)) dest v _ s1 s2 ms
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

/-- The `.mem .store16` constructor of `encoder_correct arm8TargetL3` on the
unscaled `imm9` path (`opc = 0`), writing two bytes.  The statement awaits source
review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store16_imm9 (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hsx : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hfall : ((!off.msb) && (off ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1)) = false) :
    CaseGoal (.inst (.mem .store16 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store16 = memStore (width := 64) 2 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 2) = true :=
    arm8MemStore_aligned_two .store16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_two .store16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hast := arm8Ast_store_single16 dest base off hsx
  have henc : arm8Enc (.inst (.mem .store16 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  let w : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 off) (BitVec.ofNat 1 0) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm9_store16 off (!off.msb) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      hfall (arm8SignExtend_nine off hsx).symm
  have hlen : (arm8Enc (.inst (.mem .store16 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single16_length dest base off hsx
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store16 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
    (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm9_store16 (holWordExtract 9 8 0 off)
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
  have hXd : X (TN := 16) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 16 (s1.regs dest) := by
    rw [arm8X16_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 16)
          (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, false, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store16 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_two _ _ _ _ hal1]
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
        MEM := («write'Mem» (TN := 16)
          (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store16 dest (.addr base off)))
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
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 2 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store16 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 16)
      (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_two { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 16 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x]
    rw [writeMemN_two_setWidth16 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_two s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 16)
      (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_two_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 16 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x
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

/-- The `.mem .load16` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path of `e_LoadStoreImmediate` (`sz = 1`): a non-negative
offset equal to its scaled twelve-bit form (`hmsb`, `hoff`), whether or not it
also fits signed nine bits, with the two-byte read.  The statement awaits
source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load16_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1) :
    CaseGoal (.inst (.mem .load16 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .load16 = memLoad (width := 64) 2 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 2) = true :=
    arm8MemLoad_aligned_two .load16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemLoad_domain_two .load16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 1]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_load_single_of_single16 dest base off hsingle
  have henc : arm8Enc (.inst (.mem .load16 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 1)
    (holWordExtract 12 11 0 (off >>> 1)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_load16 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .load16 dest (.addr base off)))).length = 4 :=
    arm8Enc_load_single_length_of_single16 dest base off hsingle
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load16 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
    (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_load16 (holWordExtract 12 11 0 (off >>> 1))
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
  let v : BitVec 64 := BitVec.setWidth 64 (Mem (TN := 16)
    ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1
  have hv : v = (readMemWord (resultWidth := 64) (s1.regs base + off) 2 s1).1 := by
    show BitVec.setWidth 64 (Mem (TN := 16)
      ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1 = _
    exact arm8Mem_two_eq_readMemWord ms s1 (s1.regs base + off) hal1 he0 hel hbe
      (fun i hi => hmem _ (hdom i hi))
  have hpairbh : Mem (TN := 16) ((s1.regs base + off), (2, AccType.AccType_NORMAL))
      { ms with branch_hint := none } =
      ((Mem (TN := 16) ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1,
        { ms with branch_hint := none }) := by
    rw [arm8Mem_two { ms with branch_hint := none } (s1.regs base + off)
        (ms.MEM (s1.regs base + off)) (ms.MEM (s1.regs base + off + 1#64))
        rfl rfl hal1 he0 hel,
      arm8Mem_two ms (s1.regs base + off)
        (ms.MEM (s1.regs base + off)) (ms.MEM (s1.regs base + off + 1#64))
        rfl rfl hal1 he0 hel]
  have hX : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v ms.REG } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_load16 _ _ _ _ _ hbase]
    rw [hX, hpairbh]
    simp only
    rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
    rw [show BitVec.setWidth 64 (BitVec.setWidth 32 (Mem (TN := 16)
      ((s1.regs base + off), (2, AccType.AccType_NORMAL)) ms).1) = v by
      rw [setWidth64_setWidth32_of_16]]
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
  have hupd4 : asmUpd (.inst (.mem .load16 dest (.addr base off)))
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
  refine asmCaseOneMem (.mem .load16 dest (.addr base off)) dest v _ s1 s2 ms
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

/-- The `.mem .store16` constructor of `encoder_correct arm8TargetL3` on the
scaled twelve-bit path (`sz = 1`, `opc = 0`), with the two-byte write.  The
statement awaits source review against `arm8_encoder_correct`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store16_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 1))) <<< 1) :
    CaseGoal (.inst (.mem .store16 dest (.addr base off))) s1 s2 ms := by
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
      asmRegOkExact base arm8ConfigL3 = true := by
    have h' := hs.2.2.2.2.2.2
    simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
    exact ⟨h'.1.1, h'.1.2⟩
  obtain ⟨hdlt, hdav, hd31⟩ := regOk_of_asmL3 hokd.1
  obtain ⟨hslt, hsav, hs31⟩ := regOk_of_asmL3 hokd.2
  have hfields := (arm8Ok_iff ms).mp hok
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := hfields
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnotfail : ¬ s2.failed := hs.2.2.2.2.2.1
  have hspec : memOp (width := 64) .store16 = memStore (width := 64) 2 := rfl
  have hal1 : Aligned (TN := 64) (s1.regs base + off, 2) = true :=
    arm8MemStore_aligned_two .store16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_two .store16 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 1).toNat))) <<< 1) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 1]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_store_single_of_single16 dest base off hsingle
  have henc : arm8Enc (.inst (.mem .store16 dest (.addr base off))) =
      arm8Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp [hmsb]
  let w : BitVec 32 := arm8LoadStoreImm12Word (BitVec.ofNat 2 1) (BitVec.ofNat 2 0)
    (holWordExtract 12 11 0 (off >>> 1)) (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
  have hencw : Encode (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w :=
    arm8Encode_loadStoreImm12_store16 off (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest) hoff
  have hlen : (arm8Enc (.inst (.mem .store16 dest (.addr base off)))).length = 4 :=
    arm8Enc_store_single_length_of_single16 dest base off hsingle
  have hb := hs.1
  simp only [arm8ConfigL3] at hb
  have hbdom := bytesInMemoryHOL_domain hb
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store16 dest (.addr base off))))
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
  let ins : instruction := instruction.LoadStore (LoadStore.«LoadStoreImmediate@16»
    (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
     false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))
  have hdec : Decode w = ins := by
    have hd := arm8Decode_loadStoreImm12_store16 (holWordExtract 12 11 0 (off >>> 1))
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
  have hXd : X (TN := 16) (BitVec.ofNat 5 dest) { ms with branch_hint := none } =
      BitVec.setWidth 16 (s1.regs dest) := by
    rw [arm8X16_of_valid _ hd31 hdlt]
    rw [hreg dest ⟨hdlt, hdav⟩]
  have hrun : Run ins { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        MEM := («write'Mem» (TN := 16)
          (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM } := by
    rw [show ins = (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
         false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) from rfl]
    rw [arm8Run_loadStoreImmediate_store16 _ _ _ _ _ hbase]
    rw [hXb, hXd, arm8WriteMem_only_mem_two _ _ _ _ hal1]
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
        MEM := («write'Mem» (TN := 16)
          (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
          { ms with branch_hint := none }).MEM,
        PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun]
    rfl
  have hupd4 : asmUpd (.inst (.mem .store16 dest (.addr base off)))
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
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 2 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd4]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  refine asmCaseOneMem (.mem .store16 dest (.addr base off)) dest v _ s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext ?_ ?_ ?_ ?_ ?_ ?_ hs2pc hs2dom ?_
  · rfl
  · intro x hx
    show («write'Mem» (TN := 16)
      (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = s2.mem x
    rw [arm8WriteMem_two { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 16 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x]
    rw [writeMemN_two_setWidth16 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_two s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  · intro x hx
    show («write'Mem» (TN := 16)
      (BitVec.setWidth 16 (s1.regs dest), ((s1.regs base) + off, (2, .AccType_NORMAL)))
      { ms with branch_hint := none }).MEM x = ms.MEM x
    exact arm8WriteMem_two_out { ms with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 16 (s1.regs dest)) .AccType_NORMAL hal1 he0 hel x
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


/-! ## The far-offset two-instruction lowering

When the offset is neither its own signed nine-bit form nor the scaled
twelve-bit form, `arm8_load_store_ast` emits an `AddSubImmediate@64` into the
scratch register 26 followed by a `LoadStoreImmediate` against it.  These are
the lowering equations and the branch condition they depend on.
-/

theorem arm8FarCond (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3)) :
    (decide (off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) &&
      (!!off.msb || decide (off ≠
        (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3))) = true := by
  have h1 : decide (off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) = true :=
    decide_eq_true hnsx
  have h2 : (!!off.msb || decide (off ≠
      (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3)) = true := by
    rcases hfar with h | h
    · rw [h]; rfl
    · have h' : decide (off ≠
          (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3) = true :=
        decide_eq_true h
      rw [h']
      cases hb : (!!off.msb) <;> rfl
  rw [h1, h2]
  rfl

theorem arm8Ast_load_far (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3)) :
    arm8Ast (.inst (.mem .load dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
          !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst]
  rw [if_pos (arm8FarCond off hnsx hfar)]
  simp [Bool.not_not]

theorem arm8Ast_store_far (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3)) :
    arm8Ast (.inst (.mem .store dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
          !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst]
  rw [if_pos (arm8FarCond off hnsx hfar)]
  simp [Bool.not_not]

/-- The far branch condition of the three `arm8_load_store_ast` variants: they
 test the same predicate, with the offset shifted by the log2 of the transfer
 size (3 for the eight-byte form, 2 for four bytes, 1 for two). -/
theorem arm8FarCondOf (off : BitVec 64) (shift : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> shift).toNat)) <<< shift)) :
    (decide (off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) &&
      (!!off.msb || decide (off ≠
        (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> shift).toNat)) <<< shift))) = true := by
  have h1 : decide (off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)) = true :=
    decide_eq_true hnsx
  have h2 : (!!off.msb || decide (off ≠
      (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> shift).toNat)) <<< shift)) = true := by
    rcases hfar with h | h
    · rw [h]; rfl
    · have h' : decide (off ≠
          (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> shift).toNat)) <<< shift) = true :=
        decide_eq_true h
      rw [h']
      cases hb : (!!off.msb) <;> rfl
  rw [h1, h2]
  rfl

/-- `arm8_load_store_ast32`'s two-instruction branch for `.mem .load32`: the
 same `AddSubImmediate@64` into scratch register 26 followed by a
 `LoadStoreImmediate@32` against it. -/
theorem arm8Ast_load_far32 (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat)) <<< 2)) :
    arm8Ast (.inst (.mem .load32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
          false, !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst32]
  rw [if_pos (arm8FarCondOf off 2 hnsx hfar)]
  simp [Bool.not_not]

/-- `arm8_load_store_ast32`'s two-instruction branch for `.mem .store32`. -/
theorem arm8Ast_store_far32 (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat)) <<< 2)) :
    arm8Ast (.inst (.mem .store32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
          false, !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst32]
  rw [if_pos (arm8FarCondOf off 2 hnsx hfar)]
  simp [Bool.not_not]

/-- `arm8_load_store_ast16`'s two-instruction branch for `.mem .load16`. -/
theorem arm8Ast_load_far16 (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat)) <<< 1)) :
    arm8Ast (.inst (.mem .load16 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@16»
         (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false,
          false, !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst16]
  rw [if_pos (arm8FarCondOf off 1 hnsx hfar)]
  simp [Bool.not_not]

/-- `arm8_load_store_ast16`'s two-instruction branch for `.mem .store16`. -/
theorem arm8Ast_store_far16 (dest base : Nat) (off : BitVec 64)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat)) <<< 1)) :
    arm8Ast (.inst (.mem .store16 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64»
         (1, off.msb, false,
          (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)),
          BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@16»
         (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false,
          false, !off.msb,
          (if !off.msb then (0xFF : BitVec 64) else -(0x100 : BitVec 64)),
          26, BitVec.ofNat 5 dest))] := by
  simp only [arm8Ast, arm8LoadStoreAst16]
  rw [if_pos (arm8FarCondOf off 1 hnsx hfar)]
  simp [Bool.not_not]

/-- The four-byte `Mem` pair at an address whose bytes agree with the source
 (Flapjack infrastructure; the four-byte analogue of `arm8Mem_eight_pair`). -/
theorem arm8Mem_four_pair (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i, i < 4 →
      ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    Mem (TN := 32) (address, (4, AccType.AccType_NORMAL)) ms =
      (BitVec.setWidth 32 (readMemWord (resultWidth := 64) address 4 s).1, ms) := by
  have hp := arm8Mem_four_of_bytes ms address s.mem hmem hal he0 hel
  have hv := arm8Mem_four_eq_readMemWord ms s address hal he0 hel hbe hmem
  rw [hp] at hv
  have h32 : holV2w 32 (holW2v (s.mem (address + BitVec.ofNat 64 3)) ++
      (holW2v (s.mem (address + BitVec.ofNat 64 2)) ++
        (holW2v (s.mem (address + BitVec.ofNat 64 1)) ++ holW2v (s.mem address)))) =
      BitVec.setWidth 32 (readMemWord (resultWidth := 64) address 4 s).1 := by
    have := congrArg (BitVec.setWidth 32) hv
    simpa using this
  rw [hp]
  exact Prod.ext h32 rfl

/-- The two-byte `Mem` pair at an address whose bytes agree with the source. -/
theorem arm8Mem_two_pair (ms : arm8_state) (s : AsmState 64) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (hbe : s.be = false)
    (hmem : ∀ i, i < 2 →
      ms.MEM (address + BitVec.ofNat 64 i) = s.mem (address + BitVec.ofNat 64 i)) :
    Mem (TN := 16) (address, (2, AccType.AccType_NORMAL)) ms =
      (BitVec.setWidth 16 (readMemWord (resultWidth := 64) address 2 s).1, ms) := by
  have hp := arm8Mem_two_of_bytes ms address s.mem hmem hal he0 hel
  have hv := arm8Mem_two_eq_readMemWord ms s address hal he0 hel hbe hmem
  rw [hp] at hv
  have h16 : holV2w 16 (holW2v (s.mem (address + BitVec.ofNat 64 1)) ++
      holW2v (s.mem address)) =
      BitVec.setWidth 16 (readMemWord (resultWidth := 64) address 2 s).1 := by
    have := congrArg (BitVec.setWidth 16) hv
    simpa using this
  rw [hp]
  exact Prod.ext h16 rfl

/-- The L3 four-byte write agrees on the source domain across agreeing states
 (`arm8WriteMem_four` plus `writeMemN_congr`). -/
theorem arm8WriteMem_four_congr {d : BitVec 64 → Prop} (s t : arm8_state)
    (hmem : ∀ a, d a → s.MEM a = t.MEM a)
    (address : BitVec 64) (value : BitVec 32) (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 4) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2))
    (he0t : t.SCTLR_EL1.E0E = false) (helt : t.PSTATE.EL = (0 : BitVec 2)) :
    ∀ a, d a → («write'Mem» (TN := 32) (value, (address, (4, acctype))) s).MEM a =
      («write'Mem» (TN := 32) (value, (address, (4, acctype))) t).MEM a := by
  intro a ha
  rw [arm8WriteMem_four s address value acctype hal he0 hel a,
    arm8WriteMem_four t address value acctype hal he0t helt a]
  exact writeMemN_congr hmem 4 address (BitVec.setWidth 64 value) a ha

/-- The L3 two-byte write agrees on the source domain across agreeing states. -/
theorem arm8WriteMem_two_congr {d : BitVec 64 → Prop} (s t : arm8_state)
    (hmem : ∀ a, d a → s.MEM a = t.MEM a)
    (address : BitVec 64) (value : BitVec 16) (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 2) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2))
    (he0t : t.SCTLR_EL1.E0E = false) (helt : t.PSTATE.EL = (0 : BitVec 2)) :
    ∀ a, d a → («write'Mem» (TN := 16) (value, (address, (2, acctype))) s).MEM a =
      («write'Mem» (TN := 16) (value, (address, (2, acctype))) t).MEM a := by
  intro a ha
  rw [arm8WriteMem_two s address value acctype hal he0 hel a,
    arm8WriteMem_two t address value acctype hal he0t helt a]
  exact writeMemN_congr hmem 2 address (BitVec.setWidth 64 value) a ha


/-! ## The far-offset case theorems

Offsets outside the two single-instruction paths take the two-step
`asmCaseTwoMem` route.  The negative and non-negative offsets differ in
the immediate the lowering computes and in the encoding field of the
second instruction, so each is proved separately and the two branches
are joined by the dispatching theorems at the end.
-/

/-- `decide p = true` gives `p` (Flapjack infrastructure; the L3 analogue of
`arm8OfDecideTrue`, kept local to avoid importing the `Branch` case module). -/
theorem arm8DecideOfTrue {p : Prop} (inst : Decidable p) (h : @decide p inst = true) : p := by
  cases inst with
  | isTrue hp => exact hp
  | isFalse _ => exact Bool.noConfusion h

/-- The configured address-offset window is the signed range `(-4351, 4350)`. -/
theorem arm8FarOffsetBounds (off : BitVec 64)
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true) :
    (-4351 : Int) ≤ off.toInt ∧ off.toInt ≤ 4350 := by
  simp only [asmAddrOffsetOkExact, arm8ConfigL3, asmOffsetOkExact, Bool.and_eq_true] at hok
  obtain ⟨⟨hlo, hhi⟩, -⟩ := hok
  exact ⟨arm8DecideOfTrue _ hlo, arm8DecideOfTrue _ hhi⟩

/-- An offset inside the signed nine-bit range is its own nine-bit form, so an
offset that is not is outside `[-256, 255]`. -/
theorem arm8NineBitForm_of_range (off : BitVec 64)
    (hlo : (-256 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 255) :
    off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega : 9 ≤ 64), BitVec.toInt_ofNat']
  rw [← Int.bmod_bmod_of_dvd (by norm_num : (512 : Nat) ∣ 2 ^ 64),
    ← BitVec.toInt_eq_toNat_bmod]
  rw [Int.bmod_eq_of_le (m := 512) hlo (by norm_num; omega)]

/-- `Nat.testBit` is false above a bound (Flapjack infrastructure: the
`Nat.Bitwise` lemma is not in this module's import closure). -/
theorem arm8NatTestBit_false_of_lt {n i : Nat} (h : n < 2 ^ i) : n.testBit i = false := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]

/-- The low twelve bits of `4095` are all set. -/
theorem arm8NatTestBit_4095 {i : Nat} (hi : i < 12) : (4095 : Nat).testBit i = true := by
  rw [show (4095 : Nat) = 2 ^ 12 - 1 from by norm_num, Nat.testBit_two_pow_sub_one]
  simp [hi]

/-- A word below `4096` has nothing above its low twelve bits, so the
complement of `4095` clears it. -/
theorem arm8AndNot_eq_zero_of_toNat_lt (w : BitVec 64) (h : w.toNat < 4096) :
    w &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  have hz : (0 : BitVec 64).getLsbD i = false := by simp
  rw [hz]
  by_cases hi12 : i < 12
  · have hm : (~~~(4095 : BitVec 64)).getLsbD i = false := by
      rw [BitVec.getLsbD_not]
      have h4095 : (4095 : BitVec 64).getLsbD i = true := by
        simp only [BitVec.getLsbD]
        exact arm8NatTestBit_4095 hi12
      rw [h4095]
      simp [hi]
    rw [hm, Bool.and_false]
  · have hw : w.getLsbD i = false := by
      simp only [BitVec.getLsbD]
      exact arm8NatTestBit_false_of_lt (by
        have h2 : 2 ^ 12 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega)
    rw [hw, Bool.false_and]

/-- The `AddSubImmediate@64` immediate the far-offset lowering computes is
encodable: on the far-offset branch the offset is neither its own signed
nine-bit form nor the scaled twelve-bit form, so it is at least `257` in
magnitude, and the configured window keeps the computed immediate inside
`[1, 4095]`. -/
theorem arm8FarImm_encodable (off : BitVec 64)
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))) :
    (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)) &&&
      ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  have hout : ¬((-256 : Int) ≤ off.toInt ∧ off.toInt ≤ 255) := by
    intro ⟨h1, h2⟩
    exact hnsx (arm8NineBitForm_of_range off h1 h2)
  by_cases hmsb : off.msb
  · have hcond := BitVec.toInt_eq_msb_cond off
    rw [hmsb] at hcond
    simp only [if_true] at hcond
    have hnat : (off.toNat : Int) = off.toInt + 2 ^ 64 := by omega
    have hle : off.toInt ≤ -257 := by omega
    have hneg : (-off).toNat = (-off.toInt).toNat := by
      rw [BitVec.toNat_neg]
      omega
    have hbNat : (-off - (0x100 : BitVec 64)).toNat = (-off.toInt - 256).toNat := by
      rw [BitVec.toNat_sub, hneg]
      have h256 : (0x100 : BitVec 64).toNat = 256 := by decide
      rw [h256]
      omega
    have hsmall : (-off - (0x100 : BitVec 64)).toNat < 4096 := by
      rw [hbNat]
      omega
    simp only [hmsb, Bool.not_true, Bool.false_eq_true, if_false]
    exact arm8AndNot_eq_zero_of_toNat_lt _ hsmall
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    have hcond := BitVec.toInt_eq_msb_cond off
    rw [hmsbf] at hcond
    simp only [Bool.false_eq_true, if_false] at hcond
    have hge : (256 : Int) ≤ off.toInt := by omega
    have hnat : off.toNat = off.toInt.toNat := by omega
    have hbNat : (off - (0xFF : BitVec 64)).toNat = off.toNat - 255 := by
      rw [BitVec.toNat_sub]
      have h255 : (0xFF : BitVec 64).toNat = 255 := by decide
      rw [h255]
      omega
    have hsmall : (off - (0xFF : BitVec 64)).toNat < 4096 := by
      rw [hbNat]
      omega
    simp only [hmsbf, Bool.not_false, if_true]
    exact arm8AndNot_eq_zero_of_toNat_lt _ hsmall

/-- `holUpdate` at its application form for any carrier (Flapjack
infrastructure: the memory-specialised `holUpdate_apply` does not cover the
register file). -/
theorem holUpdate_apply_general {α β : Type} [DecidableEq α] (a : α) (b : β)
    (f : α → β) (c : α) : holUpdate a b f c = if a = c then b else f c := rfl

theorem holUpdate_same {α β : Type} [DecidableEq α] (a : α) (b : β) (f : α → β) :
    holUpdate a b f a = b := by
  rw [holUpdate_apply_general, if_pos rfl]

theorem holUpdate_ne {α β : Type} [DecidableEq α] {a c : α} (h : ¬ a = c) (b : β)
    (f : α → β) : holUpdate a b f c = f c := by
  rw [holUpdate_apply_general, if_neg h]


/-- The L3 eight-byte write agrees on the source domain across agreeing states
(Flapjack infrastructure; `arm8WriteMem_eight` plus `writeMemN_congr`). -/
theorem arm8WriteMem_eight_congr {d : BitVec 64 → Prop} (s t : arm8_state)
    (hmem : ∀ a, d a → s.MEM a = t.MEM a)
    (address value : BitVec 64) (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : s.SCTLR_EL1.E0E = false) (hel : s.PSTATE.EL = (0 : BitVec 2))
    (he0t : t.SCTLR_EL1.E0E = false) (helt : t.PSTATE.EL = (0 : BitVec 2)) :
    ∀ a, d a → («write'Mem» (TN := 64) (value, (address, (8, acctype))) s).MEM a =
      («write'Mem» (TN := 64) (value, (address, (8, acctype))) t).MEM a := by
  intro a ha
  rw [arm8WriteMem_eight s address value acctype hal he0 hel a,
    arm8WriteMem_eight t address value acctype hal he0t helt a]
  exact writeMemN_congr hmem 8 address value a ha

/-- The `.mem .load` constructor of `encoder_correct arm8TargetL3` on the
far-offset path with a negative offset: `arm8_ast` emits an
`AddSubImmediate@64` of `-off - 0x100` into the scratch register 26 and
then a signed `LoadStoreImmediate@64` at `-0x100` against r26, so the
pair reads `regs base + off`.

`hlow` is the encodability of the `AddSubImmediate@64` immediate the
lowering computes; `asmAddrOffsetOkExact` supplies it, so it is a case
hypothesis here rather than part of `CaseGoal`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have hal8 := arm8MemLoad_aligned .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom := arm8MemLoad_domain .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hmemv := arm8Mem_eight_value ms s1 (s1.regs base + off) hal8 he0 hel hbe hmem hdom
  set b : BitVec 64 := -off - (0x100 : BitVec 64) with hb
  set c : BitVec 64 := -(0x100 : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .load dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
          false, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_load_far dest base off hnsx (Or.inl hmsb), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .load dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (false && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    rfl
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_load c false 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .load dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base - b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 dest) v t1.REG,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v u.REG,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base - b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base - b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base - b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base - b := by
      exact huX26
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        (match Mem (TN := 64) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
          (8, .AccType_NORMAL)) { u with branch_hint := none } with
          | (v, s') => «write'X» (TN := 64) ((BitVec.setWidth 64 v), BitVec.ofNat 5 dest) s') :=
      arm8Run_loadStoreImmediate_load { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26
    have hpair2 : Mem (TN := 64) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
        (8, AccType.AccType_NORMAL)) { u with branch_hint := none } =
        (v, { u with branch_hint := none }) := by
      rw [haddr]
      exact arm8Mem_eight_pair { u with branch_hint := none } s1 (s1.regs base + off) hal8
        (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
        (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) hbe (fun i hi => by
          have hd := hdom i hi
          have h1u : ({ u with branch_hint := none } : arm8_state).MEM
              (s1.regs base + off + BitVec.ofNat 64 i) =
              t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) := hu.mem _ hd
          have h2u : t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
              ms.MEM (s1.regs base + off + BitVec.ofNat 64 i) := by rw [ht1]
          exact h1u.trans (h2u.trans (hmem _ hd)))
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          REG := holUpdate (BitVec.ofNat 5 dest) v u.REG } := by
      rw [hrun2, hpair2]
      dsimp only
      rw [arm8WriteX_of_valid _ _ hd31 hdlt]
      simp only [BitVec.setWidth_eq]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · show holUpdate (BitVec.ofNat 5 dest) v u.REG = holUpdate (BitVec.ofNat 5 dest) v t1.REG
      rw [hu.reg]
    · intro a ha
      show u.MEM a = t1.MEM a
      exact hu.mem a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .load dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .load dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd8]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2, ht1, hs2mem x]
    exact hmem x hx
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne1 : ¬((BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k)) := by
      intro hh
      exact hkd ((arm8Reg_eq hdlt hk).mp hh).symm
    have hne2 : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne1, holUpdate_ne hne2]
  have htval : t2.REG (BitVec.ofNat 5 dest) = v := by
    rw [ht2]
    dsimp only
    show holUpdate (BitVec.ofNat 5 dest) v t1.REG (BitVec.ofNat 5 dest) = v
    rw [holUpdate_same]
  refine asmCaseTwoMem (.mem .load dest (.addr base off)) dest v t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs

/-- The `.mem .load32` constructor on the far-offset path with a negative
offset: the same `AddSubImmediate@64` into scratch register 26 followed by a
signed `LoadStoreImmediate@32` at `-0x100` against it, reading the four bytes
at `regs base + off`.

`hlow` is the encodability of the `AddSubImmediate@64` immediate the lowering
computes; `asmAddrOffsetOkExact` supplies it, so it is a case hypothesis here
rather than part of `CaseGoal`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load32_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have halm4 := arm8MemLoad_aligned_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom := arm8MemLoad_domain_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  set b : BitVec 64 := -off - (0x100 : BitVec 64) with hb
  set c : BitVec 64 := -(0x100 : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .load32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
          false, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_load_far32 dest base off hnsx (Or.inl hmsb), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .load32 dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (false && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    rfl
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_load32 c false 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base - b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 dest) v t1.REG,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v u.REG,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base - b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base - b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base - b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base - b := by
      exact huX26
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        «write'X» (TN := 32)
          ((BitVec.setWidth 32 (Mem (TN := 32)
            ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
             (4, .AccType_NORMAL)) { u with branch_hint := none }).1), BitVec.ofNat 5 dest)
          (Mem (TN := 32) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
            (4, .AccType_NORMAL)) { u with branch_hint := none }).2 :=
      arm8Run_loadStoreImmediate_load32 { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26
    have hvw : BitVec.setWidth 64
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1) = v := by
      show BitVec.setWidth 64
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1) =
        (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1
      have h4 := arm8Mem_four_eq_readMemWord ms s1 (s1.regs base + off) halm4 he0 hel hbe
        (fun i hi => hmem _ (hdom i hi))
      rw [← h4]
      simp
    have hpair2 : Mem (TN := 32) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
        (4, AccType.AccType_NORMAL)) { u with branch_hint := none } =
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1,
          { u with branch_hint := none }) := by
      rw [haddr]
      exact arm8Mem_four_pair { u with branch_hint := none } s1 (s1.regs base + off) halm4
        (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
        (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) hbe (fun i hi => by
          have hd := hdom i hi
          have h1u : ({ u with branch_hint := none } : arm8_state).MEM
              (s1.regs base + off + BitVec.ofNat 64 i) =
              t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) := hu.mem _ hd
          have h2u : t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
              ms.MEM (s1.regs base + off + BitVec.ofNat 64 i) := by rw [ht1]
          exact h1u.trans (h2u.trans (hmem _ hd)))
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          REG := holUpdate (BitVec.ofNat 5 dest) v u.REG } := by
      rw [hrun2, hpair2]
      dsimp only
      rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
      simp only [BitVec.setWidth_eq]
      rw [hvw]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · show holUpdate (BitVec.ofNat 5 dest) v u.REG = holUpdate (BitVec.ofNat 5 dest) v t1.REG
      rw [hu.reg]
    · intro a ha
      show u.MEM a = t1.MEM a
      exact hu.mem a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .load32 dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd8]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2, ht1, hs2mem x]
    exact hmem x hx
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne1 : ¬((BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k)) := by
      intro hh
      exact hkd ((arm8Reg_eq hdlt hk).mp hh).symm
    have hne2 : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne1, holUpdate_ne hne2]
  have htval : t2.REG (BitVec.ofNat 5 dest) = v := by
    rw [ht2]
    dsimp only
    show holUpdate (BitVec.ofNat 5 dest) v t1.REG (BitVec.ofNat 5 dest) = v
    rw [holUpdate_same]
  refine asmCaseTwoMem (.mem .load32 dest (.addr base off)) dest v t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs


/-- The `.mem .store` constructor on the far-offset path with a negative
offset: the same `AddSubImmediate@64` into r26 and signed
`LoadStoreImmediate@64` at `-0x100`, now storing `regs dest` at
`regs base + off`.

`hlow` is the encodability of the `AddSubImmediate@64` immediate the
lowering computes; `asmAddrOffsetOkExact` supplies it, so it is a case
hypothesis here rather than part of `CaseGoal`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  set b : BitVec 64 := -off - (0x100 : BitVec 64) with hb
  set c : BitVec 64 := -(0x100 : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .store dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
          false, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_store_far dest base off hnsx (Or.inl hmsb), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .store dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (false && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    rfl
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_store c false 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .store dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base - b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    MEM := («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL))) t1).MEM,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { u with branch_hint := none }).MEM,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base - b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base - b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base - b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hdest26 : dest ≠ 26 := by
      intro hh
      rw [hh] at hdav
      simp [arm8ConfigL3] at hdav
    have hne_dest : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hdest32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    have hXd : X (TN := 64) (BitVec.ofNat 5 dest) u = s1.regs dest := by
      rw [arm8X_of_valid u hd31 hdlt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_dest]
      exact hreg dest ⟨hdlt, hdav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base - b := by
      exact huX26
    have hXuD : X (TN := 64) (BitVec.ofNat 5 dest) { u with branch_hint := none } =
        s1.regs dest := by
      exact hXd
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { u with branch_hint := none }) := by
      rw [arm8Run_loadStoreImmediate_store { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26]
      rw [hXuD, haddr]
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          MEM := («write'Mem» (TN := 64)
            (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
            { u with branch_hint := none }).MEM } := by
      rw [hrun2, arm8WriteMem_only_mem _ _ _ _ hal8]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · exact hu.reg
    · intro a ha
      exact arm8WriteMem_eight_congr { u with branch_hint := none } t1 hu.mem
        (s1.regs base + off) (s1.regs dest) .AccType_NORMAL hal8
        (by rw [hu.sctlr, ht1]; exact he0) (by rw [hu.pstate, ht1]; exact hel) he0 hel a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
    exact arm8WriteMem_eight_out { u with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8
      (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
      (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) x
      (fun k hk h => hx (h ▸ hdom k hk))
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .store dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .store dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs0 : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 8 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  have hs2regs : ∀ k, s2.regs k = if k = dest then s1.regs dest else s1.regs k := by
    intro k
    rw [hs2regs0 k]
    by_cases hk : k = dest
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2]
    rw [arm8WriteMem_eight t1 (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x]
    rw [ht1]
    rw [← writeMemWord_mem_eight s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  have hd26 : dest ≠ 26 := by
    intro hh
    rw [hh] at hdav
    simp [arm8ConfigL3] at hdav
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
  have htval : t2.REG (BitVec.ofNat 5 dest) = s1.regs dest := by
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
    exact hreg dest ⟨hdlt, hdav⟩
  refine asmCaseTwoMem (.mem .store dest (.addr base off)) dest (s1.regs dest) t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs

/-- The `.mem .store32` constructor on the far-offset path with a negative
offset: the same `AddSubImmediate@64` into scratch register 26 followed by a
signed `LoadStoreImmediate@32` at `-0x100` against it, storing the low four
bytes of `regs dest` at `regs base + off`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store32_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have halm4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemStore_aligned_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  set b : BitVec 64 := -off - (0x100 : BitVec 64) with hb
  set c : BitVec 64 := -(0x100 : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .store32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
          false, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_store_far32 dest base off hnsx (Or.inl hmsb), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .store32 dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, true, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (false && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    rfl
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       false, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_store32 c false 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base - b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord true false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low true b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, true, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base - b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    MEM := («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL))) t1).MEM,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { u with branch_hint := none }).MEM,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base - b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base - b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base - b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base - b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hdest26 : dest ≠ 26 := by
      intro hh
      rw [hh] at hdav
      simp [arm8ConfigL3] at hdav
    have hne_dest : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hdest32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    have hXd : X (TN := 32) (BitVec.ofNat 5 dest) u = BitVec.setWidth 32 (s1.regs dest) := by
      rw [arm8X32_of_valid u hd31 hdlt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_dest]
      rw [hreg dest ⟨hdlt, hdav⟩]
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base - b := by
      exact huX26
    have hXuD : X (TN := 32) (BitVec.ofNat 5 dest) { u with branch_hint := none } =
        BitVec.setWidth 32 (s1.regs dest) := by
      exact hXd
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { u with branch_hint := none }) := by
      rw [arm8Run_loadStoreImmediate_store32 { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26]
      rw [hXuD, haddr]
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          MEM := («write'Mem» (TN := 32)
            (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
            { u with branch_hint := none }).MEM } := by
      rw [hrun2, arm8WriteMem_only_mem_four _ _ _ _ halm4]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · exact hu.reg
    · intro a ha
      exact arm8WriteMem_four_congr { u with branch_hint := none } t1 hu.mem
        (s1.regs base + off) (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4
        (by rw [hu.sctlr, ht1]; exact he0) (by rw [hu.pstate, ht1]; exact hel) he0 hel a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
    exact arm8WriteMem_four_out { u with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4
      (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
      (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) x
      (fun k hk h => hx (h ▸ hdom k hk))
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .store32 dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs0 : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 4 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  have hs2regs : ∀ k, s2.regs k = if k = dest then s1.regs dest else s1.regs k := by
    intro k
    rw [hs2regs0 k]
    by_cases hk : k = dest
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2]
    rw [arm8WriteMem_four t1 (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4 he0 hel x]
    rw [ht1]
    rw [writeMemN_four_setWidth32 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_four s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  have hd26 : dest ≠ 26 := by
    intro hh
    rw [hh] at hdav
    simp [arm8ConfigL3] at hdav
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
  have htval : t2.REG (BitVec.ofNat 5 dest) = s1.regs dest := by
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
    exact hreg dest ⟨hdlt, hdav⟩
  refine asmCaseTwoMem (.mem .store32 dest (.addr base off)) dest (s1.regs dest) t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs


/-- The `.mem .load` constructor on the far-offset path with a non-negative
offset: `arm8_ast` emits an `AddSubImmediate@64` of `off - 0xFF` into
r26 and then an unsigned `LoadStoreImmediate@64` at `+0xFF` against r26.

`hlow` is the encodability of the `AddSubImmediate@64` immediate the
lowering computes; `asmAddrOffsetOkExact` supplies it, so it is a case
hypothesis here rather than part of `CaseGoal`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat) <<< 3))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have hal8 := arm8MemLoad_aligned .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom := arm8MemLoad_domain .load dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hmemv := arm8Mem_eight_value ms s1 (s1.regs base + off) hal8 he0 hel hbe hmem hdom
  set b : BitVec 64 := off - (0xFF : BitVec 64) with hb
  set c : BitVec 64 := (0xFF : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .load dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
          true, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_load_far dest base off hnsx (Or.inr hscaled_ne), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .load dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .load dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (true && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    decide
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_load c true 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .load dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base + b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 8 s1).1
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 dest) v t1.REG,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v u.REG,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base + b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base + b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base + b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base + b := by
      exact huX26
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        (match Mem (TN := 64) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
          (8, .AccType_NORMAL)) { u with branch_hint := none } with
          | (v, s') => «write'X» (TN := 64) ((BitVec.setWidth 64 v), BitVec.ofNat 5 dest) s') :=
      arm8Run_loadStoreImmediate_load { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26
    have hpair2 : Mem (TN := 64) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
        (8, AccType.AccType_NORMAL)) { u with branch_hint := none } =
        (v, { u with branch_hint := none }) := by
      rw [haddr]
      exact arm8Mem_eight_pair { u with branch_hint := none } s1 (s1.regs base + off) hal8
        (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
        (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) hbe (fun i hi => by
          have hd := hdom i hi
          have h1u : ({ u with branch_hint := none } : arm8_state).MEM
              (s1.regs base + off + BitVec.ofNat 64 i) =
              t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) := hu.mem _ hd
          have h2u : t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
              ms.MEM (s1.regs base + off + BitVec.ofNat 64 i) := by rw [ht1]
          exact h1u.trans (h2u.trans (hmem _ hd)))
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          REG := holUpdate (BitVec.ofNat 5 dest) v u.REG } := by
      rw [hrun2, hpair2]
      dsimp only
      rw [arm8WriteX_of_valid _ _ hd31 hdlt]
      simp only [BitVec.setWidth_eq]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · show holUpdate (BitVec.ofNat 5 dest) v u.REG = holUpdate (BitVec.ofNat 5 dest) v t1.REG
      rw [hu.reg]
    · intro a ha
      show u.MEM a = t1.MEM a
      exact hu.mem a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .load dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .load dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd8]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2, ht1, hs2mem x]
    exact hmem x hx
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne1 : ¬((BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k)) := by
      intro hh
      exact hkd ((arm8Reg_eq hdlt hk).mp hh).symm
    have hne2 : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne1, holUpdate_ne hne2]
  have htval : t2.REG (BitVec.ofNat 5 dest) = v := by
    rw [ht2]
    dsimp only
    show holUpdate (BitVec.ofNat 5 dest) v t1.REG (BitVec.ofNat 5 dest) = v
    rw [holUpdate_same]
  refine asmCaseTwoMem (.mem .load dest (.addr base off)) dest v t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs

/-- The `.mem .load32` constructor on the far-offset path with a non-negative
offset: the same `AddSubImmediate@64` of `off - 0xFF` into scratch register 26
followed by an unsigned `LoadStoreImmediate@32` at `0xFF` against it. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load32_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat) <<< 2))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have halm4 := arm8MemLoad_aligned_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom := arm8MemLoad_domain_four .load32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  set b : BitVec 64 := off - (0xFF : BitVec 64) with hb
  set c : BitVec 64 := (0xFF : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .load32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
          true, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_load_far32 dest base off hnsx (Or.inr hscaled_ne), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .load32 dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (true && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 2))) <<< 2)) = false := by
    rw [hc]
    decide
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_load32 c true 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .load32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base + b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  let v : BitVec 64 := (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    REG := holUpdate (BitVec.ofNat 5 dest) v t1.REG,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 dest) v u.REG,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base + b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base + b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base + b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base + b := by
      exact huX26
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        «write'X» (TN := 32)
          ((BitVec.setWidth 32 (Mem (TN := 32)
            ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
             (4, .AccType_NORMAL)) { u with branch_hint := none }).1), BitVec.ofNat 5 dest)
          (Mem (TN := 32) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
            (4, .AccType_NORMAL)) { u with branch_hint := none }).2 :=
      arm8Run_loadStoreImmediate_load32 { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26
    have hvw : BitVec.setWidth 64
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1) = v := by
      show BitVec.setWidth 64
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1) =
        (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1
      have h4 := arm8Mem_four_eq_readMemWord ms s1 (s1.regs base + off) halm4 he0 hel hbe
        (fun i hi => hmem _ (hdom i hi))
      rw [← h4]
      simp
    have hpair2 : Mem (TN := 32) ((X (TN := 64) (26 : BitVec 5) { u with branch_hint := none }) + c,
        (4, AccType.AccType_NORMAL)) { u with branch_hint := none } =
        (BitVec.setWidth 32 (readMemWord (resultWidth := 64) (s1.regs base + off) 4 s1).1,
          { u with branch_hint := none }) := by
      rw [haddr]
      exact arm8Mem_four_pair { u with branch_hint := none } s1 (s1.regs base + off) halm4
        (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
        (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) hbe (fun i hi => by
          have hd := hdom i hi
          have h1u : ({ u with branch_hint := none } : arm8_state).MEM
              (s1.regs base + off + BitVec.ofNat 64 i) =
              t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) := hu.mem _ hd
          have h2u : t1.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
              ms.MEM (s1.regs base + off + BitVec.ofNat 64 i) := by rw [ht1]
          exact h1u.trans (h2u.trans (hmem _ hd)))
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          REG := holUpdate (BitVec.ofNat 5 dest) v u.REG } := by
      rw [hrun2, hpair2]
      dsimp only
      rw [arm8WriteX32_of_valid _ _ hd31 hdlt]
      simp only [BitVec.setWidth_eq]
      rw [hvw]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · show holUpdate (BitVec.ofNat 5 dest) v u.REG = holUpdate (BitVec.ofNat 5 dest) v t1.REG
      rw [hu.reg]
    · intro a ha
      show u.MEM a = t1.MEM a
      exact hu.mem a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .load32 dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .load32 dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2mem : ∀ x, s2.mem x = s1.mem x := by
    rw [← hupd8]
    intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  have hs2regs : ∀ k, s2.regs k = if k = dest then v else s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, if_false, v]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2, ht1, hs2mem x]
    exact hmem x hx
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne1 : ¬((BitVec.ofNat 5 dest) = (BitVec.ofNat 5 k)) := by
      intro hh
      exact hkd ((arm8Reg_eq hdlt hk).mp hh).symm
    have hne2 : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne1, holUpdate_ne hne2]
  have htval : t2.REG (BitVec.ofNat 5 dest) = v := by
    rw [ht2]
    dsimp only
    show holUpdate (BitVec.ofNat 5 dest) v t1.REG (BitVec.ofNat 5 dest) = v
    rw [holUpdate_same]
  refine asmCaseTwoMem (.mem .load32 dest (.addr base off)) dest v t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs

/-- The `.mem .store` constructor on the far-offset path with a
non-negative offset: the same `off - 0xFF` / `+0xFF` pair, storing
`regs dest` at `regs base + off`.

`hlow` is the encodability of the `AddSubImmediate@64` immediate the
lowering computes; `asmAddrOffsetOkExact` supplies it, so it is a case
hypothesis here rather than part of `CaseGoal`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat) <<< 3))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  set b : BitVec 64 := off - (0xFF : BitVec 64) with hb
  set c : BitVec 64 := (0xFF : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .store dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@64»
         (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
          true, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_store_far dest base off hnsx (Or.inr hscaled_ne), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .store dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .store dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (true && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 3))) <<< 3)) = false := by
    rw [hc]
    decide
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@64»
      (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_store c true 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .store dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base + b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    MEM := («write'Mem» (TN := 64)
      (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL))) t1).MEM,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        MEM := («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { u with branch_hint := none }).MEM,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base + b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base + b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base + b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hdest26 : dest ≠ 26 := by
      intro hh
      rw [hh] at hdav
      simp [arm8ConfigL3] at hdav
    have hne_dest : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hdest32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    have hXd : X (TN := 64) (BitVec.ofNat 5 dest) u = s1.regs dest := by
      rw [arm8X_of_valid u hd31 hdlt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_dest]
      exact hreg dest ⟨hdlt, hdav⟩
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base + b := by
      exact huX26
    have hXuD : X (TN := 64) (BitVec.ofNat 5 dest) { u with branch_hint := none } =
        s1.regs dest := by
      exact hXd
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        («write'Mem» (TN := 64)
          (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
          { u with branch_hint := none }) := by
      rw [arm8Run_loadStoreImmediate_store { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26]
      rw [hXuD, haddr]
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          MEM := («write'Mem» (TN := 64)
            (s1.regs dest, ((s1.regs base) + off, (8, .AccType_NORMAL)))
            { u with branch_hint := none }).MEM } := by
      rw [hrun2, arm8WriteMem_only_mem _ _ _ _ hal8]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · exact hu.reg
    · intro a ha
      exact arm8WriteMem_eight_congr { u with branch_hint := none } t1 hu.mem
        (s1.regs base + off) (s1.regs dest) .AccType_NORMAL hal8
        (by rw [hu.sctlr, ht1]; exact he0) (by rw [hu.pstate, ht1]; exact hel) he0 hel a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
    exact arm8WriteMem_eight_out { u with branch_hint := none } (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8
      (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
      (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) x
      (fun k hk h => hx (h ▸ hdom k hk))
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .store dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .store dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs0 : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 8 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  have hs2regs : ∀ k, s2.regs k = if k = dest then s1.regs dest else s1.regs k := by
    intro k
    rw [hs2regs0 k]
    by_cases hk : k = dest
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2]
    rw [arm8WriteMem_eight t1 (s1.regs base + off)
      (s1.regs dest) .AccType_NORMAL hal8 he0 hel x]
    rw [ht1]
    rw [← writeMemWord_mem_eight s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  have hd26 : dest ≠ 26 := by
    intro hh
    rw [hh] at hdav
    simp [arm8ConfigL3] at hdav
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
  have htval : t2.REG (BitVec.ofNat 5 dest) = s1.regs dest := by
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
    exact hreg dest ⟨hdlt, hdav⟩
  refine asmCaseTwoMem (.mem .store dest (.addr base off)) dest (s1.regs dest) t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs


/-- The `.mem .store32` constructor on the far-offset path with a
non-negative offset: the same `off - 0xFF` / `+0xFF` pair, storing the low
four bytes of `regs dest` at `regs base + off`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store32_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store32 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 2).toNat) <<< 2))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
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
  have halm4 : Aligned (TN := 64) (s1.regs base + off, 4) = true :=
    arm8MemStore_aligned_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  have hdom : ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) :=
    arm8MemStore_domain_four .store32 dest base off s1 s2 _ hspec hupd hbe hnotfail
  set b : BitVec 64 := off - (0xFF : BitVec 64) with hb
  set c : BitVec 64 := (0xFF : BitVec 64) with hc
  have hast : arm8Ast (.inst (.mem .store32 dest (.addr base off))) =
      [.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26)),
       .LoadStore (.«LoadStoreImmediate@32»
         (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
          true, c, 26, BitVec.ofNat 5 dest))] := by
    rw [arm8Ast_store_far32 dest base off hnsx (Or.inr hscaled_ne), hmsb]
    simp [hb, hc]
  have henc : arm8Enc (.inst (.mem .store32 dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, false, false, b, BitVec.ofNat 5 base, 26))) ++
      arm8Encode (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, c, 26, BitVec.ofNat 5 dest))) := by
    rw [arm8Enc, hast]
    simp
  have hlen : (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  let w1 : BitVec 32 := arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
    (BitVec.ofNat 5 base) 26
  let w2 : BitVec 32 := arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
    (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)
  have hencw1 : Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8 w1 := by
    show Encode (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) = MachineCode.ARM8
      (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b) (BitVec.ofNat 5 base) 26)
    exact arm8Encode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hfallc : (true && (c ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (c >>> 2))) <<< 2)) = false := by
    rw [hc]
    decide
  have hsxc : c = BitVec.signExtend 64 (holWordExtract 9 8 0 c) := by
    rw [arm8HolWordExtract_nine, hc]
    decide
  have hencw2 : Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8 w2 := by
    show Encode (.LoadStore (.«LoadStoreImmediate@32»
      (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
       true, c, 26, BitVec.ofNat 5 dest))) = MachineCode.ARM8
      (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest))
    exact arm8Encode_loadStoreImm9_store32 c true 26 (BitVec.ofNat 5 dest) hfallc hsxc
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem .store32 dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).getD j 0 :=
    bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  have h0 : ms.MEM ms.PC = BitVec.ofNat 8 ((w1 >>> 0).toNat) := by
    have hh := hbyte 0 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h1 : ms.MEM (ms.PC + 1) = BitVec.ofNat 8 ((w1 >>> 8).toNat) := by
    have hh := hbyte 1 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h2 : ms.MEM (ms.PC + 2) = BitVec.ofNat 8 ((w1 >>> 16).toNat) := by
    have hh := hbyte 2 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h3 : ms.MEM (ms.PC + 3) = BitVec.ofNat 8 ((w1 >>> 24).toNat) := by
    have hh := hbyte 3 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w1] using hh
  have h4 : ms.MEM (ms.PC + 4) = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
    have hh := hbyte 4 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h5 : ms.MEM (ms.PC + 5) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
    have hh := hbyte 5 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h6 : ms.MEM (ms.PC + 6) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
    have hh := hbyte 6 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have h7 : ms.MEM (ms.PC + 7) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
    have hh := hbyte 7 (by omega)
    rw [henc] at hh
    simp only [arm8Encode, hencw1, hencw2] at hh
    simp at hh
    simpa [w2] using hh
  have hbne : (BitVec.ofNat 5 base : BitVec 5) ≠ 31#5 := by
    intro hh
    apply hs31
    have hto := congrArg BitVec.toNat hh
    rw [BitVec.toNat_ofNat] at hto
    have h31 : (31#5).toNat = 31 := by decide
    rw [h31] at hto
    have hb32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
    omega
  have hrdne : (26 : BitVec 5) ≠ 31#5 := by decide
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne hrdne]
    simp only [hXb]
    show «write'X» (TN := 64) ((s1.regs base + b), BitVec.ofNat 5 26)
        { ms with branch_hint := none } =
      { ms with
        branch_hint := none,
        REG := holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG }
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
  have hbr1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).branch_hint = none := by
    rw [hrun1]
  have hexc1 : (Run (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) { ms with branch_hint := none }).exception =
      exception.NoException := by
    rw [hrun1]
    exact hexc0
  have hdec1 : Decode w1 = (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) := by
    show Decode (arm8AddSubImmediateWord false false (holWordExtract 12 11 0 b)
      (BitVec.ofNat 5 base) 26) = _
    exact arm8Decode_addSubImmediate_low false b (BitVec.ofNat 5 base) 26 hlow
  have hn1 := arm8Next_word ms w1 (.Data (.«AddSubImmediate@64» (1, false, false, b,
      BitVec.ofNat 5 base, 26))) hdec1 hbr1 hexc1 h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) (s1.regs base + b) ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    MEM := («write'Mem» (TN := 32)
      (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL))) t1).MEM,
    PC := ms.PC + 8 } with ht2
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        MEM := («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { u with branch_hint := none }).MEM,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    have huX26 : X (TN := 64) (26 : BitVec 5) u = s1.regs base + b := by
      show X (TN := 64) (BitVec.ofNat 5 26) u = s1.regs base + b
      rw [arm8X_of_valid u (by decide) (by decide), hu.reg, ht1]
      dsimp only
      show holUpdate (BitVec.ofNat 5 26) (s1.regs base + b) ms.REG (BitVec.ofNat 5 26) =
        s1.regs base + b
      rw [holUpdate_same]
    have hbase26 : base ≠ 26 := by
      intro hh
      rw [hh] at hsav
      simp [arm8ConfigL3] at hsav
    have hne_base : ¬((26 : BitVec 5) = (BitVec.ofNat 5 base)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hbase32 : base % 2 ^ 5 = base := Nat.mod_eq_of_lt (by omega)
      omega
    have huXb : X (TN := 64) (BitVec.ofNat 5 base) u = s1.regs base := by
      rw [arm8X_of_valid u hs31 hslt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_base]
      exact hreg base ⟨hslt, hsav⟩
    have hdest26 : dest ≠ 26 := by
      intro hh
      rw [hh] at hdav
      simp [arm8ConfigL3] at hdav
    have hne_dest : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hdest32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    have hXd : X (TN := 32) (BitVec.ofNat 5 dest) u = BitVec.setWidth 32 (s1.regs dest) := by
      rw [arm8X32_of_valid u hd31 hdlt, hu.reg, ht1]
      dsimp only
      rw [holUpdate_ne hne_dest]
      rw [hreg dest ⟨hdlt, hdav⟩]
    have hXu : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } =
        s1.regs base + b := by
      exact huX26
    have hXuD : X (TN := 32) (BitVec.ofNat 5 dest) { u with branch_hint := none } =
        BitVec.setWidth 32 (s1.regs dest) := by
      exact hXd
    have haddr : X (TN := 64) (26 : BitVec 5) { u with branch_hint := none } + c =
        s1.regs base + off := by
      rw [hXu, ← huXb, hb, hc]
      bv_omega
    have hu0 : u.MEM u.PC = BitVec.ofNat 8 ((w2 >>> 0).toNat) := by
      have hidx : u.PC = ms.PC + BitVec.ofNat 64 4 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain u.PC := by
        rw [hidx, hpc]
        exact hbdom 4 (by omega)
      have h1u : u.MEM u.PC = t1.MEM u.PC := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 4 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu1 : u.MEM (u.PC + 1) = BitVec.ofNat 8 ((w2 >>> 8).toNat) := by
      have hidx : u.PC + 1 = ms.PC + BitVec.ofNat 64 5 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 1) := by
        rw [hidx, hpc]
        exact hbdom 5 (by omega)
      have h1u : u.MEM (u.PC + 1) = t1.MEM (u.PC + 1) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 5 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu2 : u.MEM (u.PC + 2) = BitVec.ofNat 8 ((w2 >>> 16).toNat) := by
      have hidx : u.PC + 2 = ms.PC + BitVec.ofNat 64 6 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 2) := by
        rw [hidx, hpc]
        exact hbdom 6 (by omega)
      have h1u : u.MEM (u.PC + 2) = t1.MEM (u.PC + 2) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 6 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have hu3 : u.MEM (u.PC + 3) = BitVec.ofNat 8 ((w2 >>> 24).toNat) := by
      have hidx : u.PC + 3 = ms.PC + BitVec.ofNat 64 7 := by
        rw [hupc]
        bv_omega
      have hd : s1.memDomain (u.PC + 3) := by
        rw [hidx, hpc]
        exact hbdom 7 (by omega)
      have h1u : u.MEM (u.PC + 3) = t1.MEM (u.PC + 3) := hu.mem _ hd
      rw [h1u, ht1]
      dsimp only
      rw [hidx, hbyte 7 (by omega), henc]
      simp only [arm8Encode, hencw1, hencw2]
      simp [w2]
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hdec2 : Decode w2 = (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) := by
      show Decode (arm8LoadStoreImm9Word (BitVec.ofNat 2 2) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 c) (BitVec.ofNat 1 0) 26 (BitVec.ofNat 5 dest)) = _
      have h := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 c) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at h
      exact h
    have hb26 : ((26 : BitVec 5) == (BitVec.ofNat 5 31)) = false := by decide
    have hrun2 : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        («write'Mem» (TN := 32)
          (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
          { u with branch_hint := none }) := by
      rw [arm8Run_loadStoreImmediate_store32 { u with branch_hint := none } c false 26
        (BitVec.ofNat 5 dest) hb26]
      rw [hXuD, haddr]
    have hrun2' : Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none } =
        { u with
          branch_hint := none,
          MEM := («write'Mem» (TN := 32)
            (BitVec.setWidth 32 (s1.regs dest), ((s1.regs base) + off, (4, .AccType_NORMAL)))
            { u with branch_hint := none }).MEM } := by
      rw [hrun2, arm8WriteMem_only_mem_four _ _ _ _ halm4]
    have hbr2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).branch_hint =
        none := by
      rw [hrun2']
    have hexc2 : (Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) { u with branch_hint := none }).exception =
        exception.NoException := by
      rw [hrun2']
      show u.exception = exception.NoException
      rw [hu.exc]
      exact hexc0
    have hn2 := arm8Next_word u w2 (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         false, c, 26, BitVec.ofNat 5 dest))) hdec2 hbr2 hexc2 hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := by rw [hu.pc, ht1]
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hupc]
      bv_omega
    · exact hu.reg
    · intro a ha
      exact arm8WriteMem_four_congr { u with branch_hint := none } t1 hu.mem
        (s1.regs base + off) (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4
        (by rw [hu.sctlr, ht1]; exact he0) (by rw [hu.pstate, ht1]; exact hel) he0 hel a ha
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
    exact arm8WriteMem_four_out { u with branch_hint := none } (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4
      (by show u.SCTLR_EL1.E0E = false; rw [hu.sctlr, ht1]; exact he0)
      (by show u.PSTATE.EL = (0 : BitVec 2); rw [hu.pstate, ht1]; exact hel) x
      (fun k hk h => hx (h ▸ hdom k hk))
  have htok1 : arm8Ok t1 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht1]
      exact hexc0
    · rw [ht1]
      have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 4) = true
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
  have htpc1 : t1.PC = ms.PC + 4 := by rw [ht1]
  have htmem1 : ∀ x, ¬ s1.memDomain x → t1.MEM x = ms.MEM x := by
    intro x hx
    rw [ht1]
  have htcode1 : ∀ pc, pc ∈ allPcs (arm8Enc (.inst (.mem .store32 dest (.addr base off)))).length
      s1.pc 0 → t1.MEM pc = ms.MEM pc := by
    intro pc hpc'
    rw [ht1]
  have htok2 : arm8Ok t2 = true := by
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, ?_, ?_⟩
    · rw [ht2, ht1]
      exact hexc0
    · rw [ht2]
      have h8' : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
      change holAligned 2 (ms.PC + 8) = true
      rw [(alignedAddSub 2 ms.PC 8 h8').1, halign]
  have htpc2 : t2.PC = ms.PC + 8 := by rw [ht2]
  have hupd8 : asmUpd (.inst (.mem .store32 dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    rfl
  have hs2dom : s2.memDomain = s1.memDomain := by
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  have hs2regs0 : ∀ k, s2.regs k = s1.regs k := by
    intro k
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  have hs2mem : ∀ x, s2.mem x =
      (writeMemWord (valueWidth := 64) (s1.regs base + off) 4 (s1.regs dest) s1).mem x := by
    intro x
    rw [← hupd8]
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, if_false]
  have hs2regs : ∀ k, s2.regs k = if k = dest then s1.regs dest else s1.regs k := by
    intro k
    rw [hs2regs0 k]
    by_cases hk : k = dest
    · rw [if_pos hk, hk]
    · rw [if_neg hk]
  have htmemIn : ∀ x, s1.memDomain x → t2.MEM x = s2.mem x := by
    intro x hx
    rw [ht2]
    rw [arm8WriteMem_four t1 (s1.regs base + off)
      (BitVec.setWidth 32 (s1.regs dest)) .AccType_NORMAL halm4 he0 hel x]
    rw [ht1]
    rw [writeMemN_four_setWidth32 (memState ms.MEM) (s1.regs base + off) (s1.regs dest) x]
    rw [← writeMemWord_mem_four s1 ms.MEM (s1.regs base + off) (s1.regs dest) x hbe
      (hmem x hx).symm]
    exact (hs2mem x).symm
  have hd26 : dest ≠ 26 := by
    intro hh
    rw [hh] at hdav
    simp [arm8ConfigL3] at hdav
  have htreg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false → k ≠ dest →
      t2.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k) := by
    intro k hk hav hkd
    have hk26 : k ≠ 26 := by
      intro hh
      rw [hh] at hav
      simp [arm8ConfigL3] at hav
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 k)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hk32 : k % 2 ^ 5 = k := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
  have htval : t2.REG (BitVec.ofNat 5 dest) = s1.regs dest := by
    have hne : ¬((26 : BitVec 5) = (BitVec.ofNat 5 dest)) := by
      intro hh
      have hto := congrArg BitVec.toNat hh
      have h26 : ((26 : BitVec 5)).toNat = 26 := by decide
      rw [h26, BitVec.toNat_ofNat] at hto
      have hd32 : dest % 2 ^ 5 = dest := Nat.mod_eq_of_lt (by omega)
      omega
    rw [ht2, ht1]
    dsimp only
    rw [holUpdate_ne hne]
    exact hreg dest ⟨hdlt, hdav⟩
  refine asmCaseTwoMem (.mem .store32 dest (.addr base off)) dest (s1.regs dest) t1 t2 s1 s2 ms
    ⟨hs, ⟨hok, hpc, hmem, hreg, hfp⟩⟩ hnext1 hnext2 hnext2_out hlen htok1 htpc1 htmem1 htcode1 htok2 htpc2 htmemIn
    htreg htval hs2pc hs2dom hs2regs



/-- The far-offset branch of the `.mem .load` constructor: the offset is neither
its own signed nine-bit form nor the scaled twelve-bit form, so `arm8_ast`
emits the two-instruction lowering. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_far (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3))
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms := by
  have hlow := arm8FarImm_encodable off hok hnsx
  by_cases hmsb : off.msb
  · exact arm8_encoder_correct_mem_load_far_neg dest base off s1 s2 ms h hnsx hmsb (by
      simp only [hmsb, Bool.not_true, Bool.false_eq_true, if_false] at hlow
      exact hlow)
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    rcases hfar with htrue | hscaled
    · rw [htrue] at hmsbf
      exact absurd hmsbf (by decide)
    · exact arm8_encoder_correct_mem_load_far_pos dest base off s1 s2 ms h hnsx hmsbf hscaled (by
        simp only [hmsbf, Bool.not_false, if_true] at hlow
        exact hlow)

/-- The far-offset branch of the `.mem .store` constructor: the offset is neither
its own signed nine-bit form nor the scaled twelve-bit form, so `arm8_ast`
emits the two-instruction lowering. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_far (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hfar : off.msb = true ∨
      ¬(off = (BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 3).toNat)) <<< 3))
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true) :
    CaseGoal (.inst (.mem .store dest (.addr base off))) s1 s2 ms := by
  have hlow := arm8FarImm_encodable off hok hnsx
  by_cases hmsb : off.msb
  · exact arm8_encoder_correct_mem_store_far_neg dest base off s1 s2 ms h hnsx hmsb (by
      simp only [hmsb, Bool.not_true, Bool.false_eq_true, if_false] at hlow
      exact hlow)
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    rcases hfar with htrue | hscaled
    · rw [htrue] at hmsbf
      exact absurd hmsbf (by decide)
    · exact arm8_encoder_correct_mem_store_far_pos dest base off s1 s2 ms h hnsx hmsbf hscaled (by
        simp only [hmsbf, Bool.not_false, if_true] at hlow
        exact hlow)

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
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 3]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_load_single_of_single dest base off hsingle
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
    arm8Enc_load_single_length_of_single dest base off hsingle
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
scaled twelve-bit path of `e_LoadStoreImmediate`: a non-negative offset equal to
its scaled twelve-bit form (`hmsb`, `hoff`), covering scaled offsets beyond the
signed nine-bit range as well.  The memory obligations are discharged as in the
`imm9` store case. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
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
  have hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3)) = true := by
    right
    have hbeq : (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> 3).toNat))) <<< 3) = true := by
      rw [beq_iff_eq, arm8ScaledForm_eq off 3]
      exact hoff
    rw [hmsb]
    simp only [Bool.not_false, Bool.true_and]
    exact hbeq
  have hast := arm8Ast_store_single_of_single dest base off hsingle
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
    arm8Enc_store_single_length_of_single dest base off hsingle
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
