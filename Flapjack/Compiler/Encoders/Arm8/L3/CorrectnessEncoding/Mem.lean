import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldCase

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
`MemOp_LOAD`. -/
theorem arm8ELoadStoreImm9_load (offset : BitVec 64) (rn rt : BitVec 5)
    (hfall : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt)) =
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
  have hfall' : ¬((offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = true) := by
    intro h; rw [hfall] at h; simp at h
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hload, hnrm, hunpriv, hpref,
    hstore, Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true, holV2w_one_false]
  split_ifs with hg
  all_goals first | rfl | exact absurd hg hfall'

/-- `e_load_store` of `LoadStoreImmediate@64` on the signed nine-bit path for
`MemOp_STORE`. -/
theorem arm8ELoadStoreImm9_store (offset : BitVec 64) (rn rt : BitVec 5)
    (hfall : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    e_load_store (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt)) =
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
  have hfall' : ¬((offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = true) := by
    intro h; rw [hfall] at h; simp at h
  simp only [e_load_store, e_LoadStoreImmediate, hs, h3, hnrm, hunpriv, hpref, hstore,
    Bool.false_eq_true, if_false, hnf, if_true, Bool.true_and, Bool.and_true, holV2w_one_false]
  split_ifs with hg
  all_goals first | rfl | exact absurd hg hfall'

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
theorem arm8Encode_loadStoreImm9_load (offset : BitVec 64) (rn rt : BitVec 5)
    (hfall : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 1)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_load offset rn rt hfall hsx

/-- `Encode` of the nine-bit `LoadStoreImmediate@64` store. -/
theorem arm8Encode_loadStoreImm9_store (offset : BitVec 64) (rn rt : BitVec 5)
    (hfall : (offset ==
      (BitVec.setWidth 64 (holWordExtract 12 11 0 (offset >>> 3))) <<< 3) = false)
    (hsx : offset = BitVec.signExtend 64 (holWordExtract 9 8 0 offset)) :
    Encode (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         true, offset, rn, rt))) =
      MachineCode.ARM8 (arm8LoadStoreImm9Word (BitVec.ofNat 2 3) (BitVec.ofNat 2 0)
        (holWordExtract 9 8 0 offset) (BitVec.ofNat 1 0) rn rt) :=
  arm8ELoadStoreImm9_store offset rn rt hfall hsx


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

end Flapjack.Compiler.Encoders.Arm8.L3
