module

public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.AddSubImmediate
public import Flapjack.Compiler.Encoders.Arm8.L3.CorrectnessEncoding.ShiftBitfieldCase
public import Flapjack.Compiler.Encoders.Arm8.MemLemmas
public import Mathlib.Data.List.GetD

@[expose] public section

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


/-- `holW2v` of a `width`-bit word has `width` bits (Flapjack infrastructure;
    the generic form of `holW2v_length{8,16,32}`). -/
theorem holW2v_lengthN {width : Nat} [NeZero width] (value : BitVec width) :
    (holW2v value).length = width := by
  simp [holW2v]

/-- `holW2v` at index `m` is the `m`-th high-to-low bit (Flapjack
    infrastructure; the generic form of `holW2v_getElem?_{16,32}`). -/
theorem holW2v_getElem?N {width : Nat} [NeZero width] (value : BitVec width) (m : Nat) :
    (holW2v value)[m]? = if m < width then some (value.getLsbD (width - 1 - m)) else none := by
  simp only [holW2v, List.getElem?_map]
  by_cases hm : m < width
  · simp [hm]
  · simp [hm]

/-- The `i`-th eight-bit field of a `8 * n`-bit word has eight bits (Flapjack
    infrastructure; the generic form of `holField_{two,four}_length`). -/
theorem holFieldN_length {n : Nat} [NeZero (8 * n)] (value : BitVec (8 * n)) (i : Nat)
    (hi : i < n) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (8 * n - 8 * i < 8) := by omega
  have hmin : min (8 * n - 8 * i) (8 * n) = 8 * n - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_lengthN, hmin, hge, ite_false,
    List.length_take, List.length_drop]
  omega

/-- The `i`-th eight-bit field of a `8 * n`-bit word is the byte `8i .. 8i+7`
    (Flapjack infrastructure; the generic form of
    `holField_{two,four}_getElem?`). -/
theorem holFieldN_getElem? {n : Nat} [NeZero (8 * n)] (value : BitVec (8 * n)) (i j : Nat)
    (hi : i < n) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  have h8 : 8 * i + 7 + 1 - 8 * i = 8 := by omega
  have hge : ¬ (8 * n - 8 * i < 8) := by omega
  have hmin : min (8 * n - 8 * i) (8 * n) = 8 * n - 8 * i := Nat.min_eq_left (by omega)
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_lengthN, List.length_take, hmin, hge,
    ite_false]
  rw [List.getElem?_drop]
  rw [show 8 * n - 8 * i - 8 + (7 - j) = 8 * n - 1 - 8 * i - j by omega]
  rw [List.getElem?_take_of_lt (by omega : 8 * n - 1 - 8 * i - j < 8 * n - 8 * i)]
  rw [holW2v_getElem?N]
  have hlt : 8 * n - 1 - 8 * i - j < 8 * n := by omega
  have hidx : 8 * n - 1 - (8 * n - 1 - 8 * i - j) = 8 * i + j := by omega
  simp only [hlt, ite_true, hidx]

/-- The byte `write'Mem` stores at `address + i` for a `8 * n`-bit value
    (Flapjack infrastructure; the generic form of `arm8HolByte{8,16,32}`). -/
theorem arm8HolByteN {n : Nat} [NeZero (8 * n)] (value : BitVec (8 * n)) (i : Nat)
    (hi : i < n) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Flapjack.RiscV.L3.holV2w]
  rw [getLsbD_holFcpWord]
  have hlen := holFieldN_length value i hi
  simp only [hj, decide_true, Bool.true_and, hlen, show 8 - 1 - j = 7 - j by omega]
  rw [List.getD_eq_getElem?_getD, holFieldN_getElem? value i j hi hj]
  simp only [Option.getD_some, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]

/-- `Aligned` at a power-of-two size is `toNat` divisibility
(Flapjack infrastructure; the generic form of `Aligned_two_iff`/`Aligned_four_iff`/
`arm8Aligned_eight_iff`). -/
theorem arm8Aligned_iff (a : BitVec 64) {n : Nat} :
    Aligned (TN := 64) (a, n) = true ↔ a.toNat % n = 0 := by
  simp only [Aligned, Align, beq_iff_eq]
  constructor
  · intro h
    have ht := congrArg BitVec.toNat h
    have hle : n * (a.toNat / n) ≤ a.toNat := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle a.isLt)] at ht
    rw [ht]
    exact Nat.mul_mod_right n (a.toNat / n)
  · intro h
    apply BitVec.eq_of_toNat_eq
    have hle : n * (a.toNat / n) ≤ a.toNat := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self _ _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle a.isLt), Nat.mul_comm]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)).symm

/-- `holAligned` at `k` bits implies `Aligned` at the power-of-two size `2 ^ k`
(Flapjack infrastructure; the generic form of
`arm8Aligned_{one,two,four,eight}_of_holAligned`). -/
theorem arm8AlignedN_of_holAligned (a : BitVec 64) {n k : Nat}
    (hpow : n = 2 ^ k) (h : holAligned k a = true) :
    Aligned (TN := 64) (a, n) = true := by
  rw [arm8Aligned_iff a, hpow]
  exact (holAligned_iff k a).mp h

/-- A successful store of `n = 2 ^ k` bytes has its effective address
`n`-byte aligned (Flapjack infrastructure; the generic form of
`arm8MemStore_aligned_{one,two,four,eight}`). -/
theorem arm8MemStore_alignedN {n k : Nat} (hpow : n = 2 ^ k) (op : HolMemop)
    (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) n)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, n) = true := by
  have hlog : holLOG2 n = k := by
    rw [hpow]
    exact holLOG_UNIQUE 2 (2 ^ k) k
      ⟨Nat.le_refl _, Nat.pow_lt_pow_succ (a := 2) (n := k) (by decide)⟩
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  rw [hlog] at hal
  exact arm8AlignedN_of_holAligned _ hpow (by simpa using hal)

/-- A successful store of `n = 2 ^ k` bytes has every written address in the
source memory domain (Flapjack infrastructure; the generic form of
`arm8MemStore_domain_{one,two,four,eight}`). -/
theorem arm8MemStore_domainN {n : Nat} (op : HolMemop)
    (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) n)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ i, i < n → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 i) := by
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at hfail
  obtain ⟨-, hf⟩ := (Bool.or_eq_false_iff).1 hfail
  exact writeMemWord_domain (s1.regs base + off) n (s1.regs r) s1 hbe (not_of_eq_false hf)

/-- A successful load of `n = 2 ^ k` bytes has its effective address
`n`-byte aligned (Flapjack infrastructure; the generic form of
`arm8MemLoad_aligned_{one,two,four,eight}`). -/
theorem arm8MemLoad_alignedN {n k : Nat} (hpow : n = 2 ^ k) (op : HolMemop)
    (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) n)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, n) = true := by
  have hlog : holLOG2 n = k := by
    rw [hpow]
    exact holLOG_UNIQUE 2 (2 ^ k) k
      ⟨Nat.le_refl _, Nat.pow_lt_pow_succ (a := 2) (n := k) (by decide)⟩
  have hfail : s2.failed = false := boolOfNotTrue hok
  rw [← hupd] at hfail
  simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
    Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false] at hfail
  obtain ⟨hal, -⟩ := (Bool.or_eq_false_iff).1 hfail
  rw [hlog] at hal
  exact arm8AlignedN_of_holAligned _ hpow (by simpa using hal)

/-- A successful load of `n = 2 ^ k` bytes reads only addresses in the source
memory domain (Flapjack infrastructure; the generic form of
`arm8MemLoad_domain_{one,two,four,eight}`). -/
theorem arm8MemLoad_domainN {n k : Nat} (hpow : n = 2 ^ k) (op : HolMemop)
    (r base : Nat) (off : BitVec 64) (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) n)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ i, i < n → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 i) := by
  have hspec' : memOp (width := 64) op = memLoad (width := 64) (2 ^ k) := by
    rw [← hpow]
    exact hspec
  have h := memLoadDomain op r base off s1 s2 k pc hspec' hupd hbe hok
  intro i hi
  exact h i (by
    rw [← hpow]
    exact hi)

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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.true_and, Bool.and_true]
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.true_and, Bool.and_true]
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
    hstore, Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true, holV2w_one_false]
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
    simp only [Bool.false_eq_true, ite_false]
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
    ite_false, Bool.false_and, Bool.false_eq_true]

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
    ite_false, Bool.false_and, Bool.false_eq_true]

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
    ite_false, ite_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

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
    ite_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]


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


/-- The scaled twelve-bit form of `arm8_load_store_ast` (a zero-extended
 twelve-bit slice shifted into place) is the `hoff` form the case theorems use:
 `setWidth 64` of the low twelve bits of the shifted offset. -/
theorem arm8ScaledForm_eq (off : BitVec 64) (shift : BitVec 64) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> shift).toNat))) =
      BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> shift)) := by
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract]

/-- The one-instruction branch condition of `arm8_load_store_ast*` at scale
`k`: if the offset is its own signed nine-bit form or a non-negative scaled
twelve-bit form, the far-offset branch's guard cannot hold (Flapjack
infrastructure shared by the `arm8Ast_*_single_of_single*` lemmas). -/
theorem arm8SingleBranch_absurd (off k : BitVec 64)
    (hsingle : off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> k).toNat))) <<< k)) = true)
    (hne : off ≠ BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))
    (hrest : off.msb = true ∨
      off ≠ (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> k).toNat))) <<< k) : False := by
  rcases hsingle with hsx | hscaled
  · exact hne hsx
  · rw [Bool.and_eq_true, beq_iff_eq] at hscaled
    obtain ⟨hunsigned, hbeq⟩ := hscaled
    rcases hrest with hmsb | hne'
    · rw [hmsb] at hunsigned
      exact absurd hunsigned (by decide)
    · exact hne' hbeq

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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 3 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 3 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 2 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 2 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 1 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
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
    rw [Bool.and_eq_true, Bool.or_eq_true] at hcond
    exact (arm8SingleBranch_absurd off 1 hsingle (by simpa using hcond.1)
      (hcond.2.imp (by simpa using ·) (by simpa using ·))).elim
  · rfl

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
    simp only [Bool.false_eq_true, ite_false]
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
  exact arm8AlignedN_of_holAligned a (n := 8) (k := 3) (by decide) h
theorem arm8MemStore_aligned (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 8) = true := by
  exact arm8MemStore_alignedN (n := 8) (k := 3) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemStore_domain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemStore_domainN op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_aligned (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 8) = true := by
  exact arm8MemLoad_alignedN (n := 8) (k := 3) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_domain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 8)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 8 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemLoad_domainN (n := 8) (k := 3) (by decide) op r base off s1 s2 pc hspec hupd hbe hok
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
identifies the nested `holUpdate` chain with the if-chain `writeMemBytes` uses. -/

/-- `holUpdate` at its application form (Flapjack infrastructure: the rendered
`holUpdate` is an abbreviation, so `rw [holUpdate]` does not fire). -/
theorem holUpdate_apply (a : BitVec 64) (b : BitVec 8) (f : BitVec 64 → BitVec 8)
    (c : BitVec 64) :
    holUpdate a b f c = if a = c then b else f c := rfl

/-- The eight nested `holUpdate`s `write'Mem` builds are the if-chain
`writeMemBytes` uses (Flapjack infrastructure). -/
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
  simp only [holField, holShiftr, h8, holFixwidth, holW2v_length, hmin, hge, ite_false,
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
    ite_false]
  rw [List.getElem?_drop]
  rw [show 64 - 8 * i - 8 + (7 - j) = 63 - 8 * i - j by omega]
  rw [List.getElem?_take_of_lt (by omega : 63 - 8 * i - j < 64 - 8 * i)]
  rw [holW2v_getElem?]
  have hlt : 63 - 8 * i - j < 64 := by omega
  have hidx : 63 - (63 - 8 * i - j) = 8 * i + j := by omega
  simp only [hlt, ite_true, hidx]

/-- The byte `write'Mem` stores at `address + i` is the byte `writeMemBytes` stores
there (Flapjack infrastructure). -/
theorem arm8HolByte (value : BitVec 64) (i : Nat) (hi : i < 8) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  exact arm8HolByteN (n := 8) value i hi
theorem arm8WriteMem_eight (ms : arm8_state) (address : BitVec 64) (value : BitVec 64)
    (acctype : AccType)
    (hal : Aligned (TN := 64) (address, 8) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2))
    (x : BitVec 64) :
    («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms).MEM x =
      writeMemBytes ms.MEM 8 address value x := by
  simp only [«write'Mem», writeMemBytes]
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


/-- `write'Mem` changes only `MEM` (Flapjack infrastructure). -/
theorem arm8WriteMem_only_mem (ms : arm8_state) (value : BitVec 64) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 8) = true) :
    («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 64) (value, (address, (8, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 8 acctype true hal]

/-! ## The four-byte `Mem` helpers -/

theorem holW2v_length32 (value : BitVec 32) : (holW2v value).length = 32 := by
  exact holW2v_lengthN value
theorem holW2v_getElem?_32 (value : BitVec 32) (m : Nat) :
    (holW2v value)[m]? = if m < 32 then some (value.getLsbD (31 - m)) else none := by
  exact holW2v_getElem?N value m
theorem holField_four_length (value : BitVec 32) (i : Nat) (hi : i < 4) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  exact holFieldN_length (n := 4) value i hi
theorem holField_four_getElem? (value : BitVec 32) (i j : Nat) (hi : i < 4) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  exact holFieldN_getElem? (n := 4) value i j hi hj
theorem arm8HolByte32 (value : BitVec 32) (i : Nat) (hi : i < 4) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  exact arm8HolByteN (n := 4) value i hi
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
theorem writeMemBytes_four_setWidth32 (m : BitVec 64 → BitVec 8) (a w : BitVec 64)
    (x : BitVec 64) :
    writeMemBytes m 4 a (BitVec.setWidth 64 (BitVec.setWidth 32 w)) x =
      writeMemBytes m 4 a w x := by
  simp only [writeMemBytes]
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
      writeMemBytes ms.MEM 4 address (BitVec.setWidth 64 value) x := by
  simp only [«write'Mem», writeMemBytes]
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

theorem arm8WriteMem_only_mem_four (ms : arm8_state) (value : BitVec 32) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 4) = true) :
    («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 32) (value, (address, (4, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 4 acctype true hal]

theorem arm8Aligned_four_of_holAligned (a : BitVec 64)
    (h : holAligned 2 a = true) : Aligned (TN := 64) (a, 4) = true := by
  exact arm8AlignedN_of_holAligned a (n := 4) (k := 2) (by decide) h
theorem arm8MemStore_aligned_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 4) = true := by
  exact arm8MemStore_alignedN (n := 4) (k := 2) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemStore_domain_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemStore_domainN op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_aligned_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 4) = true := by
  exact arm8MemLoad_alignedN (n := 4) (k := 2) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_domain_four (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 4)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 4 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemLoad_domainN (n := 4) (k := 2) (by decide) op r base off s1 s2 pc hspec hupd hbe hok
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
  simp only [«write'X», hcond, ite_true]

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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.true_and, Bool.and_true]
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.true_and, Bool.and_true]
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
    hstore, Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true]
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

/-! ## The one-byte `Mem` layer

The `load8`/`store8` lowerings emit one `LoadStoreImmediate@8`; its `Mem`
transfer is one byte, and the register write is the zero-extended byte.
-/

theorem arm8ShiftRight_zero (x : BitVec 64) : x >>> (0 : Nat) = x := rfl

/-! ## The one-byte `Mem` helpers -/

theorem holW2v_length8 (value : BitVec 8) : (holW2v value).length = 8 := by
  exact holW2v_lengthN value
theorem holField_eight_of_length (l : List Bool) (h : l.length = 8) : holField 7 0 l = l := by
  have ht : (l.take 8).length = 8 := by rw [List.length_take, h]; omega
  simp only [holField, holShiftr, holFixwidth, h, Nat.sub_zero, ht, Nat.sub_self]
  exact List.take_of_length_le (by omega)

theorem arm8HolByte8 (value : BitVec 8) :
    holV2w 8 (holField 7 0 (holW2v value)) = value := by
  rw [holField_eight_of_length _ (holW2v_length8 value), holV2w_holW2v]

theorem arm8Aligned_one_of_holAligned (a : BitVec 64)
    (_h : holAligned 0 a = true) : Aligned (TN := 64) (a, 1) = true := by
  exact arm8AlignedN_of_holAligned a (n := 1) (k := 0) (by decide) _h
theorem arm8Mem_one (ms : arm8_state) (address : BitVec 64)
    (hal : Aligned (TN := 64) (address, 1) = true)
    (he0 : ms.SCTLR_EL1.E0E = false) (hel : ms.PSTATE.EL = (0 : BitVec 2)) :
    Mem (TN := 8) (address, (1, AccType.AccType_NORMAL)) ms = (ms.MEM address, ms) := by
  simp only [Mem]
  simp [holFor]
  constructor
  · rw [CheckAlignment_aligned ms address 1 AccType.AccType_NORMAL false hal]
    rw [BigEndian_false ms hel he0]
    simp only [Bool.false_eq_true, ite_false]
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
      writeMemBytes ms.MEM 1 address (BitVec.setWidth 64 value) x := by
  simp only [«write'Mem», writeMemBytes]
  simp [holFor, CheckAlignment_aligned ms address 1 acctype true hal,
    BigEndian_false ms hel he0, arm8HolByte8, holUpdate_apply]
  by_cases h : x = address
  · rw [ite_eq_left h.symm, ite_eq_left h]
  · rw [ite_eq_right (fun hh => h hh.symm), ite_eq_right h]


/-- A one-byte machine write ignores the `setWidth 8`-then-`setWidth 64` round
trip of its value (Flapjack infrastructure). -/
theorem writeMemBytes_one_setWidth8 (m : BitVec 64 → BitVec 8) (a w x : BitVec 64) :
    writeMemBytes m 1 a (BitVec.setWidth 64 (BitVec.setWidth 8 w)) x =
      writeMemBytes m 1 a w x := by
  simp only [writeMemBytes]
  by_cases h : x = a
  · simp [h]
  · simp [h]


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
  exact arm8MemStore_alignedN (n := 1) (k := 0) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemStore_domain_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemStore_domainN op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_aligned_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 1) = true := by
  exact arm8MemLoad_alignedN (n := 1) (k := 0) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_domain_one (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 1)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 1 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemLoad_domainN (n := 1) (k := 0) (by decide) op r base off s1 s2 pc hspec hupd hbe hok
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
    hstore, Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    ite_false, ite_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

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
    ite_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

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


/-! ## The two-byte `Mem` layer

The `load16`/`store16` lowerings emit one `LoadStoreImmediate@16`; its `Mem`
transfer is two bytes, and the register write is the zero-extended halfword.
-/

theorem holW2v_length16 (value : BitVec 16) : (holW2v value).length = 16 := by
  exact holW2v_lengthN value
theorem holW2v_getElem?_16 (value : BitVec 16) (m : Nat) :
    (holW2v value)[m]? = if m < 16 then some (value.getLsbD (15 - m)) else none := by
  exact holW2v_getElem?N value m
theorem holField_two_length (value : BitVec 16) (i : Nat) (hi : i < 2) :
    (holField (8 * i + 7) (8 * i) (holW2v value)).length = 8 := by
  exact holFieldN_length (n := 2) value i hi
theorem holField_two_getElem? (value : BitVec 16) (i j : Nat) (hi : i < 2) (hj : j < 8) :
    (holField (8 * i + 7) (8 * i) (holW2v value))[7 - j]? =
      some (value.getLsbD (8 * i + j)) := by
  exact holFieldN_getElem? (n := 2) value i j hi hj
theorem arm8HolByte16 (value : BitVec 16) (i : Nat) (hi : i < 2) :
    holV2w 8 (holField (8 * i + 7) (8 * i) (holW2v value)) =
      (value >>> (8 * i)).setWidth 8 := by
  exact arm8HolByteN (n := 2) value i hi
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

theorem writeMemBytes_two_setWidth16 (m : BitVec 64 → BitVec 8) (a w x : BitVec 64) :
    writeMemBytes m 2 a (BitVec.setWidth 64 (BitVec.setWidth 16 w)) x =
      writeMemBytes m 2 a w x := by
  simp only [writeMemBytes]
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
      writeMemBytes ms.MEM 2 address (BitVec.setWidth 64 value) x := by
  simp only [«write'Mem», writeMemBytes]
  simp [holFor, CheckAlignment_aligned ms address 2 acctype true hal,
    BigEndian_false ms hel he0]
  have hb0 : holV2w 8 (holField 7 0 (holW2v value)) = BitVec.setWidth 8 value := by
    simpa using arm8HolByte16 value 0 (by decide)
  have hb1 : holV2w 8 (holField 15 8 (holW2v value)) = BitVec.setWidth 8 (value >>> 8) := by
    simpa using arm8HolByte16 value 1 (by decide)
  rw [hb0, hb1]
  exact holUpdate_two address ms.MEM _ _ x

theorem arm8WriteMem_only_mem_two (ms : arm8_state) (value : BitVec 16) (address : BitVec 64)
    (acctype : AccType) (hal : Aligned (TN := 64) (address, 2) = true) :
    («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms) =
      { ms with MEM := («write'Mem» (TN := 16) (value, (address, (2, acctype))) ms).MEM } := by
  simp only [«write'Mem»]
  simp [holFor, CheckAlignment_aligned ms address 2 acctype true hal]

theorem arm8Aligned_two_of_holAligned (a : BitVec 64)
    (h : holAligned 1 a = true) : Aligned (TN := 64) (a, 2) = true := by
  exact arm8AlignedN_of_holAligned a (n := 2) (k := 1) (by decide) h
theorem arm8MemStore_aligned_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2) = true := by
  exact arm8MemStore_alignedN (n := 2) (k := 1) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemStore_domain_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memStore (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemStore_domainN op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_aligned_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2) = true := by
  exact arm8MemLoad_alignedN (n := 2) (k := 1) (by decide)
    op r base off s1 s2 pc hspec hupd hbe hok
theorem arm8MemLoad_domain_two (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64)
    (hspec : memOp (width := 64) op = memLoad (width := 64) 2)
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    ∀ k, k < 2 → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  exact arm8MemLoad_domainN (n := 2) (k := 1) (by decide) op r base off s1 s2 pc hspec hupd hbe hok
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
    simp only [Bool.false_eq_true, ite_false]
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
    hstore, Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true,
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true]
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true]
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
    Bool.false_eq_true, ite_false, hnf, ite_true, Bool.and_true]
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
    ite_false, ite_true, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

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
    ite_false, Bool.false_and, Bool.false_eq_true, Nat.reduceDiv]

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
  rw [ite_eq_left (arm8FarCond off hnsx hfar)]
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
  rw [ite_eq_left (arm8FarCond off hnsx hfar)]
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
  rw [ite_eq_left (arm8FarCondOf off 2 hnsx hfar)]
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
  rw [ite_eq_left (arm8FarCondOf off 2 hnsx hfar)]
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
  rw [ite_eq_left (arm8FarCondOf off 1 hnsx hfar)]
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
  rw [ite_eq_left (arm8FarCondOf off 1 hnsx hfar)]
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
magnitude, and a window inside `[-4351, 4350]` keeps the computed immediate
inside `[1, 4095]`.  Stated over the offset's window so every configured
offset check (`addr_offset_ok`, `hw_offset_ok`, `byte_offset_ok`) can supply
it. -/
theorem arm8FarImm_encodable_of_bounds (off : BitVec 64)
    (hlo : (-4351 : Int) ≤ off.toInt) (hhi : off.toInt ≤ 4350)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))) :
    (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)) &&&
      ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  have hout : ¬((-256 : Int) ≤ off.toInt ∧ off.toInt ≤ 255) := by
    intro ⟨h1, h2⟩
    exact hnsx (arm8NineBitForm_of_range off h1 h2)
  by_cases hmsb : off.msb
  · have hcond := BitVec.toInt_eq_msb_cond off
    rw [hmsb] at hcond
    simp only [ite_true] at hcond
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
    simp only [hmsb, Bool.not_true, Bool.false_eq_true, ite_false]
    exact arm8AndNot_eq_zero_of_toNat_lt _ hsmall
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    have hcond := BitVec.toInt_eq_msb_cond off
    rw [hmsbf] at hcond
    simp only [Bool.false_eq_true, ite_false] at hcond
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
    simp only [hmsbf, Bool.not_false, ite_true]
    exact arm8AndNot_eq_zero_of_toNat_lt _ hsmall

/-- The configured `addr_offset_ok` window supplies the far-immediate bounds. -/
theorem arm8FarImm_encodable (off : BitVec 64)
    (hok : asmAddrOffsetOkExact arm8ConfigL3 off = true)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat))) :
    (if !off.msb then off - (0xFF : BitVec 64) else -off - (0x100 : BitVec 64)) &&&
      ~~~(4095 : BitVec 64) = (0 : BitVec 64) := by
  obtain ⟨hlo, hhi⟩ := arm8FarOffsetBounds off hok
  exact arm8FarImm_encodable_of_bounds off hlo hhi hnsx


/-! ## The shared `Mem` tail

HOL proves every `Mem` branch of `arm8_encoder_correct` with one tactic tail
after its case split on the constructor and the offset form; only the number of
emitted instructions (`next_tac 0` or `next_tac 1`) and the per-width memory
rewrites differ.  The lemmas below are that tail: `arm8MemCaseOne` and
`arm8MemCaseTwo` simulate a one- or two-instruction lowering for any memory
effect, `arm8MemLoadCase*`/`arm8MemStoreCase*` instantiate them for a
`2 ^ size`-byte load or store, and `arm8RunLoad_*`/`arm8RunStore_*` are the
per-width `Run` facts.
-/

/-- Scratch register 26 is distinct from every allocatable register
(Flapjack infrastructure). -/
theorem arm8Reg26_ne {k : Nat} (hk : k < 32)
    (hav : arm8ConfigL3.avoidRegs.contains k = false) :
    ¬ ((26 : BitVec 5) = BitVec.ofNat 5 k) := by
  intro hh
  have hk26 : k = 26 := ((arm8Reg_eq (a := 26) (by omega) hk).mp hh).symm
  rw [hk26] at hav
  simp [arm8ConfigL3] at hav

/-- `asmUpd` of a `Mem` instruction sets the PC to the given address
(Flapjack infrastructure). -/
theorem arm8AsmUpdMem_pc (op : HolMemop) (dest base : Nat) (off p : BitVec 64)
    (s : AsmState 64) :
    (asmUpd (.inst (.mem op dest (.addr base off))) p s).pc = p := by
  cases op <;> rfl

/-- The shared tail of every two-instruction `Mem` lowering of
`encoder_correct arm8TargetL3` (Flapjack infrastructure, the counterpart of
the single tactic tail that HOL's `arm8_encoder_correct` applies to every
`Mem` branch).  `arm8_load_store_ast` emits an `AddSubImmediate@64` that puts
`regs base ± b` in scratch register 26, followed by a `LoadStoreImmediate`
`i2` that decodes to `i2d`.  The width and the direction of the memory access
enter only through `hrun2`, which describes `i2d` by its register effect
`regF` and memory effect `memF`, and through the source-side facts about
`s2`. -/
theorem arm8MemCaseTwo (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hbase : base < 32 ∧ arm8ConfigL3.avoidRegs.contains base = false ∧ base ≠ 31)
    (hdest : dest < 32 ∧ arm8ConfigL3.avoidRegs.contains dest = false)
    (sub : Bool) (b : BitVec 64) (hlow : b &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64))
    (i2 i2d : instruction) (w2 : BitVec 32)
    (regF : (BitVec 5 → BitVec 64) → BitVec 5 → BitVec 64)
    (memF : (BitVec 64 → BitVec 8) → BitVec 64 → BitVec 8)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, sub, false, b, BitVec.ofNat 5 base, 26))) ++
        arm8Encode i2)
    (hencw2 : Encode i2 = MachineCode.ARM8 w2) (hdec2 : Decode w2 = i2d)
    (hrun2 : ∀ st : arm8_state, st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      X (TN := 64) (26 : BitVec 5) st = (if sub then s1.regs base - b else s1.regs base + b) →
      (∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false →
        st.REG (BitVec.ofNat 5 k) = s1.regs k) →
      (∀ a, s1.memDomain a → st.MEM a = s1.mem a) →
      Run i2d st = { st with REG := regF st.REG, MEM := memF st.MEM })
    (hregF : ∀ R k, k < 32 → k ≠ dest → regF R (BitVec.ofNat 5 k) = R (BitVec.ofNat 5 k))
    (hregFd : ∀ R, R (BitVec.ofNat 5 dest) = s1.regs dest →
      regF R (BitVec.ofNat 5 dest) = s2.regs dest)
    (hmemIn : ∀ m : BitVec 64 → BitVec 8, (∀ a, s1.memDomain a → m a = s1.mem a) →
      ∀ a, s1.memDomain a → memF m a = s2.mem a)
    (hmemOut : ∀ m a, ¬ s1.memDomain a → memF m a = m a)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, k ≠ dest → s2.regs k = s1.regs k) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hr0 := hr
  obtain ⟨hok, hpc, hmem, hreg, _hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  obtain ⟨hslt, hsav, hs31⟩ := hbase
  obtain ⟨hdlt, hdav⟩ := hdest
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hlen : (arm8Enc (.inst (.mem op dest (.addr base off)))).length = 8 := by
    rw [henc, List.length_append, arm8Encode_length, arm8Encode_length]
  -- The two machine words in memory.
  have hencw1 := arm8Encode_addSubImmediate_low sub b (BitVec.ofNat 5 base) 26 hlow
  have hdec1 := arm8Decode_addSubImmediate_low sub b (BitVec.ofNat 5 base) 26 hlow
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem op dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  have hbyte (j : Nat) (hj : j < 8) :
      ms.MEM (ms.PC + BitVec.ofNat 64 j) =
        (arm8Encode (.Data (.«AddSubImmediate@64» (1, sub, false, b, BitVec.ofNat 5 base, 26))) ++
          arm8Encode i2).getD j 0 := by
    rw [← henc]
    exact bytesInMemoryHOL_get hbms j (by rw [hlen]; exact hj)
  obtain ⟨h0, h1, h2, h3⟩ := arm8WordBytes ms.MEM ms.PC _ _ hencw1 (fun k hk => by
    rw [hbyte k (by omega), List.getD_append _ _ _ _ (by rw [arm8Encode_length]; exact hk)])
  have hbyte2 (k : Nat) (hk : k < 4) :
      ms.MEM (ms.PC + 4 + BitVec.ofNat 64 k) = (arm8Encode i2).getD k 0 ∧
        s1.memDomain (ms.PC + 4 + BitVec.ofNat 64 k) := by
    have hidx : ms.PC + 4 + BitVec.ofNat 64 k = ms.PC + BitVec.ofNat 64 (4 + k) := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [hidx, hbyte (4 + k) (by omega), List.getD_append_right _ _ _ _
      (by rw [arm8Encode_length]; omega)]
    refine ⟨?_, ?_⟩
    · rw [arm8Encode_length]
      congr 1
      omega
    · rw [hpc]
      exact hbdom (4 + k) (by rw [hlen]; omega)
  -- First step: the scratch-register `AddSubImmediate@64`.
  have hbne : BitVec.ofNat 5 base ≠ (31 : BitVec 5) := arm8Reg_ne31 hs31 hslt
  have hXb : X (TN := 64) (BitVec.ofNat 5 base) { ms with branch_hint := none } =
      s1.regs base := by
    rw [arm8X_of_valid _ hs31 hslt]
    exact hreg base ⟨hslt, hsav⟩
  set a26 : BitVec 64 := (if sub then s1.regs base - b else s1.regs base + b) with ha26
  have hrun1 : Run (.Data (.«AddSubImmediate@64» (1, sub, false, b, BitVec.ofNat 5 base, 26)))
      { ms with branch_hint := none } =
      { ms with branch_hint := none, REG := holUpdate (26 : BitVec 5) a26 ms.REG } := by
    rw [arm8Run_addSubImmediate _ _ _ _ _ hbne (by decide)]
    simp only [hXb]
    show «write'X» (TN := 64) (a26, BitVec.ofNat 5 26) { ms with branch_hint := none } = _
    rw [arm8WriteX_of_valid _ _ (by decide) (by decide)]
    rfl
  have hn1 := arm8Next_word ms _ _ hdec1 (by rw [hrun1]) (by rw [hrun1]; exact hexc0)
    h0 h1 h2 h3 hal he0 hel
  set t1 : arm8_state := { ms with
    branch_hint := none,
    REG := holUpdate (26 : BitVec 5) a26 ms.REG,
    PC := ms.PC + 4 } with ht1
  have hnext1 : arm8Next ms = t1 := by
    rw [ht1]
    unfold arm8Next
    rw [hn1, hrun1]
    rfl
  have ht1reg : ∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false →
      t1.REG (BitVec.ofNat 5 k) = s1.regs k := by
    intro k hk hav
    show holUpdate (26 : BitVec 5) a26 ms.REG (BitVec.ofNat 5 k) = s1.regs k
    rw [holUpdate_ne (arm8Reg26_ne hk hav)]
    exact hreg k ⟨hk, hav⟩
  -- Second step: the memory instruction, on any state agreeing with `t1`.
  set t2 : arm8_state := { t1 with
    branch_hint := none,
    REG := regF t1.REG,
    MEM := memF t1.MEM,
    PC := ms.PC + 8 } with ht2
  have hagreeMem : ∀ u : arm8_state, Arm8L3Agree s1.memDomain u t1 →
      ∀ a, s1.memDomain a → u.MEM a = s1.mem a := by
    intro u hu a ha
    rw [hu.mem a ha]
    exact hmem a ha
  have hnext2_eq : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      arm8Next u = { u with
        branch_hint := none,
        REG := regF u.REG,
        MEM := memF u.MEM,
        PC := u.PC + 4 } := by
    intro u hu
    have hupc : u.PC = ms.PC + 4 := hu.pc
    have hwb (k : Nat) (hk : k < 4) :
        u.MEM (u.PC + BitVec.ofNat 64 k) = (arm8Encode i2).getD k 0 := by
      obtain ⟨hv, hd⟩ := hbyte2 k hk
      rw [hupc, hu.mem _ hd]
      exact hv
    obtain ⟨hu0, hu1, hu2, hu3⟩ := arm8WordBytes u.MEM u.PC i2 w2 hencw2 hwb
    have h4' : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    have hal4h : holAligned 2 (ms.PC + 4) = true := by
      rw [(alignedAddSub 2 ms.PC 4 h4').1, halign]
    have hal4 : Aligned (TN := 64) (u.PC, 4) = true := by
      rw [hupc, Aligned_four_iff]
      simpa using (holAligned_iff 2 (ms.PC + 4)).mp hal4h
    have he0u : u.SCTLR_EL1.E0E = false := by rw [hu.sctlr]; exact he0
    have helu : u.PSTATE.EL = (0 : BitVec 2) := by rw [hu.pstate]; exact hel
    have hrun2' := hrun2 { u with branch_hint := none } he0u helu
      (by
        show X (TN := 64) (BitVec.ofNat 5 26) u = a26
        rw [arm8X_of_valid u (by decide) (by decide), hu.reg]
        exact holUpdate_same (26 : BitVec 5) a26 ms.REG)
      (fun k hk hav => by
        show u.REG (BitVec.ofNat 5 k) = s1.regs k
        rw [hu.reg]
        exact ht1reg k hk hav)
      (fun a ha => hagreeMem u hu a ha)
    have hn2 := arm8Next_word u w2 i2d hdec2 (by rw [hrun2'])
      (by rw [hrun2']; show u.exception = _; rw [hu.exc]; exact hexc0)
      hu0 hu1 hu2 hu3 hal4 he0u helu
    unfold arm8Next
    rw [hn2, hrun2']
    rfl
  have hnext2 : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      Arm8L3Agree s1.memDomain (arm8Next u) t2 := by
    intro u hu
    rw [hnext2_eq u hu]
    refine ⟨?_, ?_, hu.pstate, hu.sctlr, hu.tcr, hu.exc, ?_⟩
    · show u.PC + 4 = ms.PC + 8
      rw [hu.pc]
      show ms.PC + 4 + 4 = ms.PC + 8
      bv_omega
    · show regF u.REG = regF t1.REG
      rw [hu.reg]
    · intro a ha
      show memF u.MEM a = memF t1.MEM a
      rw [hmemIn _ (hagreeMem u hu) a ha,
        hmemIn _ (hagreeMem t1 (Arm8L3Agree.refl _ _)) a ha]
  have hnext2_out : ∀ (u : arm8_state), Arm8L3Agree s1.memDomain u t1 →
      ∀ x, ¬ s1.memDomain x → (arm8Next u).MEM x = u.MEM x := by
    intro u hu x hx
    rw [hnext2_eq u hu]
    exact hmemOut _ x hx
  have hokPc : ∀ t : arm8_state, ∀ n : BitVec 64, holAligned 2 n = true →
      t.PSTATE = ms.PSTATE → t.SCTLR_EL1 = ms.SCTLR_EL1 → t.TCR_EL1 = ms.TCR_EL1 →
      t.exception = ms.exception → t.PC = ms.PC + n → arm8Ok t = true := by
    intro t n hn hp hsc htc hex htpc
    rw [arm8Ok_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hp]; exact hel
    · rw [hsc]; exact he0
    · rw [hsc]; exact hsa0
    · rw [htc]; exact htbi1
    · rw [htc]; exact htbi0
    · rw [hex]; exact hexc0
    · rw [htpc, (alignedAddSub 2 ms.PC n hn).1, halign]
  have h4a : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
  have h8a : holAligned 2 (8 : BitVec 64) = true := by rw [holAligned_iff]; decide
  have hupd8 : asmUpd (.inst (.mem op dest (.addr base off))) (s1.pc + BitVec.ofNat 64 8) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 8 := by
    rw [← hupd8]
    exact arm8AsmUpdMem_pc _ _ _ _ _ _
  refine asmCaseTwoMem (.mem op dest (.addr base off)) dest (s2.regs dest) t1 t2 s1 s2 ms
    ⟨hs, hr0⟩ hnext1 hnext2 hnext2_out hlen
    (hokPc t1 4 h4a rfl rfl rfl rfl rfl) rfl (fun _ _ => rfl) (fun _ _ => rfl)
    (hokPc t2 8 h8a rfl rfl rfl rfl rfl) rfl ?_ ?_ ?_ hs2pc hs2dom ?_
  · intro x hx
    exact hmemIn _ (fun a ha => hmem a ha) x hx
  · intro k hk hav hkd
    show regF t1.REG (BitVec.ofNat 5 k) = ms.REG (BitVec.ofNat 5 k)
    rw [hregF _ k hk hkd]
    show holUpdate (26 : BitVec 5) a26 ms.REG (BitVec.ofNat 5 k) = _
    rw [holUpdate_ne (arm8Reg26_ne hk hav)]
  · exact hregFd _ (ht1reg dest hdlt hdav)
  · intro k
    by_cases hk : k = dest
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk, hs2regs k hk]

/-- The shared tail of every one-instruction `Mem` lowering of
`encoder_correct arm8TargetL3` (Flapjack infrastructure, the one-instruction
counterpart of `arm8MemCaseTwo`): a single `LoadStoreImmediate` `i`, decoding
to `id`, addressed from `regs base`. -/
theorem arm8MemCaseOne (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hbase : base < 32 ∧ arm8ConfigL3.avoidRegs.contains base = false ∧ base ≠ 31)
    (hdest : dest < 32 ∧ arm8ConfigL3.avoidRegs.contains dest = false)
    (i id : instruction) (w : BitVec 32)
    (regF : (BitVec 5 → BitVec 64) → BitVec 5 → BitVec 64)
    (memF : (BitVec 64 → BitVec 8) → BitVec 64 → BitVec 8)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) = arm8Encode i)
    (hencw : Encode i = MachineCode.ARM8 w) (hdec : Decode w = id)
    (hrun : ∀ st : arm8_state, st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      X (TN := 64) (BitVec.ofNat 5 base) st = s1.regs base →
      (∀ k, k < 32 → arm8ConfigL3.avoidRegs.contains k = false →
        st.REG (BitVec.ofNat 5 k) = s1.regs k) →
      (∀ a, s1.memDomain a → st.MEM a = s1.mem a) →
      Run id st = { st with REG := regF st.REG, MEM := memF st.MEM })
    (hregF : ∀ R k, k < 32 → k ≠ dest → regF R (BitVec.ofNat 5 k) = R (BitVec.ofNat 5 k))
    (hregFd : ∀ R, R (BitVec.ofNat 5 dest) = s1.regs dest →
      regF R (BitVec.ofNat 5 dest) = s2.regs dest)
    (hmemIn : ∀ m : BitVec 64 → BitVec 8, (∀ a, s1.memDomain a → m a = s1.mem a) →
      ∀ a, s1.memDomain a → memF m a = s2.mem a)
    (hmemOut : ∀ m a, ¬ s1.memDomain a → memF m a = m a)
    (hs2dom : s2.memDomain = s1.memDomain)
    (hs2regs : ∀ k, k ≠ dest → s2.regs k = s1.regs k) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  obtain ⟨hs, hr⟩ := h
  have hr0 := hr
  obtain ⟨hok, hpc, hmem, hreg, _hfp⟩ := hr
  rw [arm8TargetL3_stateOk] at hok
  rw [arm8TargetL3_getPc] at hpc
  rw [arm8TargetL3_getByte] at hmem
  rw [arm8TargetL3_getReg] at hreg
  change ms.PC = s1.pc at hpc
  change ∀ a, s1.memDomain a → ms.MEM a = s1.mem a at hmem
  change ∀ k, k < arm8ConfigL3.regCount ∧ arm8ConfigL3.avoidRegs.contains k = false →
    ms.REG (BitVec.ofNat 5 k) = s1.regs k at hreg
  obtain ⟨hslt, hsav, hs31⟩ := hbase
  obtain ⟨hdlt, hdav⟩ := hdest
  obtain ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, halign⟩ := (arm8Ok_iff ms).mp hok
  have hal : Aligned (TN := 64) (ms.PC, 4) = true := by
    rw [Aligned_four_iff]
    simpa using (holAligned_iff 2 ms.PC).mp halign
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hlen : (arm8Enc (.inst (.mem op dest (.addr base off)))).length = 4 := by
    rw [henc, arm8Encode_length]
  have hbcode := hs.1
  simp only [arm8ConfigL3] at hbcode
  have hbdom := bytesInMemoryHOL_domain hbcode
  have hbms : bytesInMemoryHOL ms.PC (arm8Enc (.inst (.mem op dest (.addr base off))))
      ms.MEM s1.memDomain := by
    rw [hpc]
    exact bytesInMemory_changeMem _ _ _ _ _ ⟨hbcode, fun n hn => (hmem _ (hbdom n hn)).symm⟩
  obtain ⟨h0, h1, h2, h3⟩ := arm8WordBytes ms.MEM ms.PC i w hencw (fun k hk => by
    rw [← henc]
    exact bytesInMemoryHOL_get hbms k (by rw [hlen]; exact hk))
  have hrun' := hrun { ms with branch_hint := none } he0 hel
    (by rw [arm8X_of_valid _ hs31 hslt]; exact hreg base ⟨hslt, hsav⟩)
    (fun k hk hav => hreg k ⟨hk, hav⟩) hmem
  have hn := arm8Next_word ms w id hdec (by rw [hrun']) (by rw [hrun']; exact hexc0)
    h0 h1 h2 h3 hal he0 hel
  have hnext : arm8Next ms = { ms with
      branch_hint := none,
      REG := regF ms.REG,
      MEM := memF ms.MEM,
      PC := ms.PC + 4 } := by
    unfold arm8Next
    rw [hn, hrun']
    rfl
  have hupd4 : asmUpd (.inst (.mem op dest (.addr base off))) (s1.pc + BitVec.ofNat 64 4) s1 =
      s2 := by
    rw [← hupd, hlen]
  have hs2pc : s2.pc = s1.pc + BitVec.ofNat 64 4 := by
    rw [← hupd4]
    exact arm8AsmUpdMem_pc _ _ _ _ _ _
  refine asmCaseOneMem (.mem op dest (.addr base off)) dest (s2.regs dest) _ s1 s2 ms
    ⟨hs, hr0⟩ hnext rfl (hmemIn _ hmem) (hmemOut _) (fun k hk hkd => hregF _ k hk hkd)
    (hregFd _ (hreg dest ⟨hdlt, hdav⟩)) ?_ hs2pc hs2dom ?_
  · have h4 : holAligned 2 (4 : BitVec 64) = true := by rw [holAligned_iff]; decide
    rw [arm8Ok_iff]
    refine ⟨hel, he0, hsa0, htbi1, htbi0, hexc0, ?_⟩
    change holAligned 2 (ms.PC + 4) = true
    rw [(alignedAddSub 2 ms.PC 4 h4).1, halign]
  · intro k
    by_cases hk : k = dest
    · rw [ite_eq_left hk, hk]
    · rw [ite_eq_right hk, hs2regs k hk]

/-- The register side conditions of a `Mem` instruction accepted by
`asm_ok` (Flapjack infrastructure; any `memop`). -/
theorem arm8MemRegsOk (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (h : asmOkExact (.inst (.mem op dest (.addr base off))) arm8ConfigL3 = true) :
    (base < 32 ∧ arm8ConfigL3.avoidRegs.contains base = false ∧ base ≠ 31) ∧
      (dest < 32 ∧ arm8ConfigL3.avoidRegs.contains dest = false ∧ dest ≠ 31) := by
  have h' := h
  simp only [asmOkExact, asmInstOkExact, Bool.and_eq_true] at h'
  exact ⟨regOk_of_asmL3 h'.1.2, regOk_of_asmL3 h'.1.1⟩

/-- A successful `2 ^ size`-byte load is aligned and has its bytes in the
source memory domain (Flapjack infrastructure, gathering the per-size
`arm8MemLoad_aligned*` and `arm8MemLoad_domain*` facts). -/
theorem arm8MemLoad_alignedDomain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64) (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true ∧
      ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  interval_cases size
  · exact ⟨arm8MemLoad_aligned_one op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemLoad_domain_one op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemLoad_aligned_two op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemLoad_domain_two op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemLoad_aligned_four op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemLoad_domain_four op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemLoad_aligned op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemLoad_domain op r base off s1 s2 pc hspec hupd hbe hok⟩

/-- The store counterpart of `arm8MemLoad_alignedDomain` (Flapjack
infrastructure). -/
theorem arm8MemStore_alignedDomain (op : HolMemop) (r base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64) (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (hupd : asmUpd (.inst (.mem op r (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) (hok : ¬ s2.failed) :
    Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true ∧
      ∀ k, k < 2 ^ size → s1.memDomain (s1.regs base + off + BitVec.ofNat 64 k) := by
  interval_cases size
  · exact ⟨arm8MemStore_aligned_one op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemStore_domain_one op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemStore_aligned_two op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemStore_domain_two op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemStore_aligned_four op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemStore_domain_four op r base off s1 s2 pc hspec hupd hbe hok⟩
  · exact ⟨arm8MemStore_aligned op r base off s1 s2 pc hspec hupd hbe hok,
      arm8MemStore_domain op r base off s1 s2 pc hspec hupd hbe hok⟩

/-- The source state after an `n`-byte load (Flapjack infrastructure). -/
theorem arm8MemLoadPost (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64) (n : Nat)
    (hspec : memOp (width := 64) op = memLoad (width := 64) n)
    (hupd : asmUpd (.inst (.mem op dest (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) :
    s2.memDomain = s1.memDomain ∧ (∀ x, s2.mem x = s1.mem x) ∧
      ∀ k, s2.regs k = if k = dest then
        (readMemWord (resultWidth := 64) (s1.regs base + off) n s1).1 else s1.regs k := by
  subst hupd
  refine ⟨?_, ?_, ?_⟩
  · simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_memDomain]
  · intro x
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_mem_eq_direct]
  · intro k
    simp only [asmUpd, instUpd, hspec, memLoad, addrHOL, updPc, updReg, assertState,
      readMemWord_regs, Flapjack.Compiler.Encoders.AsmSem.readReg, hbe,
      Bool.false_eq_true, ite_false]

/-- The source state after an `n`-byte store (Flapjack infrastructure). -/
theorem arm8MemStorePost (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (pc : BitVec 64) (n : Nat)
    (hspec : memOp (width := 64) op = memStore (width := 64) n)
    (hupd : asmUpd (.inst (.mem op dest (.addr base off))) pc s1 = s2)
    (hbe : s1.be = false) :
    s2.memDomain = s1.memDomain ∧ (∀ k, s2.regs k = s1.regs k) ∧
      ∀ x, s2.mem x =
        (writeMemWord (valueWidth := 64) (s1.regs base + off) n (s1.regs dest) s1).mem x := by
  subst hupd
  refine ⟨?_, ?_, ?_⟩
  · simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_memDomain]
  · intro k
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      writeMemWord_regs]
  · intro x
    simp only [asmUpd, instUpd, hspec, memStore, addrHOL, updPc, assertState,
      Flapjack.Compiler.Encoders.AsmSem.readReg, hbe, Bool.false_eq_true, ite_false]

/-- A `2 ^ size`-byte `writeMemBytes` leaves every other address alone
(Flapjack infrastructure). -/
theorem arm8WriteMemN_out (m : BitVec 64 → BitVec 8) (size : Nat) (hsize : size < 4)
    (a v x : BitVec 64) (hx : ∀ k, k < 2 ^ size → x ≠ a + BitVec.ofNat 64 k) :
    writeMemBytes m (2 ^ size) a v x = m x := by
  have h0 : x ≠ a := by simpa using hx 0 (by positivity)
  interval_cases size
  · simp [writeMemBytes, h0]
  · have h1 : x ≠ a + 1#64 := by simpa using hx 1 (by omega)
    simp [writeMemBytes, h0, h1]
  · have h1 : x ≠ a + 1#64 := by simpa using hx 1 (by omega)
    have h2 : x ≠ a + 2#64 := by simpa using hx 2 (by omega)
    have h3 : x ≠ a + 3#64 := by simpa using hx 3 (by omega)
    simp [writeMemBytes, h0, h1, h2, h3]
  · have h1 : x ≠ a + 1#64 := by simpa using hx 1 (by omega)
    have h2 : x ≠ a + 2#64 := by simpa using hx 2 (by omega)
    have h3 : x ≠ a + 3#64 := by simpa using hx 3 (by omega)
    have h4 : x ≠ a + 4#64 := by simpa using hx 4 (by omega)
    have h5 : x ≠ a + 5#64 := by simpa using hx 5 (by omega)
    have h6 : x ≠ a + 6#64 := by simpa using hx 6 (by omega)
    have h7 : x ≠ a + 7#64 := by simpa using hx 7 (by omega)
    simp [writeMemBytes, h0, h1, h2, h3, h4, h5, h6, h7]

/-- The one-instruction `Mem` load of `2 ^ size` bytes (Flapjack
infrastructure): `arm8MemCaseOne` with the load's register and memory
effects, the source-side facts derived from the `asmStep`, and the machine
instruction's `Run` equation (`hrun`) left to the per-width lemma. -/
theorem arm8MemLoadCaseOne (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (i id : instruction) (w : BitVec 32)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) = arm8Encode i)
    (hencw : Encode i = MachineCode.ARM8 w) (hdec : Decode w = id)
    (hrun : ∀ st : arm8_state, dest < 32 → dest ≠ 31 → s1.be = false →
      Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true →
      st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false →
      X (TN := 64) (BitVec.ofNat 5 base) st = s1.regs base →
      (∀ i, i < 2 ^ size → st.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
        s1.mem (s1.regs base + off + BitVec.ofNat 64 i)) →
      Run id st = { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ size) s1).1 st.REG }) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  have hs := h.1
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnf : ¬ s2.failed := hs.2.2.2.2.2.1
  obtain ⟨hbase, hdest⟩ := arm8MemRegsOk op dest base off hs.2.2.2.2.2.2
  have hrn : (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    exact arm8Reg_ne31 hbase.2.2 hbase.1 (beq_iff_eq.mp hh)
  obtain ⟨hal, hdom⟩ :=
    arm8MemLoad_alignedDomain op dest base off s1 s2 _ size hsize hspec hupd hbe hnf
  obtain ⟨hs2dom, hs2mem, hs2regs⟩ := arm8MemLoadPost op dest base off s1 s2 _ _ hspec hupd hbe
  refine arm8MemCaseOne op dest base off s1 s2 ms h ⟨hbase.1, hbase.2.1, hbase.2.2⟩
    ⟨hdest.1, hdest.2.1⟩ i id w
    (fun R => holUpdate (BitVec.ofNat 5 dest)
      (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ size) s1).1 R) (fun m => m)
    henc hencw hdec ?_ ?_ ?_ ?_ (fun _ _ _ => rfl) hs2dom ?_
  · intro st he0 hel hX _ hm
    exact hrun st hdest.1 hdest.2.2 hbe hal he0 hel hrn hX (fun i hi => hm _ (hdom i hi))
  · intro R k hk hkd
    exact holUpdate_ne (fun hh => hkd ((arm8Reg_eq hdest.1 hk).mp hh).symm) _ _
  · intro R _
    rw [holUpdate_same, hs2regs dest, ite_eq_left rfl]
  · intro m hm a ha
    rw [hs2mem a]
    exact hm a ha
  · intro k hk
    rw [hs2regs k, ite_eq_right hk]

/-- The two-instruction (far-offset) `Mem` load of `2 ^ size` bytes (Flapjack
infrastructure): `arm8MemCaseTwo` with the load's register and memory
effects, the source-side facts derived from the `asmStep`, and the machine
instruction's `Run` equation (`hrun2`) left to the per-width lemma. -/
theorem arm8MemLoadCaseTwo (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memLoad (width := 64) (2 ^ size))
    (sub : Bool) (b : BitVec 64) (hlow : b &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64))
    (i2 i2d : instruction) (w2 : BitVec 32)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, sub, false, b, BitVec.ofNat 5 base, 26))) ++
        arm8Encode i2)
    (hencw2 : Encode i2 = MachineCode.ARM8 w2) (hdec2 : Decode w2 = i2d)
    (hrun2 : ∀ st : arm8_state, dest < 32 → dest ≠ 31 → s1.be = false →
      Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true →
      st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      ((26 : BitVec 5) == BitVec.ofNat 5 31) = false →
      X (TN := 64) (26 : BitVec 5) st = (if sub then s1.regs base - b else s1.regs base + b) →
      (∀ i, i < 2 ^ size → st.MEM (s1.regs base + off + BitVec.ofNat 64 i) =
        s1.mem (s1.regs base + off + BitVec.ofNat 64 i)) →
      Run i2d st = { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ size) s1).1 st.REG }) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  have hs := h.1
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnf : ¬ s2.failed := hs.2.2.2.2.2.1
  obtain ⟨hbase, hdest⟩ := arm8MemRegsOk op dest base off hs.2.2.2.2.2.2
  have hrn : (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    exact arm8Reg_ne31 hbase.2.2 hbase.1 (beq_iff_eq.mp hh)
  obtain ⟨hal, hdom⟩ :=
    arm8MemLoad_alignedDomain op dest base off s1 s2 _ size hsize hspec hupd hbe hnf
  obtain ⟨hs2dom, hs2mem, hs2regs⟩ := arm8MemLoadPost op dest base off s1 s2 _ _ hspec hupd hbe
  refine arm8MemCaseTwo op dest base off s1 s2 ms h ⟨hbase.1, hbase.2.1, hbase.2.2⟩
    ⟨hdest.1, hdest.2.1⟩ sub b hlow i2 i2d w2
    (fun R => holUpdate (BitVec.ofNat 5 dest)
      (readMemWord (resultWidth := 64) (s1.regs base + off) (2 ^ size) s1).1 R) (fun m => m)
    henc hencw2 hdec2 ?_ ?_ ?_ ?_ (fun _ _ _ => rfl) hs2dom ?_
  · intro st he0 hel hX _ hm
    exact hrun2 st hdest.1 hdest.2.2 hbe hal he0 hel (by decide) hX (fun i hi => hm _ (hdom i hi))
  · intro R k hk hkd
    exact holUpdate_ne (fun hh => hkd ((arm8Reg_eq hdest.1 hk).mp hh).symm) _ _
  · intro R _
    rw [holUpdate_same, hs2regs dest, ite_eq_left rfl]
  · intro m hm a ha
    rw [hs2mem a]
    exact hm a ha
  · intro k hk
    rw [hs2regs k, ite_eq_right hk]

/-- The one-instruction `Mem` store of `2 ^ size` bytes (Flapjack
infrastructure): `arm8MemCaseOne` with the store's register and memory
effects, the source-side facts derived from the `asmStep`, and the machine
instruction's `Run` equation (`hrun`) left to the per-width lemma. -/
theorem arm8MemStoreCaseOne (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (i id : instruction) (w : BitVec 32)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) = arm8Encode i)
    (hencw : Encode i = MachineCode.ARM8 w) (hdec : Decode w = id)
    (hrun : ∀ st : arm8_state, dest < 32 → dest ≠ 31 → s1.be = false →
      Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true →
      st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false →
      X (TN := 64) (BitVec.ofNat 5 base) st = s1.regs base →
      st.REG (BitVec.ofNat 5 dest) = s1.regs dest →
      Run id st = { st with
        MEM := writeMemBytes st.MEM (2 ^ size) (s1.regs base + off) (s1.regs dest) }) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  have hs := h.1
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnf : ¬ s2.failed := hs.2.2.2.2.2.1
  obtain ⟨hbase, hdest⟩ := arm8MemRegsOk op dest base off hs.2.2.2.2.2.2
  have hrn : (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    exact arm8Reg_ne31 hbase.2.2 hbase.1 (beq_iff_eq.mp hh)
  obtain ⟨hal, hdom⟩ :=
    arm8MemStore_alignedDomain op dest base off s1 s2 _ size hsize hspec hupd hbe hnf
  obtain ⟨hs2dom, hs2regs, hs2mem⟩ := arm8MemStorePost op dest base off s1 s2 _ _ hspec hupd hbe
  refine arm8MemCaseOne op dest base off s1 s2 ms h ⟨hbase.1, hbase.2.1, hbase.2.2⟩
    ⟨hdest.1, hdest.2.1⟩ i id w
    (fun R => R) (fun m => writeMemBytes m (2 ^ size) (s1.regs base + off) (s1.regs dest))
    henc hencw hdec ?_ (fun _ _ _ _ => rfl) ?_ ?_ ?_ hs2dom (fun k _ => hs2regs k)
  · intro st he0 hel hX hregs _
    exact hrun st hdest.1 hdest.2.2 hbe hal he0 hel hrn hX (hregs dest hdest.1 hdest.2.1)
  · intro R hR
    show R (BitVec.ofNat 5 dest) = s2.regs dest
    rw [hR, hs2regs]
  · intro m hm a ha
    rw [hs2mem a]
    exact (writeMemWord_memSize s1 m size hsize _ _ a hbe (hm a ha).symm).symm
  · intro m a ha
    exact arm8WriteMemN_out m size hsize _ _ a (fun k hk hh => ha (hh ▸ hdom k hk))

/-- The two-instruction (far-offset) `Mem` store of `2 ^ size` bytes (Flapjack
infrastructure): `arm8MemCaseTwo` with the store's register and memory
effects, the source-side facts derived from the `asmStep`, and the machine
instruction's `Run` equation (`hrun2`) left to the per-width lemma. -/
theorem arm8MemStoreCaseTwo (op : HolMemop) (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem op dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (size : Nat) (hsize : size < 4)
    (hspec : memOp (width := 64) op = memStore (width := 64) (2 ^ size))
    (sub : Bool) (b : BitVec 64) (hlow : b &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64))
    (i2 i2d : instruction) (w2 : BitVec 32)
    (henc : arm8Enc (.inst (.mem op dest (.addr base off))) =
      arm8Encode (.Data (.«AddSubImmediate@64» (1, sub, false, b, BitVec.ofNat 5 base, 26))) ++
        arm8Encode i2)
    (hencw2 : Encode i2 = MachineCode.ARM8 w2) (hdec2 : Decode w2 = i2d)
    (hrun2 : ∀ st : arm8_state, dest < 32 → dest ≠ 31 → s1.be = false →
      Aligned (TN := 64) (s1.regs base + off, 2 ^ size) = true →
      st.SCTLR_EL1.E0E = false → st.PSTATE.EL = (0 : BitVec 2) →
      ((26 : BitVec 5) == BitVec.ofNat 5 31) = false →
      X (TN := 64) (26 : BitVec 5) st = (if sub then s1.regs base - b else s1.regs base + b) →
      st.REG (BitVec.ofNat 5 dest) = s1.regs dest →
      Run i2d st = { st with
        MEM := writeMemBytes st.MEM (2 ^ size) (s1.regs base + off) (s1.regs dest) }) :
    CaseGoal (.inst (.mem op dest (.addr base off))) s1 s2 ms := by
  have hs := h.1
  have hbe : s1.be = false := hs.2.2.1
  have hupd := hs.2.2.2.2.1
  simp only [arm8ConfigL3] at hupd
  have hnf : ¬ s2.failed := hs.2.2.2.2.2.1
  obtain ⟨hbase, hdest⟩ := arm8MemRegsOk op dest base off hs.2.2.2.2.2.2
  have hrn : (BitVec.ofNat 5 base == BitVec.ofNat 5 31) = false := by
    rw [Bool.eq_false_iff]
    intro hh
    exact arm8Reg_ne31 hbase.2.2 hbase.1 (beq_iff_eq.mp hh)
  obtain ⟨hal, hdom⟩ :=
    arm8MemStore_alignedDomain op dest base off s1 s2 _ size hsize hspec hupd hbe hnf
  obtain ⟨hs2dom, hs2regs, hs2mem⟩ := arm8MemStorePost op dest base off s1 s2 _ _ hspec hupd hbe
  refine arm8MemCaseTwo op dest base off s1 s2 ms h ⟨hbase.1, hbase.2.1, hbase.2.2⟩
    ⟨hdest.1, hdest.2.1⟩ sub b hlow i2 i2d w2
    (fun R => R) (fun m => writeMemBytes m (2 ^ size) (s1.regs base + off) (s1.regs dest))
    henc hencw2 hdec2 ?_ (fun _ _ _ _ => rfl) ?_ ?_ ?_ hs2dom (fun k _ => hs2regs k)
  · intro st he0 hel hX hregs _
    exact hrun2 st hdest.1 hdest.2.2 hbe hal he0 hel (by decide) hX (hregs dest hdest.1 hdest.2.1)
  · intro R hR
    show R (BitVec.ofNat 5 dest) = s2.regs dest
    rw [hR, hs2regs]
  · intro m hm a ha
    rw [hs2mem a]
    exact (writeMemWord_memSize s1 m size hsize _ _ a hbe (hm a ha).symm).symm
  · intro m a ha
    exact arm8WriteMemN_out m size hsize _ _ a (fun k hk hh => ha (hh ▸ hdom k hk))

/-- `Run` of the 8-byte `LoadStoreImmediate` load at a register
holding `xr`, offset `c`, as the register update `arm8MemLoadCase*` expects
(Flapjack infrastructure; the per-width counterpart of HOL's `mem_*`
rewrites in the `Mem` tail of `arm8_encoder_correct`). -/
theorem arm8RunLoad_eight (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 8) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hm : ∀ i, i < 8 → st.MEM (addr + BitVec.ofNat 64 i) = s1.mem (addr + BitVec.ofNat 64 i)) :
    Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) addr 8 s1).1 st.REG } := by
  rw [arm8Run_loadStoreImmediate_load _ _ _ _ _ hrn, hX, hc,
    arm8Mem_eight_pair st s1 addr hal he0 hel hbe hm]
  simp only [BitVec.setWidth_eq]
  exact arm8WriteX_of_valid _ _ hd31 hd

/-- `Run` of the 4-byte `LoadStoreImmediate` load at a register
holding `xr`, offset `c`, as the register update `arm8MemLoadCase*` expects
(Flapjack infrastructure; the per-width counterpart of HOL's `mem_*`
rewrites in the `Mem` tail of `arm8_encoder_correct`). -/
theorem arm8RunLoad_four (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 4) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hm : ∀ i, i < 4 → st.MEM (addr + BitVec.ofNat 64 i) = s1.mem (addr + BitVec.ofNat 64 i)) :
    Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) addr 4 s1).1 st.REG } := by
  have hv := arm8Mem_four_eq_readMemWord st s1 addr hal he0 hel hbe hm
  rw [arm8Mem_four_pair st s1 addr hal he0 hel hbe hm] at hv
  rw [arm8Run_loadStoreImmediate_load32 _ _ _ _ _ hrn, hX, hc,
    arm8Mem_four_pair st s1 addr hal he0 hel hbe hm]
  simp only [BitVec.setWidth_eq]
  rw [arm8WriteX32_of_valid _ _ hd31 hd, hv]

/-- `Run` of the 2-byte `LoadStoreImmediate` load at a register
holding `xr`, offset `c`, as the register update `arm8MemLoadCase*` expects
(Flapjack infrastructure; the per-width counterpart of HOL's `mem_*`
rewrites in the `Mem` tail of `arm8_encoder_correct`). -/
theorem arm8RunLoad_two (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 2) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hm : ∀ i, i < 2 → st.MEM (addr + BitVec.ofNat 64 i) = s1.mem (addr + BitVec.ofNat 64 i)) :
    Run (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) addr 2 s1).1 st.REG } := by
  have hv := arm8Mem_two_eq_readMemWord st s1 addr hal he0 hel hbe hm
  rw [arm8Mem_two_pair st s1 addr hal he0 hel hbe hm] at hv
  rw [arm8Run_loadStoreImmediate_load16 _ _ _ _ _ hrn, hX, hc,
    arm8Mem_two_pair st s1 addr hal he0 hel hbe hm]
  dsimp only
  rw [arm8WriteX32_of_valid _ _ hd31 hd, setWidth64_setWidth32_of_16, hv]

/-- `Run` of the 1-byte `LoadStoreImmediate` load at a register
holding `xr`, offset `c`, as the register update `arm8MemLoadCase*` expects
(Flapjack infrastructure; the per-width counterpart of HOL's `mem_*`
rewrites in the `Mem` tail of `arm8_encoder_correct`). -/
theorem arm8RunLoad_one (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 1) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hm : ∀ i, i < 1 → st.MEM (addr + BitVec.ofNat 64 i) = s1.mem (addr + BitVec.ofNat 64 i)) :
    Run (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_LOAD, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with
        REG := holUpdate (BitVec.ofNat 5 dest)
          (readMemWord (resultWidth := 64) addr 1 s1).1 st.REG } := by
  have hm0 : st.MEM addr = s1.mem addr := by simpa using hm 0 (by decide)
  have hv := arm8Mem_one_eq_readMemWord st s1 addr hal he0 hel hbe hm0
  rw [arm8Mem_one st addr hal he0 hel] at hv
  rw [arm8Run_loadStoreImmediate_load8 _ _ _ _ _ hrn, hX, hc, arm8Mem_one st addr hal he0 hel]
  rw [arm8WriteX32_of_valid _ _ hd31 hd, setWidth64_setWidth32, hv]

/-- `Run` of the 8-byte `LoadStoreImmediate` store at a register
holding `xr`, offset `c`, as the memory update `arm8MemStoreCase*` expects
(Flapjack infrastructure). -/
theorem arm8RunStore_eight (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (_hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 8) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hv : st.REG (BitVec.ofNat 5 dest) = s1.regs dest) :
    Run (.LoadStore (.«LoadStoreImmediate@64»
        (3, false, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with MEM := writeMemBytes st.MEM 8 addr (s1.regs dest) } := by
  rw [arm8Run_loadStoreImmediate_store _ _ _ _ _ hrn, hX, hc, arm8X_of_valid st hd31 hd, hv,
    arm8WriteMem_only_mem _ _ _ _ hal]
  congr 1
  funext x
  exact arm8WriteMem_eight st addr _ _ hal he0 hel x

/-- `Run` of the 4-byte `LoadStoreImmediate` store at a register
holding `xr`, offset `c`, as the memory update `arm8MemStoreCase*` expects
(Flapjack infrastructure). -/
theorem arm8RunStore_four (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (_hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 4) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hv : st.REG (BitVec.ofNat 5 dest) = s1.regs dest) :
    Run (.LoadStore (.«LoadStoreImmediate@32»
        (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with MEM := writeMemBytes st.MEM 4 addr (s1.regs dest) } := by
  rw [arm8Run_loadStoreImmediate_store32 _ _ _ _ _ hrn, hX, hc, arm8X32_of_valid st hd31 hd, hv,
    arm8WriteMem_only_mem_four _ _ _ _ hal]
  congr 1
  funext x
  rw [arm8WriteMem_four st addr _ _ hal he0 hel x, writeMemBytes_four_setWidth32]

/-- `Run` of the 2-byte `LoadStoreImmediate` store at a register
holding `xr`, offset `c`, as the memory update `arm8MemStoreCase*` expects
(Flapjack infrastructure). -/
theorem arm8RunStore_two (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (_hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 2) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hv : st.REG (BitVec.ofNat 5 dest) = s1.regs dest) :
    Run (.LoadStore (.«LoadStoreImmediate@16»
        (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with MEM := writeMemBytes st.MEM 2 addr (s1.regs dest) } := by
  rw [arm8Run_loadStoreImmediate_store16 _ _ _ _ _ hrn, hX, hc, arm8X16_of_valid st hd31 hd, hv,
    arm8WriteMem_only_mem_two _ _ _ _ hal]
  congr 1
  funext x
  rw [arm8WriteMem_two st addr _ _ hal he0 hel x, writeMemBytes_two_setWidth16]

/-- `Run` of the 1-byte `LoadStoreImmediate` store at a register
holding `xr`, offset `c`, as the memory update `arm8MemStoreCase*` expects
(Flapjack infrastructure). -/
theorem arm8RunStore_one (s1 : AsmState 64) (c : BitVec 64) (unsigned : Bool) (rn : BitVec 5)
    (dest : Nat) (xr addr : BitVec 64) (hc : xr + c = addr) (st : arm8_state)
    (hd : dest < 32) (hd31 : dest ≠ 31) (_hbe : s1.be = false)
    (hal : Aligned (TN := 64) (addr, 1) = true)
    (he0 : st.SCTLR_EL1.E0E = false) (hel : st.PSTATE.EL = (0 : BitVec 2))
    (hrn : (rn == BitVec.ofNat 5 31) = false) (hX : X (TN := 64) rn st = xr)
    (hv : st.REG (BitVec.ofNat 5 dest) = s1.regs dest) :
    Run (.LoadStore (.«LoadStoreImmediate@8»
        (BitVec.ofNat 8 0, true, .MemOp_STORE, .AccType_NORMAL, false, false, false, false, false,
         unsigned, c, rn, BitVec.ofNat 5 dest))) st =
      { st with MEM := writeMemBytes st.MEM 1 addr (s1.regs dest) } := by
  rw [arm8Run_loadStoreImmediate_store8 _ _ _ _ _ hrn, hX, hc, arm8X8_of_valid st hd31 hd, hv,
    arm8WriteMem_only_mem_one _ _ _ _ hal]
  congr 1
  funext x
  rw [arm8WriteMem_one st addr _ _ hal he0 hel x, writeMemBytes_one_setWidth8]

/-- The scaled-form branch condition of `arm8_load_store_ast*` from the
`e_LoadStoreImmediate` one (Flapjack infrastructure). -/
theorem arm8ScaledSingle (off : BitVec 64) (k : BitVec 64) (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> k))) <<< k) :
    off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat) ∨
      (!off.msb &&
        (off == (BitVec.zeroExtend 64 (BitVec.ofNat 12 ((off >>> k).toNat))) <<< k)) = true := by
  right
  rw [hmsb, Bool.not_false, Bool.true_and, beq_iff_eq, arm8ScaledForm_eq off k]
  exact hoff

/-! ## The `Mem` case theorems

One theorem per constructor and offset branch of HOL's `Mem` case split; each
one applies the shared tail above.
-/

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
  refine arm8MemLoadCaseOne .load32 dest base off s1 s2 ms h 2 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single32 dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_load32 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunLoad_four s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store32 dest base off s1 s2 ms h 2 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single32 dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_store32 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunStore_four s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemLoadCaseOne .load32 dest base off s1 s2 ms h 2 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single_of_single32 dest base off
      (arm8ScaledSingle off 2 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_load32 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_load32 (holWordExtract 12 11 0 (off >>> 2))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunLoad_four s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store32 dest base off s1 s2 ms h 2 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single_of_single32 dest base off
      (arm8ScaledSingle off 2 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_store32 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_store32 (holWordExtract 12 11 0 (off >>> 2))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunStore_four s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemLoadCaseOne .load8 dest base off s1 s2 ms h 0 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@8» (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single8 dest base off]; simp)
    (arm8Encode_loadStoreImm9_load8 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_load8 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunLoad_one s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store8 dest base off s1 s2 ms h 0 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@8» (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single8 dest base off]; simp)
    (arm8Encode_loadStoreImm9_store8 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_store8 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunStore_one s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemLoadCaseOne .load8 dest base off s1 s2 ms h 0 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@8» (BitVec.ofNat 8 0, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single8 dest base off]; simp [hmsb])
    (arm8Encode_loadStoreImm12_load8 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_load8 (holWordExtract 12 11 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunLoad_one s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store8 dest base off s1 s2 ms h 0 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@8» (BitVec.ofNat 8 0, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single8 dest base off]; simp [hmsb])
    (arm8Encode_loadStoreImm12_store8 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_store8 (holWordExtract 12 11 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunStore_one s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemLoadCaseOne .load16 dest base off s1 s2 ms h 1 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single16 dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_load16 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_load16 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunLoad_two s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store16 dest base off s1 s2 ms h 1 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single16 dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_store16 off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_store16 (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunStore_two s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemLoadCaseOne .load16 dest base off s1 s2 ms h 1 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single_of_single16 dest base off
      (arm8ScaledSingle off 1 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_load16 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_load16 (holWordExtract 12 11 0 (off >>> 1))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunLoad_two s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store16 dest base off s1 s2 ms h 1 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single_of_single16 dest base off
      (arm8ScaledSingle off 1 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_store16 off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_store16 (holWordExtract 12 11 0 (off >>> 1))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunStore_two s1 _ _ _ dest _ _ rfl)

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
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load dest base off s1 s2 ms h 3 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_eight s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

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
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load32 dest base off s1 s2 ms h 2 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far32 dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load32 _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_four s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

/-- The `.mem .load16` constructor on the far-offset path with a negative
offset: the same `AddSubImmediate@64` into scratch register 26 followed by a
signed `LoadStoreImmediate@16` at `-0x100` against it, reading the two bytes
at `regs base + off`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load16_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    CaseGoal (.inst (.mem .load16 dest (.addr base off))) s1 s2 ms := by
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load16 dest base off s1 s2 ms h 1 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far16 dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load16 _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load16 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_two s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

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
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store dest base off s1 s2 ms h 3 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_eight s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

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
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store32 dest base off s1 s2 ms h 2 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far32 dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store32 _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_four s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

/-- The `.mem .store16` constructor on the far-offset path with a negative
offset: the same `AddSubImmediate@64` into scratch register 26 followed by a
signed `LoadStoreImmediate@16` at `-0x100` against it, storing the low two
bytes of `regs dest` at `regs base + off`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store16_far_neg (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = true)
    (hlow : (-off - (0x100 : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    CaseGoal (.inst (.mem .store16 dest (.addr base off))) s1 s2 ms := by
  have hsxc : (-(0x100 : BitVec 64)) = BitVec.signExtend 64 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store16 dest base off s1 s2 ms h 1 (by decide) rfl
    true (-off - 0x100) hlow
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, false, (-(0x100 : BitVec 64)), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far16 dest base off hnsx (Or.inl hmsb), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store16 _ false _ _ rfl hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store16 (holWordExtract 9 8 0 (-(0x100 : BitVec 64))) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_two s1 _ _ _ dest _ _ (by simp only [↓reduceIte]; bv_omega))

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
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load dest base off s1 s2 ms h 3 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_eight s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

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
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load32 dest base off s1 s2 ms h 2 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far32 dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load32 _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load32 (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_four s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

/-- The `.mem .load16` constructor on the far-offset path with a non-negative
offset: the same `AddSubImmediate@64` of `off - 0xFF` into scratch register 26
followed by an unsigned `LoadStoreImmediate@16` at `0xFF` against it. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load16_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat) <<< 1))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    CaseGoal (.inst (.mem .load16 dest (.addr base off))) s1 s2 ms := by
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemLoadCaseTwo .load16 dest base off s1 s2 ms h 1 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_far16 dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_load16 _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_load16 (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunLoad_two s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

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
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store dest base off s1 s2 ms h 3 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_eight s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

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
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store32 dest base off s1 s2 ms h 2 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@32» (BitVec.ofNat 32 2, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far32 dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store32 _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store32 (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_four s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

/-- The `.mem .store16` constructor on the far-offset path with a
non-negative offset: the same `off - 0xFF` / `+0xFF` pair, storing the low
two bytes of `regs dest` at `regs base + off`. -/
@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_store16_far_pos (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .store16 dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hnsx : ¬(off = BitVec.signExtend 64 (BitVec.ofNat 9 off.toNat)))
    (hmsb : off.msb = false)
    (hscaled_ne : ¬(off = BitVec.zeroExtend 64 (BitVec.ofNat 12 (off >>> 1).toNat) <<< 1))
    (hlow : (off - (0xFF : BitVec 64)) &&& ~~~(4095 : BitVec 64) = (0 : BitVec 64)) :
    CaseGoal (.inst (.mem .store16 dest (.addr base off))) s1 s2 ms := by
  have hsxc : (0xFF : BitVec 64) = BitVec.signExtend 64 (holWordExtract 9 8 0 (0xFF : BitVec 64)) := by
    rw [arm8HolWordExtract_nine]
    decide
  refine arm8MemStoreCaseTwo .store16 dest base off s1 s2 ms h 1 (by decide) rfl
    false (off - 0xFF) hlow
    (.LoadStore (.«LoadStoreImmediate@16» (BitVec.ofNat 16 1, true, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, (0xFF : BitVec 64), 26, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_far16 dest base off hnsx (Or.inr hscaled_ne), hmsb]; simp)
    (arm8Encode_loadStoreImm9_store16 _ true _ _ (by decide) hsxc)
    (by
      have hd := arm8Decode_loadStoreImm9_store16 (holWordExtract 9 8 0 (0xFF : BitVec 64)) 26
        (BitVec.ofNat 5 dest)
      rw [← hsxc] at hd
      exact hd)
    (arm8RunStore_two s1 _ _ _ dest _ _ (by simp only [Bool.false_eq_true, ↓reduceIte]; bv_omega))

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
  refine arm8MemLoadCaseOne .load dest base off s1 s2 ms h 3 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_load off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_load (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunLoad_eight s1 _ _ _ dest _ _ rfl)

@[hol "cakeml/compiler/encoders/arm8/proofs/arm8_targetProofScript.sml" "arm8_encoder_correct"]
theorem arm8_encoder_correct_mem_load_scaled (dest base : Nat) (off : BitVec 64)
    (s1 s2 : AsmState 64) (ms : arm8_state)
    (h : asmStep arm8ConfigL3 s1 (.inst (.mem .load dest (.addr base off))) s2 ∧
      targetStateRel arm8TargetL3 s1 ms)
    (hmsb : off.msb = false)
    (hoff : off = (BitVec.setWidth 64 (holWordExtract 12 11 0 (off >>> 3))) <<< 3) :
    CaseGoal (.inst (.mem .load dest (.addr base off))) s1 s2 ms := by
  refine arm8MemLoadCaseOne .load dest base off s1 s2 ms h 3 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_LOAD, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_load_single_of_single dest base off
      (arm8ScaledSingle off 3 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_load off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_load (holWordExtract 12 11 0 (off >>> 3))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunLoad_eight s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store dest base off s1 s2 ms h 3 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, !off.msb, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single dest base off hsx]; simp)
    (arm8Encode_loadStoreImm9_store off (!off.msb) _ _ hfall
      (arm8SignExtend_nine off hsx).symm)
    (by
      have hd := arm8Decode_loadStoreImm9_store (holWordExtract 9 8 0 off)
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [arm8SignExtend_nine off hsx] at hd
      exact hd)
    (arm8RunStore_eight s1 _ _ _ dest _ _ rfl)

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
  refine arm8MemStoreCaseOne .store dest base off s1 s2 ms h 3 (by decide) rfl
    (.LoadStore (.«LoadStoreImmediate@64» (3, false, .MemOp_STORE, .AccType_NORMAL,
      false, false, false, false, false, true, off, BitVec.ofNat 5 base, BitVec.ofNat 5 dest))) _ _
    (by rw [arm8Enc, arm8Ast_store_single_of_single dest base off
      (arm8ScaledSingle off 3 hmsb hoff)]; simp [hmsb])
    (arm8Encode_loadStoreImm12_store off _ _ hoff)
    (by
      have hd := arm8Decode_loadStoreImm12_store (holWordExtract 12 11 0 (off >>> 3))
        (BitVec.ofNat 5 base) (BitVec.ofNat 5 dest)
      rw [← hoff] at hd
      exact hd)
    (arm8RunStore_eight s1 _ _ _ dest _ _ rfl)
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
      simp only [hmsb, Bool.not_true, Bool.false_eq_true, ite_false] at hlow
      exact hlow)
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    rcases hfar with htrue | hscaled
    · rw [htrue] at hmsbf
      exact absurd hmsbf (by decide)
    · exact arm8_encoder_correct_mem_load_far_pos dest base off s1 s2 ms h hnsx hmsbf hscaled (by
        simp only [hmsbf, Bool.not_false, ite_true] at hlow
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
      simp only [hmsb, Bool.not_true, Bool.false_eq_true, ite_false] at hlow
      exact hlow)
  · have hmsbf : off.msb = false := by
      cases hb : off.msb
      · rfl
      · exact absurd hb hmsb
    rcases hfar with htrue | hscaled
    · rw [htrue] at hmsbf
      exact absurd hmsbf (by decide)
    · exact arm8_encoder_correct_mem_store_far_pos dest base off s1 s2 ms h hnsx hmsbf hscaled (by
        simp only [hmsbf, Bool.not_false, ite_true] at hlow
        exact hlow)

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


end Flapjack.Compiler.Encoders.Arm8.L3
