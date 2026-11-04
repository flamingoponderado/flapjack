import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement
import Flapjack.Compiler.Backend.Semantics.WordSem

/-! Reading a concrete byte from a packed heap payload. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- Alignment and byte-lane arithmetic for a 64-bit packed payload. -/
theorem alignedByteAddress64 (base q r : BitVec 64)
    (aligned : (base >>> (3 : Nat)) <<< (3 : Nat) = base) (small : r.ult 8 = true) :
    riscvByteAlignHOL (base + q * 8 + r) = base + q * 8 := by
  simp only [riscvByteAlignHOL, show Nat.log2 (64 / 8) = 3 by decide]
  change (((base + q * 8 + r) >>> (3 : Nat)) <<< (3 : Nat)) = base + q * 8
  bv_decide

/-- Reading any in-bounds byte in a separated packed payload gives the
corresponding source byte in either byte order. -/
theorem bytePayload_load64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (base : BitVec 64) (be : Bool) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat)
    (aligned : (base >>> (3 : Nat)) <<< (3 : Nat) = base) (indexBound : i < bytes.length)
    (wordBound : i < 2 ^ 64) (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (Misc.wordList base ((DataToWord.writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, fun a => domain a = true))) :
    memLoadByteAuxExact memory domain be (base + BitVec.ofNat 64 i) = some bytes[i] := by
  let packed := DataToWord.writeBytes bytes words be
  have packedLen : packed.length = words.length := writeBytes_wordCount bytes words be
  have idx : i / 8 < packed.length := by
    rw [packedLen]
    exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  obtain ⟨left, right, partition, payload, rest⟩ := separated
  have entry := wordList_indexMember (packed.map WordLocW.word) (i / 8) (by simpa using idx) base left payload
  have graph : SetSep.fun2Set (memory, fun a => domain a = true)
      (base + BitVec.ofNat 64 (i / 8) * 8, .word packed[i / 8]) := by
    rw [← partition.1]
    apply Or.inl
    simpa [StackRemove.bytesInWord, List.getElem_map] using entry
  obtain ⟨memEq, dom⟩ := (SetSep.fun2SetThm memory _ _ _).mp graph
  have remainder : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have small : (BitVec.ofNat 64 (i % 8)).ult 8 = true := by
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega : i % 8 < 18446744073709551616)]
    exact remainder
  have decomposition : BitVec.ofNat 64 i = BitVec.ofNat 64 (i / 8) * 8 + BitVec.ofNat 64 (i % 8) := by
    have h := Nat.mod_add_div i 8
    have eq : i = i / 8 * 8 + i % 8 := by omega
    conv_lhs => rw [eq]
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
    rfl
  have alignEq : riscvByteAlignHOL (base + BitVec.ofNat 64 i) = base + BitVec.ofNat 64 (i / 8) * 8 := by
    rw [decomposition, ← BitVec.add_assoc]
    exact alignedByteAddress64 base (BitVec.ofNat 64 (i / 8)) (BitVec.ofNat 64 (i % 8)) aligned small
  have baseMod : base.toNat % 8 = 0 := by
    have aligned3 : holAligned 3 base = true := by simp [holAligned, holAlign_eq_shift, aligned]
    simpa using (holAligned_iff 3 base).mp aligned3
  have addressMod : (base + BitVec.ofNat 64 i).toNat % 8 = i % 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
    norm_num
    omega
  have remNat : (BitVec.ofNat 64 (i % 8)).toNat = i % 8 := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have byteEq : getByteHOL8 (base + BitVec.ofNat 64 i) packed[i / 8] be =
      getByte (BitVec.ofNat 64 (i % 8)) packed[i / 8] be := by
    simp only [getByteHOL8, byteIndexHOL, getByte, byteIndex, show 64 / 8 = 8 by decide,
      addressMod, remNat, Nat.mod_eq_of_lt remainder]
  have byte := writeBytes_getByte64 bytes words be i indexBound capacity
  unfold memLoadByteAuxExact
  rw [alignEq, memEq, dom]
  simpa [packed, byteEq] using byte

/-- A related byte array can be read at every valid byte index. This is the
read-only 64-bit portion of the original byte-array memory theorem. -/
theorem memoryRel_byteArrayLoad64 (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (bit flag : Bool) (ref : Nat) (bytes : List (BitVec 8)) (word address : BitVec 64)
    (vars : List (DataSem.Value × WordLocW 64)) (i : Nat)
    (related : memoryRel conf be next refs space store memory domain ((.refPtr bit ref, .word word) :: vars))
    (found : sptLookup ref refs = some (.byteArray flag bytes))
    (real : getRealAddr conf store word = some address) (inBounds : i < bytes.length) :
    memLoadByteAuxExact memory domain be (address + 8 + BitVec.ofNat 64 i) = some bytes[i] := by
  obtain ⟨w, addr, wordEq, _, real', simple, _, _, configBound, byteBound⟩ :=
    memoryRel_byteArrayHeader conf be next refs space store memory domain bit flag ref bytes (.word word) vars
      related found (Or.inr rfl)
  have wordSame : word = w := WordLocW.word.inj wordEq
  subst w
  have addrSame : address = addr := Option.some.inj (real.symm.trans real')
  subst addr
  obtain ⟨header, frame, _, payload, _, count⟩ :=
    memoryRel_byteArrayWordsImp conf be next refs space store memory domain bit flag ref bytes word address vars
      ⟨related, found, Or.inr rfl, real⟩
  have lenBits : conf.lenSize + 3 ≤ 61 := by omega
  have power : 2 ^ (conf.lenSize + 3) ≤ 2 ^ 61 := Nat.pow_le_pow_right (by decide) lenBits
  have byteBound' : bytes.length + 8 < 2 ^ (conf.lenSize + 3) := by simpa using byteBound
  have indexSmall : i < 2 ^ 64 := by norm_num at power ⊢; omega
  have payloadCapacity : bytes.length ≤ ((WordGcFunctions.decodeLength conf header).toNat) * 8 := by
    rw [count]
    have h := Nat.mod_add_div bytes.length 8
    have rem := Nat.mod_lt bytes.length (by decide : 0 < 8)
    omega
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, rest⟩ := related
  obtain ⟨curr, other, currAligned, _, currStore, _, _, _, _, _, _, _, _⟩ := heapMem.2.2.2.2.2.2.2
  have currAlign : (curr >>> (3 : Nat)) <<< (3 : Nat) = curr := by
    have h : holAligned 3 curr = true := by
      simpa [holByteAligned, holLOG2_eq_log2] using currAligned
    simpa [holAligned, holAlign_eq_shift] using h
  have addrEq : address = curr + ((word >>> shiftLength conf) <<< (3 : Nat)) := by
    simpa [getRealSimpleAddr, currStore, wordShiftAmount] using simple.symm
  have payloadAlign : ((address + 8) >>> (3 : Nat)) <<< (3 : Nat) = address + 8 := by
    rw [addrEq]
    generalize word >>> shiftLength conf = shifted
    bv_decide
  simpa [BitVec.add_assoc] using bytePayload_load64 bytes
    (List.replicate ((WordGcFunctions.decodeLength conf header).toNat) 0)
    (address + 8) be memory domain frame i payloadAlign inBounds indexSmall
    (by simpa using payloadCapacity) (by simpa [StackRemove.bytesInWord] using payload)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
