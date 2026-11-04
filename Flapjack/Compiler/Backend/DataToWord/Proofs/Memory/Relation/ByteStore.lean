import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteLoad
import Flapjack.Compiler.Backend.LabToTarget.InstMem

/-! Concrete writes to a separated packed byte payload. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- Exchange the first two separated assertions while retaining the frame. -/
theorem star_swap_first {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- Writing one element of a separated word list updates exactly its graph
entry and preserves the entire external separation frame. -/
theorem wordList_write {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (values : List β) (i : Nat) (newValue : β)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (frame : ((BitVec width × β) → Prop) → Prop) (bound : i < values.length)
    (separated : SetSep.star (Misc.wordList address values) frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star (Misc.wordList address (values.set i newValue)) frame
      (SetSep.fun2Set ((fun key => if key = address + BitVec.ofNat width i * StackRemove.bytesInWord width
        then newValue else memory key), domain)) := by
  classical
  induction values generalizing address i frame with
  | nil => simp at bound
  | cons value values ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      have changed := SetSep.writeFun2Set newValue address value _ memory domain separated
      rw [SetSep.starComm] at changed
      convert changed using 2
      congr 1
      funext key
      by_cases h : key = address <;> simp [h]
    | succ i =>
      simp only [List.set_cons_succ, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      rw [star_swap_first] at separated
      have changed := ih (address + StackRemove.bytesInWord width) i
        (SetSep.star (SetSep.one (address, value)) frame) (by simpa using bound) separated
      rw [star_swap_first] at changed
      have addressEq : (address + StackRemove.bytesInWord width) +
          BitVec.ofNat width i * StackRemove.bytesInWord width =
          address + BitVec.ofNat width (i + 1) * StackRemove.bytesInWord width := by
        simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        ac_rfl
      simpa only [addressEq] using changed

/-- Updating a source byte updates the corresponding packed 64-bit word in
the concrete memory graph, while preserving the whole separation frame. -/
theorem bytePayload_store64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (base : BitVec 64) (be : Bool) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Prop)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (indexBound : i < bytes.length) (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (Misc.wordList base ((DataToWord.writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, domain))) :
    ∃ oldWord, memory (base + BitVec.ofNat 64 (i / 8) * 8) = .word oldWord ∧
      SetSep.star (Misc.wordList base ((DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word)) frame
        (SetSep.fun2Set ((fun key => if key = base + BitVec.ofNat 64 (i / 8) * 8 then
          .word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be) else memory key), domain)) := by
  let packed := DataToWord.writeBytes bytes words be
  have length : packed.length = words.length := writeBytes_wordCount bytes words be
  have bound : i / 8 < packed.length := by
    rw [length]
    exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  let oldWord := packed[i / 8]
  have graph : SetSep.fun2Set (memory, domain) (base + BitVec.ofNat 64 (i / 8) * 8, .word oldWord) := by
    rcases separated with ⟨left, right, partition, payload, rest⟩
    rw [← partition.1]
    apply Or.inl
    have entry := wordList_indexMember (packed.map WordLocW.word) (i / 8) (by simpa using bound) base left payload
    simpa [StackRemove.bytesInWord, oldWord] using entry
  have memEq := ((SetSep.fun2SetThm memory domain _ _).mp graph).1
  refine ⟨oldWord, memEq, ?_⟩
  have write := wordList_write base (packed.map WordLocW.word) (i / 8)
    (.word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be)) memory domain frame (by simpa using bound) separated
  have listEq : (DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word =
      (packed.map WordLocW.word).set (i / 8) (.word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be)) := by
    rw [writeBytes_setByte64 bytes words be i byte indexBound capacity]
    rw [List.modify_eq_set_get _ bound]
    simp [packed, oldWord, List.map_set]
  rw [listEq]
  simp only [StackRemove.bytesInWord] at write
  convert write using 2
  congr 1

/-- The actual 64-bit word-semantics byte store succeeds and preserves the
separated packed-payload assertion for the source list update. -/
theorem bytePayload_memStore64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (base : BitVec 64) (be : Bool) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (aligned : (base >>> (3 : Nat)) <<< (3 : Nat) = base) (indexBound : i < bytes.length)
    (wordBound : i < 2 ^ 64) (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (Misc.wordList base ((DataToWord.writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    ∃ updated, memStoreByteAuxExact memory domain be (base + BitVec.ofNat 64 i) byte = some updated ∧
      SetSep.star (Misc.wordList base ((DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word)) frame
        (SetSep.fun2Set (updated, fun addr => domain addr = true)) := by
  obtain ⟨oldWord, memEq, assertion⟩ := bytePayload_store64 bytes words base be memory
    (fun addr => domain addr = true) frame i byte indexBound capacity separated
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
  have byteEq : setByteHOL8 (base + BitVec.ofNat 64 i) byte oldWord be =
      setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be := by
    rw [LabToTarget.setByteHOL8_eq]
    simp only [setByte, byteIndex, show 64 / 8 = 8 by decide,
      addressMod, remNat, Nat.mod_eq_of_lt remainder]
  have loaded := bytePayload_load64 bytes words base be memory domain frame i aligned indexBound wordBound capacity separated
  have inDomain : domain (base + BitVec.ofNat 64 (i / 8) * 8) = true := by
    unfold memLoadByteAuxExact at loaded
    rw [alignEq, memEq] at loaded
    simp at loaded
    exact loaded.1
  refine ⟨_, ?_, assertion⟩
  unfold memStoreByteAuxExact
  simp only [alignEq, memEq, inDomain, ↓reduceIte, byteEq]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
