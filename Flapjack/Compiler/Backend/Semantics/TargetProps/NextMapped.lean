import Flapjack.Compiler.Backend.Semantics.TargetProps.NextInterference

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source685: the complete mapped-read interference guards, payload and oracle shift. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "next_interference_MappedRead" (words_as_type_indexed_bitvec)]
theorem nextInterferenceMappedRead {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (index r reg : Nat) (nb : BitVec 8) (off pc' : BitVec width)
    (newBytes : List (BitVec 8)) (newFfi : HolFfiState σ)
    (h : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms ≠ mc.haltPc ∧ mc.target.getPc ms ≠ mc.ccachePc ∧
      Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index ∧
      holEl index mc.ffiNames = .sharedMem .mappedRead ∧
      sptAListLookup index mc.mmioInfo = some (nb, .addr r off, reg, pc') ∧
      (nb = 0 → (mc.target.getReg ms r + off).toNat % (width / 8) = 0) ∧
      mc.sharedAddresses (mc.target.getReg ms r + off) ∧
      isValidMappedRead (mc.target.getPc ms) nb (.addr r off) reg pc' mc.target ms mc.progAddresses ∧
      callFFIHOL ffi (holEl index mc.ffiNames) [nb] (HolByte.wordToBytes (mc.target.getReg ms r + off) false) = .ret newFfi newBytes) :
    nextInterference mc ffi ms = some
      (.ffiApp index newBytes ms (mc.ffiInterfer 0 (index, newBytes, ms)),
        { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, newFfi) := by
  apply nextInterferenceIntro mc ffi 1 ms
  rcases h with ⟨hn, hh, hc, hi, he, hm, ha, hd, hv, hf⟩
  have halign : (if nb = 0 then (mc.target.getReg ms r + off).toNat % (width / 8) = 0 else True) := by
    split <;> simp_all
  simp only [he] at hf
  simp only [findNextInterference]
  rw [if_neg hn, if_neg hh, if_neg hc]
  simp only [hi, he, hm, halign, hd, hv, applyOracleHOL, hf, and_self, ite_true]

/-- Literal source712: the complete mapped-write interference guards, payload and oracle shift. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "next_interference_MappedWrite" (words_as_type_indexed_bitvec)]
theorem nextInterferenceMappedWrite {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (index r reg : Nat) (nb : BitVec 8) (off pc' : BitVec width)
    (newBytes : List (BitVec 8)) (newFfi : HolFfiState σ)
    (h : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms ≠ mc.haltPc ∧ mc.target.getPc ms ≠ mc.ccachePc ∧
      Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index ∧
      holEl index mc.ffiNames = .sharedMem .mappedWrite ∧
      sptAListLookup index mc.mmioInfo = some (nb, .addr r off, reg, pc') ∧
      (nb = 0 → (mc.target.getReg ms r + off).toNat % (width / 8) = 0) ∧
      mc.sharedAddresses (mc.target.getReg ms r + off) ∧
      isValidMappedWrite (mc.target.getPc ms) nb (.addr r off) reg pc' mc.target ms mc.progAddresses ∧
      callFFIHOL ffi (holEl index mc.ffiNames) [nb] ((if nb = 0 then HolByte.wordToBytes (mc.target.getReg ms reg) false
        else HolByte.wordToBytesAux nb.toNat (mc.target.getReg ms reg) false) ++
        HolByte.wordToBytes (mc.target.getReg ms r + off) false) = .ret newFfi newBytes) :
    nextInterference mc ffi ms = some
      (.ffiApp index newBytes ms (mc.ffiInterfer 0 (index, newBytes, ms)),
        { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, newFfi) := by
  apply nextInterferenceIntro mc ffi 1 ms
  rcases h with ⟨hn, hh, hc, hi, he, hm, ha, hd, hv, hf⟩
  have halign : (if nb = 0 then (mc.target.getReg ms r + off).toNat % (width / 8) = 0 else True) := by
    split <;> simp_all
  simp only [he] at hf
  simp only [findNextInterference]
  rw [if_neg hn, if_neg hh, if_neg hc]
  simp only [hi, he, hm, halign, hd, hv, applyOracleHOL, hf, and_self, ite_true]

end Flapjack.Compiler.Backend.Semantics.TargetProps
