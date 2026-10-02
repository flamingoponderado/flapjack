import Flapjack.Compiler.Backend.Semantics.TargetProps.NextMapped

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source742: the generic shared-memory operator result follows from its two original conditional cases. -/
@[hol "cakeml/compiler/backend/semantics/targetPropsScript.sml"
  "next_interference_SharedMem" (words_as_type_indexed_bitvec)]
theorem nextInterferenceSharedMem {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (index r reg : Nat) (nb : BitVec 8) (off pc' : BitVec width)
    (op : HolShmemOp) (newBytes : List (BitVec 8)) (newFfi : HolFfiState σ)
    (h : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms ≠ mc.haltPc ∧ mc.target.getPc ms ≠ mc.ccachePc ∧
      Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index ∧
      holEl index mc.ffiNames = .sharedMem op ∧
      sptAListLookup index mc.mmioInfo = some (nb, .addr r off, reg, pc') ∧
      (nb = 0 → (mc.target.getReg ms r + off).toNat % (width / 8) = 0) ∧
      mc.sharedAddresses (mc.target.getReg ms r + off) ∧
      (op = .mappedRead →
        isValidMappedRead (mc.target.getPc ms) nb (.addr r off) reg pc' mc.target ms mc.progAddresses ∧
        callFFIHOL ffi (holEl index mc.ffiNames) [nb]
          (HolByte.wordToBytes (mc.target.getReg ms r + off) false) = .ret newFfi newBytes) ∧
      (op = .mappedWrite →
        isValidMappedWrite (mc.target.getPc ms) nb (.addr r off) reg pc' mc.target ms mc.progAddresses ∧
        callFFIHOL ffi (holEl index mc.ffiNames) [nb]
          ((if nb = 0 then HolByte.wordToBytes (mc.target.getReg ms reg) false
            else HolByte.wordToBytesAux nb.toNat (mc.target.getReg ms reg) false) ++
            HolByte.wordToBytes (mc.target.getReg ms r + off) false) = .ret newFfi newBytes)) :
    nextInterference mc ffi ms = some
      (.ffiApp index newBytes ms (mc.ffiInterfer 0 (index, newBytes, ms)),
        { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, newFfi) := by
  rcases h with ⟨hn, hh, hc, hi, he, hm, ha, hd, hr, hw⟩
  cases op with
  | mappedRead =>
    obtain ⟨hv, hf⟩ := hr rfl
    exact nextInterferenceMappedRead mc ffi ms index r reg nb off pc' newBytes newFfi
      ⟨hn, hh, hc, hi, he, hm, ha, hd, hv, hf⟩
  | mappedWrite =>
    obtain ⟨hv, hf⟩ := hw rfl
    exact nextInterferenceMappedWrite mc ffi ms index r reg nb off pc' newBytes newFfi
      ⟨hn, hh, hc, hi, he, hm, ha, hd, hv, hf⟩

end Flapjack.Compiler.Backend.Semantics.TargetProps
