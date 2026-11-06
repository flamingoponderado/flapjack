import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ByteCopy
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ByteLists
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.MemoryBounds

/-! Assembled memory-operation simulation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Every case in the current proof-side memory dispatcher preserves the
candidate primitive relation. The dispatcher and its reference carrier remain
untagged pending comparison with the HOL semantics. -/
theorem primitiveSimulation_memory {C F : Type} (op : ClosLang.MemOp) :
    PrimitiveSimulation (C := C) (F := F) (.memOp op) := by
  cases op with
  | ref => exact primitiveSimulation_ref
  | update => exact primitiveSimulation_update
  | el => exact primitiveSimulation_el
  | length => exact primitiveSimulation_refLength false
  | lengthByte => exact primitiveSimulation_refLength true
  | refByte flag => exact primitiveSimulation_refByte flag
  | refArray => exact primitiveSimulation_refArray
  | derefByte => exact primitiveSimulation_byteAt true
  | updateByte => exact primitiveSimulation_updateByte
  | concatByteVec => exact primitiveSimulation_decodedBytes true
  | copyByte fresh =>
    cases fresh
    · exact primitiveSimulation_copyByteWrite
    · exact primitiveSimulation_copyByteNew
  | fromListByte => exact primitiveSimulation_decodedBytes false
  | toListByte => exact primitiveSimulation_toListByte
  | lengthByteVec => exact primitiveSimulation_lengthByteVec
  | derefByteVec => exact primitiveSimulation_byteAt false
  | stringCmp fast op => exact primitiveSimulation_stringCmp fast op
  | xorByte => exact primitiveSimulation_xorByte
  | boundsCheckArray => exact primitiveSimulation_boundsCheckArray
  | boundsCheckByte loose => exact primitiveSimulation_byteBounds loose
  | configGC => exact primitiveSimulation_configGC
  | mutCons tag len =>
    intro args nextArgs source target argsRel states
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩
  | updateCons | finaliseCons =>
    intro args nextArgs source target argsRel states
    exact ⟨.err (.abort .typeError), by simp [doApp, applyMemory], by simp [doApp, applyMemory, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate
