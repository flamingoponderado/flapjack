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

/-- All proof-side memory operations are simulated when their arguments are. -/
theorem evaluate_memory_op {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.MemOp)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.memOp op) args] :=
  evaluate_ordinary_op trace _ args (by intro h; cases h) (by intro h; cases h)
    argsIH (primitiveSimulation_memory op)

/-- The candidate primitive dispatcher is simulated outside installation and
thunk operations. -/
theorem primitiveSimulation_nonThunk {C F : Type} (op : ClosLang.Op)
    (notThunk : ∀ thunk, op ≠ .thunkOp thunk) (notInstall : op ≠ .install) :
    PrimitiveSimulation (C := C) (F := F) op := by
  cases op with
  | memOp operation => exact primitiveSimulation_memory operation
  | label label => exact primitiveSimulation_label label
  | ffi name => exact primitiveSimulation_ffi name
  | intOp operation => exact primitiveSimulation_int operation
  | wordOp operation => exact primitiveSimulation_word operation
  | blockOp operation => exact primitiveSimulation_block operation
  | globOp operation => exact primitiveSimulation_globalOp operation
  | thunkOp operation => exact False.elim (notThunk operation rfl)
  | install => exact False.elim (notInstall rfl)

/-- Ordinary non-thunk operations preserve the candidate evaluator simulation. -/
theorem evaluate_nonThunk_op {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (notThunk : ∀ thunk, op ≠ .thunkOp thunk) (notInstall : op ≠ .install)
    (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace op args] :=
  evaluate_ordinary_op trace op args notInstall (notThunk _) argsIH
    (primitiveSimulation_nonThunk op notThunk notInstall)

end Flapjack.Compiler.Backend.ClosAnnotate
