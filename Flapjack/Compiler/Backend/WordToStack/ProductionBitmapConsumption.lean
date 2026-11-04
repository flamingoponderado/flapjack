import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapWritePair
import Flapjack.Compiler.Backend.WordRemove.Production

/-! Flapjack caller invariants across the executed native MustTerminate removal.
These are structural carrier consequences, not HOL semantic theorem ports.
Actual writer-traversal discharge remains separate from the cleanup invariant. -/
namespace Flapjack.ProductionBitmapConsumption
open Compiler.Backend ProductionGcCutsets RiscV RiscV.CakeRegAlloc

/-- Native removal preserves every original stack-cutset predicate, including
both cutsets, both returning Call bodies, FFI/Install and tail-handler erasure. -/
theorem everyStack_remove {width : Nat} [NeZero width] (predicate : Nat → Bool) :
    ∀ program : WordLangProgHOL (BitVec width),
      everyStackVarHOL predicate (WordRemove.removeMustTerminate program) =
        everyStackVarHOL predicate program
  | .mustTerminate body => by
      simpa only [WordRemove.removeMustTerminate, everyStackVarHOL] using
        everyStack_remove predicate body
  | .seq first second => by
      simp only [WordRemove.removeMustTerminate, everyStackVarHOL,
        everyStack_remove predicate first, everyStack_remove predicate second]
  | .ite op condition right first second => by
      simp only [WordRemove.removeMustTerminate, everyStackVarHOL,
        everyStack_remove predicate first, everyStack_remove predicate second]
  | .loop before body after => by
      simpa only [WordRemove.removeMustTerminate, everyStackVarHOL] using
        everyStack_remove predicate body
  | .call returns target arguments handler => by
      rcases returns with _ | ⟨values, sets, body, l1, l2⟩
      · rcases handler with _ | ⟨exception, hbody, h1, h2⟩ <;>
          simp [WordRemove.removeMustTerminate, everyStackVarHOL]
      · rcases handler with _ | ⟨exception, hbody, h1, h2⟩ <;>
          simp [WordRemove.removeMustTerminate, everyStackVarHOL,
            everyStack_remove predicate body]
        exact congrArg _ (everyStack_remove predicate hbody)
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ |
      .store _ _ | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ |
      .return _ _ | .break _ | .continue _ | .tick | .opCurrHeap _ _ _ |
      .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ |
      .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by rfl

end Flapjack.ProductionBitmapConsumption
