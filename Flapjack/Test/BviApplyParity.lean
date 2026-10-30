import Flapjack.Compiler.Backend.Semantics.BviSem.Apply

/-! Checks BVI installation failure, special dispatch, and BVL fallback. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BackendCommon

/-- The original bad-arity installation observation, at any result type. -/
example {C F R : Type} (s : BviState C F) :
    doInstall [] s = (Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError) :
      Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) R) := by
  simp [doInstall]

example {C F : Type} (s : BviState C F) :
    doApp .install [] s = .err (.abort .typeError) := by
  simp [doApp, doInstall]

example {C F : Type} (s : BviState C F) :
    doApp (.intOp (.const 5)) [] s = .val (.number 5, s) := by
  simp [doApp, doAppAux, smallEnoughInt]

example {C F : Type} (s : BviState C F) :
    doApp (.intOp .add) [.number 2, .number 3] s = .val (.number 5, s) := by
  simp [doApp, doAppAux, BvlSem.doApp, applyNumeric, doIntApp, fromBvl_toBvl]

/-- Installation rejects incorrect declared lengths before invoking the oracle. -/
example {C F R : Type} (s : BviState C F) :
    doInstall [.block 0 [], .block 0 [], .number 1, .number 0] s =
      (Flapjack.SemanticPrimitivesHOL.Result.err (.abort .typeError) :
        Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) R) := by
  simp [doInstall, valueToBytes, valueToWords, valueToList, byteNumbers, wordValues,
    nilTag]

end Flapjack.Compiler.Backend.BviSem
