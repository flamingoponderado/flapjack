module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

@[expose] public section

/-! Error propagation through closure expressions used by flat-to-closure compilation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

namespace ClosureErrorPort
/-- Roundtrip for the closure state's canonical finite maps. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end ClosureErrorPort

/-- A failed binding evaluation propagates through a closure let. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_Let_error"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_error {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (state last : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (run : ClosSem.evaluate expressions env state = (.err error, last)) :
    ClosSem.evaluate [.let trace expressions body] env state = (.err error, last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]

/-- A failed argument evaluation propagates through a closure operation. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_Op_error"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_op_error {C F : Type} (expressions : List ClosLang.Exp)
    (env : List ClosSem.Value) (state last : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (run : ClosSem.evaluate expressions env state = (.err error, last)) :
    ClosSem.evaluate [.op trace op expressions] env state = (.err error, last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]

end Flapjack.Compiler.Backend.FlatToClos
