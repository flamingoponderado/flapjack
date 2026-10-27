import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyData
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyCopy
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

/-! Assembled flat primitive application. Full correspondence with HOL remains
open, including review of the reused source numeric and floating-point model. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- Assemble flat and source primitive cases. Unknown source operations return
failure, as do operations handled specially by the evaluator. This declaration
is untagged pending a complete clause-by-clause HOL and carrier review. -/
noncomputable def doApp {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) :
    Option (State C F × Flapjack.SemanticPrimitivesHOL.Result Value Value) :=
  match op with
  | .src sourceOp =>
    match doAppNumeric state sourceOp values with
    | some result => result
    | none => match doAppMemory state sourceOp values with
      | some result => result
      | none => match doAppData state sourceOp values with
        | some result => result
        | none => (doAppCopy state sourceOp values).getD none
  | _ => (doAppFlat state op values).getD none

end Flapjack.Compiler.Backend.FlatSem
