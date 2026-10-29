import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyMemory
import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk

/-! Assembled closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Closure primitive application. Install and force-thunk control flow are
handled by the evaluator; their ordinary primitive fallback is a type error.
The complete dispatcher is proof-side and remains untagged pending review of
the source clauses, finite-map representation and floating-point assumptions. -/
noncomputable def doApp {C F : Type} (op : ClosLang.Op) (args : List Value) (state : State C F) :
    Result (Value × State C F) Value :=
  let fail : Result (Value × State C F) Value := .err (.abort .typeError)
  let convert (value : Option (Value × State C F)) := match value with
    | none => fail
    | some pair => Result.val pair
  match op with
  | .globOp operation => convert (applyGlobal operation args state)
  | .blockOp operation => convert (applyBlock operation args state)
  | .memOp operation => convert (applyMemory operation args state)
  | .intOp _ | .wordOp _ => convert (applyNumeric op args state)
  | .ffi name =>
    match args with
    | [.byteVector configuration, .refPtr _ index] =>
      match state.refs.lookup index with
      | some (.byteArray bytes) =>
        match callFFIHOL state.ffi (.extCall name) configuration bytes with
        | .ret ffi updated =>
          .val (unitValue, { state with
            refs := state.refs.updateEq (index, .byteArray updated)
            ffi := ffi })
        | .final event => .err (.abort (.ffiError event))
      | _ => fail
    | _ => fail
  | .thunkOp operation =>
    match operation, args with
    | .allocThunk mode, [value] =>
      if badThunkUpdate mode value state.refs then fail else
        let index := leastUnusedRef state.refs
        .val (.refPtr false index, { state with refs := state.refs.updateEq (index, .thunk mode value) })
    | .updateThunk mode, [.refPtr false index, value] =>
      if badThunkUpdate mode value state.refs then fail else
        match state.refs.lookup index with
        | some (.thunk .notEvaluated _) =>
          .val (unitValue, { state with refs := state.refs.updateEq (index, .thunk mode value) })
        | _ => fail
    | _, _ => fail
  | _ => fail

end Flapjack.Compiler.Backend.ClosSem
