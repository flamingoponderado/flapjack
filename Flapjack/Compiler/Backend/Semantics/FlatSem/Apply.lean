module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyFlat
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyData
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyCopy
public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyNumeric

@[expose] public section

/-! Flat primitive application. Floating-point operations inherit the
rational-cut assumptions of the source numeric model. -/
namespace Flapjack.Compiler.Backend.FlatSem

/-- Assemble the flat and source primitive cases, including the original
failure fallback and operations handled specially by the evaluator. The
`Apply*Source` submodules review equations for individual clauses. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
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
