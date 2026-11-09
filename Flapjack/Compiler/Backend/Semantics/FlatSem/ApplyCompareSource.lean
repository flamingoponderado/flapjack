import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Source-shaped equality and comparison cases of flat application. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Equality accepts exactly two values and propagates comparison type errors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_equality_source {C F : Type} (s : State C F) (vs : List Value) :
    doApp s (.src .equality) vs = match vs with
      | [x, y] => match doEq x y with
        | .typeError => none
        | .val b => some (s, .val (boolValue b))
      | _ => none := by
  rfl

/-- Typed tests accept exactly two values and propagate comparison type errors. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_test_source {C F : Type} (s : State C F) (test : Test) (typ : PrimType)
    (vs : List Value) :
    doApp s (.src (.test test typ)) vs = match vs with
      | [x, y] => match doTest test typ x y with
        | .typeError => none
        | .val b => some (s, .val (boolValue b))
      | _ => none := by
  rfl

end Flapjack.Compiler.Backend.FlatSem
