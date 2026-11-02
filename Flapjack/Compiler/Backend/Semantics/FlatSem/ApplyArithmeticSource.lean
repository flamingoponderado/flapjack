import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Source-shaped numeric application cases for the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Integer arithmetic dispatches on the source projections of its operands. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithInt_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op .intT)) vs =
      match vs.map flatToValue with
      | [.litv (.intLit x), .litv (.intLit y)] =>
        match op with
        | .add => some (s, .val (.litv (.intLit (x + y))))
        | .sub => some (s, .val (.litv (.intLit (x - y))))
        | .mul => some (s, .val (.litv (.intLit (x * y))))
        | .div => if y = 0 then some (s, .err (.raise divExnV))
            else some (s, .val (.litv (.intLit (x.fdiv y))))
        | .mod => if y = 0 then some (s, .err (.raise divExnV))
            else some (s, .val (.litv (.intLit (x.fmod y))))
        | _ => none
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp, doAppNumericCore]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

/-- Eight-bit arithmetic checks both projected operands before applying the
word operation; unsupported operators fail. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithWord8_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op (.wordT .w8))) vs =
      match vs.map flatToValue with
      | [.litv (.word8 x), .litv (.word8 y)] =>
        (wordArith op x y).map fun result => (s, .val (.litv (.word8 result)))
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp, doAppNumericCore, wordArith]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

/-- Sixty-four-bit arithmetic checks both projected operands before applying
the word operation; unsupported operators fail. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_def"]
theorem doApp_arithWord64_source {C F : Type} (s : State C F)
    (op : Arith) (vs : List Value) :
    doApp s (.src (.arith op (.wordT .w64))) vs =
      match vs.map flatToValue with
      | [.litv (.word64 x), .litv (.word64 y)] =>
        (wordArith op x y).map fun result => (s, .val (.litv (.word64 result)))
      | _ => none := by
  cases op <;> simp [doApp, doAppNumeric, applyNumericProjection,
    SemanticPrimitivesHOL.doApp, doAppNumericCore, wordArith]
  all_goals repeat' first | split at * | simp_all [valueToFlat]

end Flapjack.Compiler.Backend.FlatSem
