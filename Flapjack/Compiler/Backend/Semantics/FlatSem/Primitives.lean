import Flapjack.Compiler.Backend.Semantics.FlatSem
import Flapjack.Compiler.Backend.BackendCommon.BoolTags

/-! Primitive type checks and literal projection in the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.Compiler.Backend.BackendCommon

/-- Check the seven primitive types against flat values. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "check_type_def"]
def checkType : PrimType → Value → Bool
  | .boolT, .conv (some (tag, some typeId)) [] =>
    typeId == FlatLang.boolId && (tag == trueTag || tag == falseTag)
  | .intT, .litv (.intLit _) => true
  | .charT, .litv (.char _) => true
  | .strT, .litv (.strLit _) => true
  | .wordT .w8, .litv (.word8 _) => true
  | .wordT .w64, .litv (.word64 _) => true
  | .float64T, .litv (.float64 _) => true
  | _, _ => false

/-- Project a literal from a flat value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "dest_Litv_def"]
def destLitv : Value → Option Lit
  | .litv lit => some lit
  | _ => none
end Flapjack.Compiler.Backend.FlatSem
