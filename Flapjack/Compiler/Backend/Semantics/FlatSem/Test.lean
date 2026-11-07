import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives
import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations
import Flapjack.SemanticPrimitivesHOL.Test

/-! Primitive comparison in the flat evaluator. Floating-point operations use
`FpSemHOL` and retain its documented rational-cut assumption. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Perform a primitive equality or ordering test on flat values. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_test_def"]
noncomputable def doTest (test : Test) (typ : PrimType) (first second : Value) : EqResult :=
  match test with
  | .equal =>
    if checkType typ first && checkType typ second then
      match typ, first, second with
      | .float64T, .litv (.float64 a), .litv (.float64 b) => .val (fpSemFpCmpComp .equal a b)
      | .float64T, _, _ => .typeError
      | _, _, _ => doEq first second
    else .typeError
  | .compare op => match typ, first, second with
    | .intT, .litv (.intLit a), .litv (.intLit b) => .val (intCmp op a b)
    | .charT, .litv (.char a), .litv (.char b) => .val (numCmp op a.toNat b.toNat)
    | .wordT .w8, .litv (.word8 a), .litv (.word8 b) => .val (numCmp op a.toNat b.toNat)
    | .float64T, .litv (.float64 a), .litv (.float64 b) => .val (fpSemFpCmp op a b)
    | .strT, .litv (.strLit a), .litv (.strLit b) => .val (strCmp false op a b)
    | _, _, _ => .typeError
  | .altCompare op => match typ, first, second with
    | .strT, .litv (.strLit a), .litv (.strLit b) => .val (strCmp true op a b)
    | _, _, _ => .typeError
end Flapjack.Compiler.Backend.FlatSem
