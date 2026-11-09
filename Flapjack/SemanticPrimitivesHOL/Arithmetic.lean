module

public import Flapjack.SemanticPrimitivesHOL.NumericConversion
public import Flapjack.SemanticPrimitivesHOL.ApplyNumericCore

@[expose] public section

/-! HOL's primitive arithmetic before the application type guard. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

/-- Test whether a value is the source-language true constructor. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "the_Boolv_def"]
noncomputable def theBoolv (v : Value) : Bool := by
  classical
  exact decide (v = boolValue true)

/-- Source primitive arithmetic, including the original unchecked selectors
and division exception. Floating-point operations inherit the rational-cut
assumption of the source floating-point model. -/
@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_arith_def" (reals_as_rational_cuts)]
noncomputable def doArith (action : Arith) (typ : PrimType) (values : List Value) :
    Option (Sum Value Value) :=
  match typ with
  | .float64T => match action, values.map theLitvFloat64 with
    | .abs, [a] => some (.inr (.litv (.float64 (holFp64Abs a))))
    | .neg, [a] => some (.inr (.litv (.float64 (holFp64Negate a))))
    | .sqrt, [a] => some (.inr (.litv (.float64 (holFp64Sqrt .roundTiesToEven a))))
    | .add, [a, b] => some (.inr (.litv (.float64 (holFp64Add .roundTiesToEven a b))))
    | .sub, [a, b] => some (.inr (.litv (.float64 (holFp64Sub .roundTiesToEven a b))))
    | .mul, [a, b] => some (.inr (.litv (.float64 (holFp64Mul .roundTiesToEven a b))))
    | .div, [a, b] => some (.inr (.litv (.float64 (holFp64Div .roundTiesToEven a b))))
    | .fma, [a, b, c] => some (.inr (.litv (.float64 (holFp64MulAdd .roundTiesToEven b c a))))
    | _, _ => none
  | .intT => match action, values.map theLitvInt with
    | .add, [a, b] => some (.inr (.litv (.intLit (a + b))))
    | .sub, [a, b] => some (.inr (.litv (.intLit (a - b))))
    | .mul, [a, b] => some (.inr (.litv (.intLit (a * b))))
    | .div, [a, b] => some (if b = 0 then .inl divExnV else .inr (.litv (.intLit (a.fdiv b))))
    | .mod, [a, b] => some (if b = 0 then .inl divExnV else .inr (.litv (.intLit (a.fmod b))))
    | _, _ => none
  | .wordT .w8 => match values.map theLitvWord8 with
    | [a, b] => (wordArith action a b).map (fun w => .inr (.litv (.word8 w)))
    | _ => none
  | .wordT .w64 => match values.map theLitvWord64 with
    | [a, b] => (wordArith action a b).map (fun w => .inr (.litv (.word64 w)))
    | _ => none
  | .boolT => match action, values with
    | .not, [v] => some (.inr (boolValue (!theBoolv v)))
    | _, _ => none
  | _ => none

end Flapjack.SemanticPrimitivesHOL
