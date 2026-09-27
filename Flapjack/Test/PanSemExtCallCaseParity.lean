import Flapjack.Pancake.Semantics.PanSem.ExtCallCase

/-! The exact finite-carrier ExtCall equation remains in the test import graph.
The direct original-HOL rows and concrete error/final/return guards are in
`PanSemExtCallExactParity`; that helper has the same constructor branch structure
exposed by this tagged evaluator equation. -/

namespace Flapjack.Test.PanSemExtCallCaseParity

open Flapjack
open Flapjack.Pancake.Semantics.PanSem.ExtCallCase
open Flapjack.Pancake.PanLang (ExpHOL MlS)

abbrev evaluateExtCallEquationGuard {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width) :=
  @evaluateHOLFiniteState_extCall_source width σ _ state function
    configuration configurationLength array arrayLength

end Flapjack.Test.PanSemExtCallCaseParity
