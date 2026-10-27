import Flapjack.SemanticPrimitivesHOL.Test

/-! Primitive comparison observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceTestParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def intV (n : Int) : Value := .litv (.intLit n)
private def strV (s : String) : Value := .litv (.strLit (ofString s))

example : doTest .equal .intT (intV 1) (intV 1) = .val true := by decide +kernel
example : doTest .equal .intT (intV 1) (.litv (.char 97)) = .typeError := by decide +kernel
example : doTest (.compare .lt) (.wordT .w64) (.litv (.word64 1)) (.litv (.word64 2)) = .typeError := by decide +kernel
example : doTest (.compare .lt) .intT (intV (-3)) (intV 1) = .val true := by decide +kernel
example : doTest (.compare .lt) .strT (strV "z") (strV "aa") = .val false := by decide +kernel
example : doTest (.altCompare .lt) .strT (strV "z") (strV "aa") = .val true := by decide +kernel

-- IEEE NaN equality is false in the pinned machine_ieee comparison capture.
example : doTest .equal .float64T (.litv (.float64 0x7ff8000000000001))
    (.litv (.float64 0x7ff8000000000001)) = .val false := by decide +kernel

end Flapjack.Test.CakeSourceTestParity
