import Flapjack.Compiler.Backend.Semantics.FlatSem.Test

/-! Matched original HOL observations from `cake_flat_sem_test_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemTestParity
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.Basis.Pure.MlString

example : doTest .equal .intT (.litv (.intLit 1)) (.litv (.intLit 1)) = .val true := by decide +kernel
example : doTest .equal .intT (.litv (.intLit 1)) (.litv (.char 97)) = .typeError := by decide +kernel
example : doTest (.compare .lt) (.wordT .w64) (.litv (.word64 1)) (.litv (.word64 2)) = .typeError := by decide +kernel
example : doTest (.compare .lt) .intT (.litv (.intLit (-3))) (.litv (.intLit 1)) = .val true := by decide +kernel
example : doTest (.compare .lt) .charT (.litv (.char 97)) (.litv (.char 98)) = .val true := by decide +kernel
example : doTest (.compare .lt) .strT (.litv (.strLit (ofString "z"))) (.litv (.strLit (ofString "aa"))) = .val false := by decide +kernel
example : doTest (.altCompare .lt) .strT (.litv (.strLit (ofString "z"))) (.litv (.strLit (ofString "aa"))) = .val true := by decide +kernel
end Flapjack.Test.CakeFlatSemTestParity
