import Flapjack.Compiler.Backend.Semantics.FlatSem.Operations
import Flapjack.Basis.Pure.MlString

/-! Matched observations from `cake_flat_sem_ops_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemOpsParity
open Flapjack.AstHOL
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

example : doEq (.litv (.intLit 4)) (.litv (.intLit 4)) = .val true := by simp [doEq, SemanticPrimitivesHOL.litSameType]
example : doEq (.litv (.intLit 4)) (.litv (.char 97)) = .typeError := by simp [doEq, SemanticPrimitivesHOL.litSameType]
example : doEq (.loc true 3) (.loc true 3) = .val true := by simp [doEq]
example : doEq (.loc false 3) (.loc true 3) = .typeError := by simp [doEq]
example : doEq (.conv (some (0, some 1)) []) (.conv (some (2, some 1)) []) = .val false := by simp [doEq, ctorSameType]
example : doEq (.conv (some (0, some 1)) []) (.conv (some (0, some 2)) []) = .typeError := by simp [doEq, ctorSameType]
example : doEq (.vectorv []) (.vectorv [.litv (.intLit 1)]) = .val false := by simp [doEq]
example : doEqList [.litv (.intLit 1)] [] = .val false := by simp [doEqList]

example : doOpApp [.closure ⟨[]⟩ (ofString "x") (.lit .none (.intLit 9)), .litv (.intLit 4)] =
    some (⟨[(ofString "x", .litv (.intLit 4))]⟩, .lit .none (.intLit 9)) := by rfl

example : doOpApp [.recclosure ⟨[]⟩
    [(ofString "f", ofString "x", .lit .none (.intLit 9)),
     (ofString "f", ofString "y", .lit .none (.intLit 8))] (ofString "f"),
    .litv (.intLit 4)] = none := by rfl

end Flapjack.Test.CakeFlatSemOpsParity
