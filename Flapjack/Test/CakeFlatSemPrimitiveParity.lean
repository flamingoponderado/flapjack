import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives

/-! Observations matched with `source_to_flat_primitive_type_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemPrimitiveParity
open Flapjack.Compiler.Backend.FlatSem

example : checkType .boolT (boolValue true) = true := by rfl
example : checkType .boolT (boolValue false) = true := by rfl
example : checkType .boolT (.conv (some (2, some 0)) []) = false := by rfl
example : checkType .intT (.litv (.intLit 7)) = true := by rfl
example : checkType .intT (.litv (.char 97)) = false := by rfl
example : checkType (.wordT .w8) (.litv (.word8 7)) = true := by rfl
example : checkType (.wordT .w64) (.litv (.word64 7)) = true := by rfl
example : destLitv (.litv (.intLit 7)) = some (.intLit 7) := by rfl
example : destLitv (.conv none []) = none := by rfl
example : valueToFlat (Flapjack.SemanticPrimitivesHOL.boolValue true) = boolValue true := by rfl
example : valueToFlat (.loc true 4) = .vectorv [] := by rfl
example : flatToValue (boolValue false) = Flapjack.SemanticPrimitivesHOL.boolValue false := by rfl
example : flatToValue (.loc true 4) = .vectorv [] := by rfl
example : bindExnV = .conv (some (0, none)) [] := by rfl
example : chrExnV = .conv (some (1, none)) [] := by rfl
example : divExnV = .conv (some (2, none)) [] := by rfl
example : subscriptExnV = .conv (some (3, none)) [] := by rfl
end Flapjack.Test.CakeFlatSemPrimitiveParity
