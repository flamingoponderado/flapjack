import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions

/-! Matched observations from `cake_flat_sem_conversions_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemConversionsParity
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

example : valueToList (listToValue []) = some [] := by simp [valueToList, listToValue, nilTag, listId]
example : valueToList (listToValue [.litv (.intLit 1), .litv (.intLit 2)]) =
    some [.litv (.intLit 1), .litv (.intLit 2)] := by simp [valueToList, listToValue, nilTag, consTag, listId]
example : valueToList (.conv (some (0, some 2)) []) = none := by simp [valueToList, nilTag, listId]
example : valueToList (.conv (some (0, some 1)) [.litv (.intLit 1), .litv (.intLit 2)]) = none := by simp [valueToList, consTag, listId]
example : valueToCharList (listToValue [.litv (.char 97), .litv (.char 98)]) = some [97, 98] := by simp [valueToCharList, listToValue, nilTag, consTag, listId]
example : valueToCharList (listToValue [.litv (.intLit 1)]) = none := by simp [valueToCharList, listToValue, nilTag, consTag, listId]
example : valuesToString [.litv (.strLit (ofString "ab")), .litv (.strLit (ofString "cd"))] = some (ofString "abcd") := by rfl
example : valuesToString [.litv (.intLit 1)] = none := by rfl
end Flapjack.Test.CakeFlatSemConversionsParity
