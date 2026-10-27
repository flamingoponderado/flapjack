import Flapjack.Compiler.Backend.Semantics.FlatSem.Eval

/-! Matched original observations from `cake_flat_sem_eval_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemEvalParity
open Flapjack.Compiler.Backend.FlatSem Flapjack.Compiler.Backend.BackendCommon

example {C F : Type} (s : State C F) : (decClock { s with clock := 0 }).clock = 0 := by rfl
example {C F : Type} (s : State C F) : (decClock { s with clock := 4 }).clock = 3 := by rfl
example {C F D E : Type} (s : State C F) (t : State D E) :
    (fixClock { s with clock := 3 } ({ t with clock := 7 }, true)).1.clock = 3 := by rfl
example {C : Type} (config : InstallConfig C) : doEval [] config = none := by simp [doEval]
example : valueToBytes (listToValue [.litv (.word8 2), .litv (.word8 255)]) = some [2, 255] := by
  rw [valueToBytes_eq_some]
  simp [listToValue, valueToList, nilTag, consTag, listId]
example : valueToWords (listToValue [.litv (.word64 4)]) = some [4] := by
  rw [valueToWords_eq_some]
  simp [listToValue, valueToList, nilTag, consTag, listId]

private def config : InstallConfig Nat where
  compile := fun _ _ => some ([2, 255], [4], 2)
  compileOracle := fun n => if n = 0 then (1, [.lit .none (.intLit 1)]) else (2, [])

example : (doEval [listToValue [.litv (.word8 2), .litv (.word8 255)],
    listToValue [.litv (.word64 4)]] config).map
      (fun (decs, next, _) => (decs.length, (next.compileOracle 0).1)) = some (1, 2) := by
  have bytes : valueToBytes (listToValue [.litv (.word8 2), .litv (.word8 255)]) = some [2, 255] := by
    rw [valueToBytes_eq_some]
    simp [listToValue, valueToList, nilTag, consTag, listId]
  have words : valueToWords (listToValue [.litv (.word64 4)]) = some [4] := by
    rw [valueToWords_eq_some]
    simp [listToValue, valueToList, nilTag, consTag, listId]
  simp only [doEval, bytes, words, config, Flapjack.holShiftSeq]
  rfl
end Flapjack.Test.CakeFlatSemEvalParity
