import Flapjack.Compiler.Backend.Semantics.DataSem.Heap.SizeProperties
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.HeapTraversal
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel

/-! Source heap sizing facts used by collector soundness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend

/-- Sizing a cons list first processes its tail, then its head. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_cons"]
theorem sizeOfValues_cons (limits : DataSem.Limits) (x : DataSem.Value) (xs : List DataSem.Value)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (x :: xs) refs seen =
      let (n1, refs1, seen1) := DataSem.sizeOfValues limits xs refs seen
      let (n2, refs2, seen2) := DataSem.sizeOfValues limits [x] refs1 seen1
      (n1 + n2, refs2, seen2) := by
  cases xs with
  | nil => simp [DataSem.sizeOfValues]
  | cons y ys => simp only [DataSem.sizeOfValues, DataSem.checkRes_sizeOfValues]

/-- The optional global and its default value have identical sizing effects. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "size_of_global_to_vs"]
theorem sizeOfValues_global (limits : DataSem.Limits) (values : List DataSem.Value) (global : Option Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (seen : Spt Unit) :
    DataSem.sizeOfValues limits (values ++ DataSem.globalToValues global) refs seen =
      DataSem.sizeOfValues limits (values ++ [theGlobal global]) refs seen := by
  induction values generalizing refs seen with
  | nil =>
    cases global with
    | none =>
      cases arch : limits.arch64Bit <;>
        simp [DataSem.globalToValues, theGlobal, DataSem.sizeOfValues, DataSem.smallNum, arch]
    | some addr => simp [DataSem.globalToValues, theGlobal]
  | cons head tail ih =>
    simp only [List.cons_append]
    conv_lhs => rw [sizeOfValues_cons, ih]
    conv_rhs => rw [sizeOfValues_cons]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
