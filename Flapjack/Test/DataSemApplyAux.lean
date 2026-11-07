import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyAux

/-! Representative data-language primitive dispatch behavior. -/
namespace Flapjack.Test.DataSemApplyAux
open Flapjack.Compiler.Backend
open DataSem

example {C F : Type} (s : State C F) :
    doAppAux (.blockOp (.cons 9)) [] s = .val (.block 0 9 [], s) := by
  simp [doAppAux, applyNonFfi]

example {C F : Type} (s : State C F) :
    doAppAux (.blockOp (.cons 9)) [.number 4] { s with tstamps := some 7 } =
      .val (.block 7 9 [.number 4], checkLim { s with tstamps := some 8 } 1) := by
  simp [doAppAux, applyNonFfi, withFreshTimestamp]

example {C F : Type} (s : State C F) :
    doAppAux (.blockOp (.fromList 9)) [.number 1, .block 0 0 []] s =
      .err (.abort .typeError) := by
  simp [doAppAux, applyNonFfi, valueToList, BackendCommon.nilTag]

example {C F : Type} (s : State C F) :
    doAppAux (.intOp .add) [.number 4, .number 7] s = .val (.number 11, s) := by
  simp [doAppAux, applyNonFfi, doIntApp]

example {C F : Type} (s : State C F) :
    doAppAux (.memOp (.copyByte true)) [] s = .err (.abort .typeError) := by
  simp [doAppAux, applyNonFfi]

end Flapjack.Test.DataSemApplyAux
