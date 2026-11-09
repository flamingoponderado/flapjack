module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock

@[expose] public section

/-! State preservation by flat primitive application. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem Flapjack.SemanticPrimitivesHOL

/-- A successful primitive application preserves the evaluation configuration. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "do_app_state_unchanged"]
theorem doApp_stateUnchanged {α C F : Type} (_c : α) (state : State C F)
    (op : FlatLang.Op) (values : List FlatSem.Value) (next : State C F)
    (result : Result FlatSem.Value FlatSem.Value) :
    doApp state op values = some (next, result) → next.evalConfig = state.evalConfig := by
  intro run
  exact (doApp_stable state next op values result run).2

end Flapjack.Compiler.Backend.FlatProps
