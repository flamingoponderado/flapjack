module

public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBasic
public import Flapjack.Compiler.Backend.Semantics.ClosSem.Int

@[expose] public section

/-! Constant-application evaluation facts from `closPropsScript.sml`. -/
namespace Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosLang
open Flapjack.Compiler.Backend.BackendCommon

@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_MAP_Op_Const"]
theorem evaluateMapOpConst {α C F : Type} (f : α → Int) (env : List Value)
    (s : State C F) (ls : List α) (tra : Tra) :
    evaluate (ls.map fun x => .op tra (.intOp (.const (f x))) []) env s =
      (.val (ls.map fun x => .number (f x)), s) := by
  induction ls with
  | nil => simp [evaluate]
  | cons x xs ih =>
    rw [List.map_cons, evaluateCons]
    simp only [evaluate]
    simp [doApp, applyNumeric, doIntApp, fixClock]
    rw [ih]
    simp [holHd]

end Flapjack.Compiler.Backend.ClosProps
