import Flapjack.Compiler.Backend.FlatToClos.Helpers
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Constructor-folding prerequisites for the flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- A recognized closure constant evaluates to its constant value without
changing the state. The evaluator remains pending HOL correspondence review. -/
theorem destConstant_evaluate {C F : Type} (expression : ClosLang.Exp) (constant : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (decoded : destConstant expression = some constant) :
    ClosSem.evaluate [expression] env state = (.val [ClosSem.makeConst constant], state) := by
  cases expression <;> simp [destConstant] at decoded
  case op trace operation args =>
    cases args with
    | cons first rest => simp at decoded
    | nil =>
      cases operation <;> try simp at decoded
      case intOp operation =>
        cases operation <;> simp at decoded
        case const value =>
          subst constant
          simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
            ClosSem.doIntApp, ClosSem.makeConst]
      case blockOp operation =>
        cases operation <;> simp at decoded
        case cons tag =>
          subst constant
          simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst]
        case constant value =>
          subst constant
          simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock]

/-- A list of recognized constants evaluates to their values without
changing the state. -/
theorem destConstants_evaluate {C F : Type} (expressions : List ClosLang.Exp)
    (constants : List ClosLang.Const) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (decoded : destConstants expressions = some constants) :
    ClosSem.evaluate expressions env state = (.val (constants.map ClosSem.makeConst), state) := by
  induction expressions generalizing constants with
  | nil =>
    simp [destConstants] at decoded
    subst constants
    simp [ClosSem.evaluate]
  | cons first rest ih =>
    cases firstDecoded : destConstant first with
    | none => simp [destConstants, firstDecoded] at decoded
    | some firstConstant =>
      cases restDecoded : destConstants rest with
      | none => simp [destConstants, firstDecoded, restDecoded] at decoded
      | some remaining =>
        simp [destConstants, firstDecoded, restDecoded] at decoded
        subst constants
        have firstEval := destConstant_evaluate first firstConstant env state firstDecoded
        have restEval := ih remaining restDecoded
        cases rest with
        | nil =>
          simp [destConstants] at restDecoded
          subst remaining
          simpa using firstEval
        | cons second tail =>
          rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, firstEval]
          simp [restEval]

/-- Folding constant constructor arguments preserves closure evaluation. -/
theorem smartCons_evaluate {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (expressions : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [smartCons trace tag expressions] env state =
      ClosSem.evaluate [.op trace (.blockOp (.cons tag)) expressions] env state := by
  cases expressions with
  | nil => rfl
  | cons first rest =>
    cases decoded : destConstants (first :: rest) with
    | none => simp [smartCons, decoded]
    | some constants =>
      have evaluated := destConstants_evaluate (first :: rest) constants env state decoded
      simp [smartCons, decoded, ClosSem.evaluate, ClosSem.fixClock, evaluated,
        ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst, List.map_reverse]

end Flapjack.Compiler.Backend.FlatToClos
