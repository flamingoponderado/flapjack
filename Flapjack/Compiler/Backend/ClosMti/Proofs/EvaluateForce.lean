import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveThunk

/-! Forced thunk evaluation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- A successfully inspected thunk must be named by a single unflagged
reference. -/
theorem destThunk_isThunk_shape (values : List Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (mode : AstHOL.ThunkMode) (value : Value)
    (run : destThunk values refs = .isThunk mode value) :
    ∃ ptr, values = [.refPtr false ptr] := by
  cases values with
  | nil => simp [destThunk] at run
  | cons first rest =>
    cases rest with
    | cons second tail => simp [destThunk] at run
    | nil =>
      cases first <;> try simp [destThunk] at run
      case refPtr flag ptr =>
        cases flag <;> simp_all
        all_goals split at run <;> simp_all

/-- The evaluator's generated unary force application is preserved by the
multi-argument pass. -/
theorem forceApplication_codeRel (maxApp : Nat) :
    CodeRel maxApp [appUnit (.var .none 0)] [appUnit (.var .none 0)] := by
  simp [CodeRel, appUnit, ClosProps.noMti, ClosProps.noMtiList, introList,
    introExp_app_none, collectApps, introExp_var, introExp_op]

end Flapjack.Compiler.Backend.ClosMti
