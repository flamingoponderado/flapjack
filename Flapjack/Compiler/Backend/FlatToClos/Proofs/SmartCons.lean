import Flapjack.Compiler.Backend.FlatToClos.Helpers
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock
import Batteries.Data.List.Basic

/-! Constructor-folding prerequisites for the flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

namespace SmartConsPort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end SmartConsPort

@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "dest_Constant_IMP"]
theorem destConstant_iff (expression : ClosLang.Exp) (constant : ClosLang.Const) :
    destConstant expression = some constant ↔
      (∃ trace, expression = .op trace (.blockOp (.constant constant)) []) ∨
      (∃ trace value, expression = .op trace (.intOp (.const value)) [] ∧
        constant = .constInt value) ∨
      (∃ trace tag, expression = .op trace (.blockOp (.cons tag)) [] ∧
        constant = .constCons tag []) := by
  cases expression <;> simp [destConstant]
  case op trace operation args =>
    cases args <;> simp
    case nil =>
      cases operation <;> simp
      case intOp op =>
        cases op <;> simp [eq_comm]
        all_goals aesop
      case blockOp op =>
        cases op <;> simp [eq_comm]
        all_goals aesop

@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "dest_Constants_IMP"]
theorem destConstants_imp (expressions : List ClosLang.Exp) (constants : List ClosLang.Const)
    (decoded : destConstants expressions = some constants) :
    List.Forall₂ (fun expression constant => destConstant expression = some constant)
      expressions constants := by
  induction expressions generalizing constants with
  | nil =>
    simp [destConstants] at decoded
    subst constants
    exact .nil
  | cons expression expressions ih =>
    cases first : destConstant expression with
    | none => simp [destConstants, first] at decoded
    | some constant =>
      cases rest : destConstants expressions with
      | none => simp [destConstants, first, rest] at decoded
      | some constants' =>
        simp [destConstants, first, rest] at decoded
        subst constants
        exact .cons first (ih constants' rest)

/-- A recognized closure constant evaluates to its constant value without
changing the state. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "dest_Constant_evaluate"
  (fmap_as_finite_support := [refs, code])]
theorem destConstant_evaluate {C F : Type} (expression : ClosLang.Exp) (constant : ClosLang.Const)
    (env : List ClosSem.Value) (state : ClosSem.State C F)
    (decoded : destConstant expression = some constant) :
    ClosSem.evaluate [expression] env state = (.val [ClosSem.makeConst constant], state) := by
  rcases (destConstant_iff expression constant).mp decoded with
    ⟨_, rfl⟩ | ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;>
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.makeConst]

/-- A list of recognized constants evaluates to their values without
changing the state. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "dest_Constants_evaluate"
  (fmap_as_finite_support := [refs, code])]
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
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "evaluate_SmartCons"
  (fmap_as_finite_support := [refs, code])]
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
