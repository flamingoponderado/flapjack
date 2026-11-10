module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.OperatorCorrectness
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.ErrorPropagation

import all Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateExact

@[expose] public section

namespace Flapjack.Compiler.Backend.FlatToClos

open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The App case of HOL `compile_correct`: a proved operator theorem and
argument simulation imply expression simulation when `destNop` returns none.
This is proof infrastructure, not a separate HOL declaration. -/
theorem evalSim_app_of_op {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (noNop : destNop op args = none)
    (notApp : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (opCorrect : ∀ (s : FlatSem.State C F) vs s' result (t' : ClosSem.State C F)
      xs db t ws tt,
      FlatSem.doApp s op vs = some (s', result) ∧ StateRel s t' ∧
      ClosSem.evaluate xs db t = (.val ws, t') ∧ List.Forall₂ ValueRel vs ws.reverse ∧
      xs.length = vs.length ∧ op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
      ∃ targetResult targetLast,
        ClosSem.evaluate [compileOp tt op xs] db t = (targetResult, targetLast) ∧
        StateRel s' targetLast ∧
        SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
          (Flapjack.EvaluateHOL.listResult result) targetResult)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace op args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace op args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps, compileExp] at ⊢
  split
  next x h => rw [noNop] at h; contradiction
  next h =>
    rw [FlatSem.evaluate]
    simp only [flatFix]
    cases flatRun : FlatSem.evaluate env source args.reverse with
    | mk next flatResult =>
      cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
      | mk closResult nextTarget =>
        simp only [flatRun, closRun] at argsSim
        rcases argsSim with ⟨states, results⟩
        cases results with
        | abort error =>
          have run := compileOp_evaluates_args _ _ _ _ _ _ trace ⟨closRun, notApp, notEval, notForce⟩
          rw [run]
          exact ⟨states, .abort error⟩
        | raise related =>
          have run := compileOp_evaluates_args _ _ _ _ _ _ trace ⟨closRun, notApp, notEval, notForce⟩
          rw [run]
          exact ⟨states, .raise related⟩
        | value related =>
          rename_i sourceArgs targetArgs
          cases applied : FlatSem.doApp next op sourceArgs.reverse with
          | none =>
            have h := notTypeError
            rw [FlatSem.evaluate, flatFix, flatRun] at h
            simp [FlatSem.applyResult, FlatSem.typeError, applied] at h
          | some pair =>
            obtain ⟨sourceNext, result⟩ := pair
            have length := FlatSem.evaluate_length env source next args.reverse sourceArgs flatRun
            have lengthEq : (compileExps names args).reverse.length = sourceArgs.reverse.length := by
              have compiledLength : ∀ xs, (compileExps names xs).length = xs.length := by
                intro xs
                induction xs with
                | nil => simp [compileExps]
                | cons x xs ih => simp [compileExps, ih]
              simpa [compiledLength] using length.symm
            have reversed : List.Forall₂ ValueRel sourceArgs.reverse targetArgs.reverse := List.rel_reverse related
            obtain ⟨out, last, run, stateRel, resultRel⟩ :=
              opCorrect next sourceArgs.reverse sourceNext result nextTarget
                (compileExps names args).reverse values target targetArgs trace
                ⟨applied, states, closRun, reversed, lengthEq, notApp, notForce⟩
            simp only [FlatSem.applyResult, applied]
            rw [run]
            cases result with
            | val value =>
              simp [Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel] at resultRel
              cases out <;> simp_all [SemanticPrimitivesProps.resultRel]
              exact .value resultRel
            | err error =>
              cases error <;> cases out <;>
                simp_all [Flapjack.EvaluateHOL.listResult, SemanticPrimitivesProps.resultRel,
                  SemanticPrimitivesProps.excRel]
              all_goals rename_i sourceError targetError
              all_goals cases targetError <;> simp_all
              all_goals first | exact .raise resultRel | exact .abort _
end Flapjack.Compiler.Backend.FlatToClos
