import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileListCase

/-! Conditional case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Conditional simulation from its condition and branch induction
hypotheses. Untagged pending BVI evaluator correspondence review. -/
theorem simulation_if {C F : Type} (condition yes no : Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F)
    (conditionIH : simulation [condition] env source)
    (yesIH : ∀ mid : BvlSem.State (Nat × C) F, mid.clock ≤ source.clock → simulation [yes] env mid)
    (noIH : ∀ mid : BvlSem.State (Nat × C) F, mid.clock ≤ source.clock → simulation [no] env mid) :
    simulation [.ifThenElse condition yes no] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases conditionCompile : compileSingSource n condition with ⟨conditionCode, conditionAux, n1⟩
  rcases yesCompile : compileSingSource n1 yes with ⟨yesCode, yesAux, nYes⟩
  rcases noCompile : compileSingSource nYes no with ⟨noCode, noAux, finalName⟩
  have conditionNil : smartAppend conditionAux .nil = conditionAux := by cases conditionAux <;> rfl
  have yesNil : smartAppend yesAux .nil = yesAux := by cases yesAux <;> rfl
  have noNil : smartAppend noAux .nil = noAux := by cases noAux <;> rfl
  have conditionCompiled : compileListSource n [condition] = ([conditionCode], conditionAux, n1) := by
    simp [compileListSource, conditionCompile, conditionNil]
  have yesCompiled : compileListSource n1 [yes] = ([yesCode], yesAux, nYes) := by
    simp [compileListSource, yesCompile, yesNil]
  have noCompiled : compileListSource nYes [no] = ([noCode], noAux, finalName) := by
    simp [compileListSource, noCompile, noNil]
  simp [compileListSource, compileSingSource, conditionCompile, yesCompile, noCompile] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have parts : auxCodeInstalled (appListAppend conditionAux) target.code ∧
      auxCodeInstalled (appListAppend yesAux) target.code ∧
      auxCodeInstalled (appListAppend noAux) target.code := by
    have first : auxCodeInstalled (appListAppend (smartAppend conditionAux yesAux)) target.code ∧
        auxCodeInstalled (appListAppend noAux) target.code := by
      apply auxCodeInstalled_append
      simpa only [appListAppend_smartAppend,
        show appListAppend (.nil : AppList (Nat × Nat × Bvi.Exp)) = [] from rfl,
        List.append_nil] using installed
    have second : auxCodeInstalled (appListAppend conditionAux) target.code ∧
        auxCodeInstalled (appListAppend yesAux) target.code := by
      apply auxCodeInstalled_append
      simpa [appListAppend_smartAppend] using first.1
    exact ⟨second.1, second.2, first.2⟩
  have shape : BvlHandle.Proofs.handleOk [condition] ∧ BvlHandle.Proofs.handleOk [yes] ∧
      BvlHandle.Proofs.handleOk [no] := by
    simpa [BvlHandle.Proofs.handleOk] using handlers
  cases conditionRun : BvlSem.evaluate [condition] env source with
  | mk conditionResult mid =>
    have sourceGrowth := BvlProps.evaluateRefsSubset [condition] env source mid conditionResult conditionRun
    have sourcePreserved := evaluateOk [condition] env source conditionResult mid conditionRun sourceOk envOk
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, conditionRun] at run
    cases conditionResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        conditionIH n (.err error) next target n1 [conditionCode] conditionAux relocate conditionRun notTypeError
          conditionCompiled related sourceOk envOk parts.1 shape.1 global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
      cases error <;> rfl
    | val values =>
      obtain ⟨conditionValue, rfl⟩ := BvlSem.evaluate_singleton condition env source mid values conditionRun
      cases bool : BvlSem.asBool conditionValue with
      | none =>
        simp [bool] at run
        exact (notTypeError run.1.symm).elim
      | some choice =>
        obtain ⟨targetMid, midRelocate, conditionClock, targetCondition, relatedMid, envMidEq, refsMidEq⟩ :=
          conditionIH n (.val [conditionValue]) mid target n1 [conditionCode] conditionAux relocate conditionRun (by simp)
            conditionCompiled related sourceOk envOk parts.1 shape.1 global
        have targetCodeGrowth := BviProps.evaluate_code_mono [conditionCode] (env.map (adjustBv midRelocate))
          (BviProps.incClock conditionClock target) targetMid (.val [adjustBv midRelocate conditionValue]) (by
            simpa [mapSimulationResult] using targetCondition)
        have targetGlobal := BviProps.evaluate_global_mono [conditionCode] (env.map (adjustBv midRelocate))
          (BviProps.incClock conditionClock target) targetMid (.val [adjustBv midRelocate conditionValue]) (by
            simpa [mapSimulationResult] using targetCondition) (by simpa [BviProps.incClock] using global)
        have yesInstalled : auxCodeInstalled (appListAppend yesAux) targetMid.code := by
          apply auxCodeInstalled_subspt _ target.code targetMid.code parts.2.1
          simpa [BviProps.incClock] using targetCodeGrowth
        have noInstalled : auxCodeInstalled (appListAppend noAux) targetMid.code := by
          apply auxCodeInstalled_subspt _ target.code targetMid.code parts.2.2
          simpa [BviProps.incClock] using targetCodeGrowth
        have runBranch (branch : Bvl.Exp) (branchCode : Bvi.Exp)
            (branchAux : AppList (Nat × Nat × Bvi.Exp)) (startName endName : Nat)
            (branchIH : simulation [branch] env mid)
            (branchRun : BvlSem.evaluate [branch] env mid = (res, next))
            (branchCompiled : compileListSource startName [branch] = ([branchCode], branchAux, endName))
            (branchInstalled : auxCodeInstalled (appListAppend branchAux) targetMid.code)
            (branchShape : BvlHandle.Proofs.handleOk [branch])
            (branchCodeEq : branchCode = if choice then yesCode else noCode) :
            ∃ targetNext newRelocate clock,
              BviSem.evaluate [.ifThenElse conditionCode yesCode noCode]
                  (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
                (mapSimulationResult newRelocate res, targetNext) ∧
              stateRel newRelocate next targetNext ∧
              env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
              ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
          obtain ⟨targetFinal, finalRelocate, branchClock, targetBranch, relatedFinal, envFinalEq, refsFinalEq⟩ :=
            branchIH startName res next targetMid endName [branchCode] branchAux midRelocate branchRun notTypeError
              branchCompiled relatedMid sourcePreserved.1 sourcePreserved.2.2 branchInstalled branchShape targetGlobal
          have shiftedCondition := BviProps.evaluate_inv_clock [conditionCode]
            (env.map (adjustBv midRelocate)) (BviProps.incClock conditionClock target)
            targetMid (.val [adjustBv midRelocate conditionValue]) branchClock
            (by simpa [mapSimulationResult] using targetCondition) (by simp)
          rw [BviProps.incClock_add, envFinalEq] at shiftedCondition
          have refsEq : ∀ key, source.refs.lookup key ≠ none → relocate key = finalRelocate key := by
            intro key present
            exact (refsMidEq key present).trans (refsFinalEq key (sourceGrowth key present))
          refine ⟨targetFinal, finalRelocate, branchClock + conditionClock, ?_, relatedFinal,
            envMidEq.trans envFinalEq, refsEq⟩
          rw [BviSem.evaluate, BviSem.fixClock_evaluate, shiftedCondition]
          change (match BvlSem.asBool (adjustBv midRelocate conditionValue) with
            | none => ((.err (.abort .typeError) : BviSem.BviResult), BviProps.incClock branchClock targetMid)
            | some true => BviSem.evaluate [yesCode] (env.map (adjustBv finalRelocate))
                (BviProps.incClock branchClock targetMid)
            | some false => BviSem.evaluate [noCode] (env.map (adjustBv finalRelocate))
                (BviProps.incClock branchClock targetMid)) = _
          cases choice <;> simpa [asBool_adjustBv, bool, branchCodeEq] using targetBranch
        have midClock : mid.clock ≤ source.clock := by
          have clockBound := BvlSem.evaluate_clock_le [condition] env source
          simpa [conditionRun] using clockBound
        cases choice with
        | false =>
          have branchRun : BvlSem.evaluate [no] env mid = (res, next) := by simpa [bool] using run
          exact runBranch no noCode noAux nYes finalName (noIH mid midClock) branchRun noCompiled noInstalled shape.2.2 (by rfl)
        | true =>
          have branchRun : BvlSem.evaluate [yes] env mid = (res, next) := by simpa [bool] using run
          exact runBranch yes yesCode yesAux n1 nYes (yesIH mid midClock) branchRun yesCompiled yesInstalled shape.2.1 (by rfl)

/-- Flapjack consequence: a conditional whose condition and branches are
variables satisfies the simulation for any environment and source state. -/
theorem simulation_if_vars {C F : Type} (condition yes no : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) :
    simulation [.ifThenElse (.var condition) (.var yes) (.var no)] env source :=
  simulation_if (.var condition) (.var yes) (.var no) env source
    (simulation_var condition env source) (fun mid _ => simulation_var yes env mid)
    (fun mid _ => simulation_var no env mid)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
