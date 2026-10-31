import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileCases
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.EvaluateAllOk
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.RelocationOk
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateGrowth
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift

/-! Non-singleton expression-list case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Sequential expression-list case, using the original head and tail
induction hypotheses. Untagged pending BVI evaluator correspondence review. -/
theorem simulation_cons {C F : Type} (first second : Bvl.Exp) (rest : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (headIH : simulation [first] env source)
    (tailIH : ∀ mid : BvlSem.State (Nat × C) F, mid.clock ≤ source.clock → simulation (second :: rest) env mid) :
    simulation (first :: second :: rest) env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases headCompile : compileSingSource n first with ⟨headCode, headAux, n1⟩
  rcases tailCompile : compileListSource n1 (second :: rest) with ⟨tailCode, tailAux, finalName⟩
  have nilRight : smartAppend headAux .nil = headAux := by cases headAux <;> rfl
  have headCompiled : compileListSource n [first] = ([headCode], headAux, n1) := by
    simp [compileListSource, headCompile, nilRight]
  simp [compileListSource, headCompile, tailCompile] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have pieces : auxCodeInstalled (appListAppend headAux) target.code ∧
      auxCodeInstalled (appListAppend tailAux) target.code := by
    apply auxCodeInstalled_append
    simpa [appListAppend_smartAppend] using installed
  have shape : BvlHandle.Proofs.handleOk [first] ∧ BvlHandle.Proofs.handleOk (second :: rest) := by
    simpa [BvlHandle.Proofs.handleOk] using handlers
  cases headRun : BvlSem.evaluate [first] env source with
  | mk headResult mid =>
    have sourceGrowth := BvlProps.evaluateRefsSubset [first] env source mid headResult headRun
    have sourcePreserved := evaluateOk [first] env source headResult mid headRun sourceOk envOk
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, headRun] at run
    cases headResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        headIH n (.err error) next target n1 [headCode] headAux relocate headRun notTypeError
          headCompiled related sourceOk envOk pieces.1 shape.1 global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      change BviSem.evaluateTuple (headCode :: tailCode, env.map (adjustBv newRelocate),
        BviProps.incClock clock target) = _
      rw [BviSem.evaluateCons]
      change BviSem.evaluateTuple ([headCode], env.map (adjustBv newRelocate),
        BviProps.incClock clock target) = _ at targetRun
      rw [targetRun]
      cases error <;> rfl
    | val headValues =>
      obtain ⟨headValue, rfl⟩ := BvlSem.evaluate_singleton first env source mid headValues headRun
      cases tailRun : BvlSem.evaluate (second :: rest) env mid with
      | mk tailResult last =>
        rw [tailRun] at run
        have tailNotType : tailResult ≠ .err (.abort .typeError) := by
          intro bad
          subst tailResult
          simp at run
          exact notTypeError run.1.symm
        obtain ⟨targetMid, midRelocate, headClock, targetHead, relatedMid, envMidEq, refsMidEq⟩ :=
          headIH n (.val [headValue]) mid target n1 [headCode] headAux relocate headRun (by simp)
            headCompiled related sourceOk envOk pieces.1 shape.1 global
        have targetCodeGrowth := BviProps.evaluate_code_mono [headCode] (env.map (adjustBv midRelocate))
          (BviProps.incClock headClock target) targetMid (.val [adjustBv midRelocate headValue]) (by
            simpa [mapSimulationResult] using targetHead)
        have targetGlobal := BviProps.evaluate_global_mono [headCode] (env.map (adjustBv midRelocate))
          (BviProps.incClock headClock target) targetMid (.val [adjustBv midRelocate headValue]) (by
            simpa [mapSimulationResult] using targetHead) (by simpa [BviProps.incClock] using global)
        have tailInstalled : auxCodeInstalled (appListAppend tailAux) targetMid.code := by
          apply auxCodeInstalled_subspt _ target.code targetMid.code pieces.2
          simpa [BviProps.incClock] using targetCodeGrowth
        have midClock : mid.clock ≤ source.clock := by
          have clockBound := BvlSem.evaluate_clock_le [first] env source
          simpa [headRun] using clockBound
        obtain ⟨targetFinal, finalRelocate, tailClock, targetTail, relatedFinal, envFinalEq, refsFinalEq⟩ :=
          tailIH mid midClock n1 tailResult last targetMid finalName tailCode tailAux midRelocate tailRun tailNotType
            tailCompile relatedMid sourcePreserved.1 sourcePreserved.2.2 tailInstalled shape.2 targetGlobal
        have headValueOk : bvOk mid.refs headValue := by
          simpa [bvOkList] using sourcePreserved.2.1
        have headRelocated := adjustBv_eq_of_ok midRelocate headValue finalRelocate mid.refs
          headValueOk refsFinalEq
        have shiftedHead := BviProps.evaluate_inv_clock [headCode] (env.map (adjustBv midRelocate))
          (BviProps.incClock headClock target) targetMid (.val [adjustBv midRelocate headValue]) tailClock
          (by simpa [mapSimulationResult] using targetHead) (by simp)
        rw [BviProps.incClock_add, envFinalEq, headRelocated] at shiftedHead
        have refsEq : ∀ key, source.refs.lookup key ≠ none → relocate key = finalRelocate key := by
          intro key present
          exact (refsMidEq key present).trans (refsFinalEq key (sourceGrowth key present))
        change BviSem.evaluateTuple ([headCode], env.map (adjustBv finalRelocate),
          BviProps.incClock (tailClock + headClock) target) = _ at shiftedHead
        change BviSem.evaluateTuple (tailCode, env.map (adjustBv finalRelocate),
          BviProps.incClock tailClock targetMid) = _ at targetTail
        cases tailResult with
        | err error =>
          simp only at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨targetFinal, finalRelocate, tailClock + headClock, ?_, relatedFinal,
            envMidEq.trans envFinalEq, refsEq⟩
          change BviSem.evaluateTuple (headCode :: tailCode, env.map (adjustBv finalRelocate),
            BviProps.incClock (tailClock + headClock) target) = _
          rw [BviSem.evaluateCons, shiftedHead]
          dsimp only
          rw [targetTail]
          cases error <;> rfl
        | val tailValues =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨targetFinal, finalRelocate, tailClock + headClock, ?_, relatedFinal,
            envMidEq.trans envFinalEq, refsEq⟩
          change BviSem.evaluateTuple (headCode :: tailCode, env.map (adjustBv finalRelocate),
            BviProps.incClock (tailClock + headClock) target) = _
          rw [BviSem.evaluateCons, shiftedHead]
          dsimp only
          rw [targetTail]
          simp [mapSimulationResult, Flapjack.holHd]

/-- Flapjack consequence: any list of variables satisfies the simulation,
including intermediate errors and changes of the relocation map. -/
theorem simulation_vars {C F : Type} (indices : List Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) :
    simulation (indices.map Bvl.Exp.var) env source := by
  induction indices generalizing source with
  | nil => exact simulation_nil env source
  | cons index indices ih =>
    cases indices with
    | nil => exact simulation_var index env source
    | cons second rest =>
      simpa using simulation_cons (.var index) (.var second) (rest.map Bvl.Exp.var) env source
        (simulation_var index env source) (fun mid _ => ih mid)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
