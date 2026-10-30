import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileListCase

/-! Nonempty let-binding case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- Nonempty let simulation from its binding and body induction hypotheses.
Untagged pending BVI evaluator correspondence review. -/
theorem simulation_let_cons {C F : Type} (first : Bvl.Exp) (rest : List Bvl.Exp)
    (body : Bvl.Exp) (env : List Value) (source : BvlSem.State (Nat × C) F)
    (bindingsIH : simulation (first :: rest) env source)
    (bodyIH : ∀ (mid : BvlSem.State (Nat × C) F) (values : List Value),
      simulation [body] (values ++ env) mid) :
    simulation [.let (first :: rest) body] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases bindingsCompile : compileListSource n (first :: rest) with ⟨bindingsCode, bindingsAux, n1⟩
  rcases bodyCompile : compileSingSource n1 body with ⟨bodyCode, bodyAux, finalName⟩
  have bodyNil : smartAppend bodyAux .nil = bodyAux := by cases bodyAux <;> rfl
  have bodyCompiled : compileListSource n1 [body] = ([bodyCode], bodyAux, finalName) := by
    simp [compileListSource, bodyCompile, bodyNil]
  simp [compileListSource, compileSingSource, bindingsCompile, bodyCompile] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have pieces : auxCodeInstalled (appListAppend bindingsAux) target.code ∧
      auxCodeInstalled (appListAppend bodyAux) target.code := by
    apply auxCodeInstalled_append
    simpa only [appListAppend_smartAppend,
      show appListAppend (.nil : AppList (Nat × Nat × Bvi.Exp)) = [] from rfl,
      List.append_nil] using installed
  have shape : BvlHandle.Proofs.handleOk (first :: rest) ∧ BvlHandle.Proofs.handleOk [body] := by
    cases body <;> simpa [BvlHandle.Proofs.handleOk] using handlers
  cases bindingsRun : BvlSem.evaluate (first :: rest) env source with
  | mk bindingsResult mid =>
    have sourceGrowth := BvlProps.evaluateRefsSubset (first :: rest) env source mid bindingsResult bindingsRun
    have sourcePreserved := evaluateOk (first :: rest) env source bindingsResult mid bindingsRun sourceOk envOk
    rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, bindingsRun] at run
    cases bindingsResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        bindingsIH n (.err error) next target n1 bindingsCode bindingsAux relocate bindingsRun notTypeError
          bindingsCompile related sourceOk envOk pieces.1 shape.1 global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
      cases error <;> rfl
    | val values =>
      have bodyRun : BvlSem.evaluate [body] (values ++ env) mid = (res, next) := run
      obtain ⟨targetMid, midRelocate, bindingsClock, targetBindings, relatedMid, envMidEq, refsMidEq⟩ :=
        bindingsIH n (.val values) mid target n1 bindingsCode bindingsAux relocate bindingsRun (by simp)
          bindingsCompile related sourceOk envOk pieces.1 shape.1 global
      have targetCodeGrowth := BviProps.evaluate_code_mono bindingsCode (env.map (adjustBv midRelocate))
        (BviProps.incClock bindingsClock target) targetMid (.val (values.map (adjustBv midRelocate))) (by
          simpa [mapSimulationResult] using targetBindings)
      have targetGlobal := BviProps.evaluate_global_mono bindingsCode (env.map (adjustBv midRelocate))
        (BviProps.incClock bindingsClock target) targetMid (.val (values.map (adjustBv midRelocate))) (by
          simpa [mapSimulationResult] using targetBindings) (by simpa [BviProps.incClock] using global)
      have bodyInstalled : auxCodeInstalled (appListAppend bodyAux) targetMid.code := by
        apply auxCodeInstalled_subspt _ target.code targetMid.code pieces.2
        simpa [BviProps.incClock] using targetCodeGrowth
      have extendedOk : bvOkList mid.refs (values ++ env) := by
        apply (bvOkList_iff _ _).2
        intro value member
        rcases List.mem_append.mp member with bound | old
        · exact (bvOkList_iff _ _).1 sourcePreserved.2.1 value bound
        · exact (bvOkList_iff _ _).1 sourcePreserved.2.2 value old
      obtain ⟨targetFinal, finalRelocate, bodyClock, targetBody, relatedFinal, extendedEq, refsFinalEq⟩ :=
        bodyIH mid values n1 res next targetMid finalName [bodyCode] bodyAux midRelocate bodyRun notTypeError
          bodyCompiled relatedMid sourcePreserved.1 extendedOk bodyInstalled shape.2 targetGlobal
      have valuesEq := adjustMap_eq_of_ok midRelocate finalRelocate values mid.refs sourcePreserved.2.1 refsFinalEq
      have envFinalEq : env.map (adjustBv midRelocate) = env.map (adjustBv finalRelocate) := by
        simp only [List.map_append] at extendedEq
        rw [valuesEq] at extendedEq
        exact List.append_cancel_left extendedEq
      have shiftedBindings := BviProps.evaluate_inv_clock bindingsCode (env.map (adjustBv midRelocate))
        (BviProps.incClock bindingsClock target) targetMid (.val (values.map (adjustBv midRelocate))) bodyClock
        (by simpa [mapSimulationResult] using targetBindings) (by simp)
      rw [BviProps.incClock_add, envFinalEq, valuesEq] at shiftedBindings
      have refsEq : ∀ key, source.refs.lookup key ≠ none → relocate key = finalRelocate key := by
        intro key present
        exact (refsMidEq key present).trans (refsFinalEq key (sourceGrowth key present))
      refine ⟨targetFinal, finalRelocate, bodyClock + bindingsClock, ?_, relatedFinal,
        envMidEq.trans envFinalEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, shiftedBindings]
      simpa [List.map_append] using targetBody

/-- Variable bindings and a variable body are an instance of the let simulation. -/
theorem simulation_let_vars {C F : Type} (first : Nat) (rest : List Nat) (body : Nat)
    (env : List Value) (source : BvlSem.State (Nat × C) F) :
    simulation [.let ((first :: rest).map Bvl.Exp.var) (.var body)] env source := by
  apply simulation_let_cons (.var first) (rest.map Bvl.Exp.var) (.var body) env source
  · exact simulation_vars (first :: rest) env source
  · intro mid values
    exact simulation_var body (values ++ env) mid

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
