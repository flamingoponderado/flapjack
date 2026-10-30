import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxCall

/-! Empty let-binding case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

private theorem handleOk_varList (xs : List Bvl.Exp) (onlyVars : xs.all BvlProps.isVar = true) :
    BvlHandle.Proofs.handleOk xs := by
  rw [BvlHandle.Proofs.handleOk_every]
  intro expression member
  have isVariable := (List.all_eq_true.mp onlyVars) expression member
  cases expression <;> simp_all [BvlProps.isVar, BvlHandle.Proofs.handleOk]

/-- Empty let simulation for the source's variable-only, bounded inner let.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_let_empty {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (bindingsIH : simulation bindings env source)
    (bodyIH : ∀ values : List Value, simulation [body] values source) :
    simulation [.let [] (.let bindings body)] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases bindingsCompile : compileListSource n bindings with ⟨bindingsCode, bindingsAux, n1⟩
  rcases bodyCompile : compileSingSource n1 body with ⟨bodyCode, bodyAux, finalName⟩
  have bodyNil : smartAppend bodyAux .nil = bodyAux := by cases bodyAux <;> rfl
  have bodyCompiled : compileListSource n1 [body] = ([bodyCode], bodyAux, finalName) := by
    simp [compileListSource, bodyCompile, bodyNil]
  simp [compileListSource, compileSingSource, destLet, bindingsCompile, bodyCompile] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have pieces : auxCodeInstalled (appListAppend bindingsAux) target.code ∧
      auxCodeInstalled (appListAppend bodyAux) target.code ∧
      sptLookup (bvlNumStubs + bvlToBviNamespaces * finalName + 1) target.code =
        some (bindings.length, BviLet.compileSing [] 0 bodyCode) := by
    simp only [appListAppend_smartAppend, compileAuxSource,
      show appListAppend (.list [(bvlNumStubs + bvlToBviNamespaces * finalName + 1,
        bindings.length, BviLet.compileSing [] 0 bodyCode)]) =
          [(bvlNumStubs + bvlToBviNamespaces * finalName + 1,
            bindings.length, BviLet.compileSing [] 0 bodyCode)] from rfl,
      show appListAppend (.nil : AppList (Nat × Nat × Bvi.Exp)) = [] from rfl,
      List.append_nil] at installed
    have both := auxCodeInstalled_append _ _ target.code installed
    have components := auxCodeInstalled_append _ _ target.code both.1
    exact ⟨components.1, components.2, both.2.1⟩
  have shape : bindings.all BvlProps.isVar = true ∧
      BvlProps.bVarBound bindings.length [body] ∧ BvlHandle.Proofs.handleOk [body] := by
    simpa [BvlHandle.Proofs.handleOk, BvlHandle.Proofs.letOk, and_assoc] using handlers
  have innerRun : BvlSem.evaluate [.let bindings body] env source = (res, next) := by
    simpa [BvlSem.evaluate, BvlSem.fixClock] using run
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate] at innerRun
  cases bindingsRun : BvlSem.evaluate bindings env source with
  | mk bindingsResult mid =>
    cases bindingsResult with
    | err error =>
      simp only [bindingsRun] at innerRun
      rcases innerRun with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        bindingsIH n (.err error) next target n1 bindingsCode bindingsAux relocate bindingsRun notTypeError
          bindingsCompile related sourceOk envOk pieces.1 (handleOk_varList bindings shape.1) global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetRun]
      cases error <;> rfl
    | val values =>
      have unchanged := (evaluate_varList_members bindings env source mid values shape.1 bindingsRun).2
      subst mid
      have valuesLength := BvlSem.evaluate_length bindings env source source values bindingsRun
      have bodyRunExtended : BvlSem.evaluate [body] (values ++ env) source = (res, next) := by
        simpa only [bindingsRun] using innerRun
      have bodyBound : BvlProps.bVarBound values.length [body] := by simpa [valuesLength] using shape.2.1
      have bodyRun : BvlSem.evaluate [body] values source = (res, next) := by
        rw [← evaluate_bVarBound [body] values env source bodyBound]
        exact bodyRunExtended
      obtain ⟨targetMid, midRelocate, bindingsClock, targetBindings, relatedMid, envMidEq, refsMidEq⟩ :=
        bindingsIH n (.val values) source target n1 bindingsCode bindingsAux relocate bindingsRun (by simp)
          bindingsCompile related sourceOk envOk pieces.1 (handleOk_varList bindings shape.1) global
      have targetCodeGrowth := BviProps.evaluate_code_mono bindingsCode (env.map (adjustBv midRelocate))
        (BviProps.incClock bindingsClock target) targetMid (.val (values.map (adjustBv midRelocate))) (by
          simpa [mapSimulationResult] using targetBindings)
      have targetGlobal := BviProps.evaluate_global_mono bindingsCode (env.map (adjustBv midRelocate))
        (BviProps.incClock bindingsClock target) targetMid (.val (values.map (adjustBv midRelocate))) (by
          simpa [mapSimulationResult] using targetBindings) (by simpa [BviProps.incClock] using global)
      have bodyInstalled : auxCodeInstalled (appListAppend bodyAux) targetMid.code := by
        apply auxCodeInstalled_subspt _ target.code targetMid.code pieces.2.1
        simpa [BviProps.incClock] using targetCodeGrowth
      have auxInstalled : sptLookup (bvlNumStubs + bvlToBviNamespaces * finalName + 1) targetMid.code =
          some (bindings.length, BviLet.compileSing [] 0 bodyCode) := by
        have member : sptMem (bvlNumStubs + bvlToBviNamespaces * finalName + 1) target.code :=
          (sptMem_iff_lookup _ _).2 ⟨_, pieces.2.2⟩
        exact (targetCodeGrowth _ member).2.trans pieces.2.2
      have valuesOk : bvOkList source.refs values := by
        have members := (evaluate_varList_members bindings env source source values shape.1 bindingsRun).1
        apply (bvOkList_iff _ _).2
        intro value member
        exact (bvOkList_iff _ _).1 envOk value (members value member)
      obtain ⟨targetFinal, finalRelocate, bodyClock, targetBody, relatedFinal, valuesEq, refsFinalEq⟩ :=
        bodyIH values n1 res next targetMid finalName [bodyCode] bodyAux midRelocate bodyRun notTypeError
          bodyCompiled relatedMid sourceOk valuesOk bodyInstalled shape.2.2 targetGlobal
      have envFinalEq := adjustMap_eq_of_ok midRelocate finalRelocate env source.refs envOk refsFinalEq
      have argsFinal : BviSem.evaluate bindingsCode (env.map (adjustBv finalRelocate))
          (BviProps.incClock bindingsClock target) = (.val (values.map (adjustBv finalRelocate)), targetMid) := by
        simpa [mapSimulationResult, envFinalEq, valuesEq] using targetBindings
      have auxRun := evaluate_aux_call bindingsCode (env.map (adjustBv finalRelocate))
        (values.map (adjustBv finalRelocate)) (BviProps.incClock bindingsClock target) targetMid targetFinal
        (bvlNumStubs + bvlToBviNamespaces * finalName + 1) bindings.length bodyClock bodyCode finalRelocate res
        argsFinal (by simpa using valuesLength) auxInstalled targetBody notTypeError
      refine ⟨targetFinal, finalRelocate, (bodyClock + 1) + bindingsClock, ?_, relatedFinal,
        envMidEq.trans envFinalEq, ?_⟩
      · simpa [BviProps.incClock_add] using auxRun
      · intro key present
        exact (refsMidEq key present).trans (refsFinalEq key present)

/-- Variable-only inner lets instantiate the empty-let simulation. -/
theorem simulation_let_empty_vars {C F : Type} (indices : List Nat) (body : Nat)
    (env : List Value) (source : BvlSem.State (Nat × C) F) :
    simulation [.let [] (.let (indices.map Bvl.Exp.var) (.var body))] env source :=
  simulation_let_empty (indices.map Bvl.Exp.var) (.var body) env source
    (simulation_vars indices env source) (fun values => simulation_var body values source)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
