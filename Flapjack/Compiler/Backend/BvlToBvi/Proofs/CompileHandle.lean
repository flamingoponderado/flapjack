import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AuxHandle

/-! Exception-handler case of BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result)

private theorem handleOk_varList (xs : List Bvl.Exp) (onlyVars : xs.all BvlProps.isVar = true) :
    BvlHandle.Proofs.handleOk xs := by
  rw [BvlHandle.Proofs.handleOk_every]
  intro expression member
  have isVariable := (List.all_eq_true.mp onlyVars) expression member
  cases expression <;> simp_all [BvlProps.isVar, BvlHandle.Proofs.handleOk]

/-- Handler simulation for a variable-only, bounded protected let.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_handle {C F : Type} (bindings : List Bvl.Exp) (body handler : Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (bindingsIH : simulation bindings env source)
    (bodyIH : ∀ values : List Value, simulation [body] values source)
    (handlerIH : ∀ (exception : Value) (mid : BvlSem.State (Nat × C) F),
      mid.clock ≤ source.clock → simulation [handler] (exception :: env) mid) :
    simulation [.handle (.let bindings body) handler] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases bindingsCompile : compileListSource n bindings with ⟨bindingsCode, bindingsAux, n1⟩
  rcases bodyCompile : compileSingSource n1 body with ⟨bodyCode, bodyAux, nBody⟩
  rcases handlerCompile : compileSingSource nBody handler with ⟨handlerCode, handlerAux, finalName⟩
  have bodyNil : smartAppend bodyAux .nil = bodyAux := by cases bodyAux <;> rfl
  have handlerNil : smartAppend handlerAux .nil = handlerAux := by cases handlerAux <;> rfl
  have bodyCompiled : compileListSource n1 [body] = ([bodyCode], bodyAux, nBody) := by
    simp [compileListSource, bodyCompile, bodyNil]
  have handlerCompiled : compileListSource nBody [handler] = ([handlerCode], handlerAux, finalName) := by
    simp [compileListSource, handlerCompile, handlerNil]
  simp [compileListSource, compileSingSource, destLet, bindingsCompile, bodyCompile, handlerCompile] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have pieces : auxCodeInstalled (appListAppend bindingsAux) target.code ∧
      auxCodeInstalled (appListAppend bodyAux) target.code ∧
      auxCodeInstalled (appListAppend handlerAux) target.code ∧
      sptLookup (bvlNumStubs + bvlToBviNamespaces * finalName + 1) target.code =
        some (bindings.length, BviLet.compileSing [] 0 bodyCode) := by
    simp only [appListAppend_smartAppend, compileAuxSource,
      show appListAppend (.list [(bvlNumStubs + bvlToBviNamespaces * finalName + 1,
        bindings.length, BviLet.compileSing [] 0 bodyCode)]) =
          [(bvlNumStubs + bvlToBviNamespaces * finalName + 1,
            bindings.length, BviLet.compileSing [] 0 bodyCode)] from rfl,
      show appListAppend (.nil : AppList (Nat × Nat × Bvi.Exp)) = [] from rfl,
      List.append_nil] at installed
    have all := auxCodeInstalled_append _ _ target.code installed
    have earlier := auxCodeInstalled_append _ _ target.code all.1
    have pair := auxCodeInstalled_append _ _ target.code earlier.1
    exact ⟨pair.1, pair.2, earlier.2, all.2.1⟩
  have shape : bindings.all BvlProps.isVar = true ∧ BvlProps.bVarBound bindings.length [body] ∧
      BvlHandle.Proofs.handleOk [body] ∧ BvlHandle.Proofs.handleOk [handler] := by
    simpa [BvlHandle.Proofs.handleOk, and_assoc] using handlers
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, BvlSem.evaluate, BvlSem.fixClock_evaluate] at run
  cases bindingsRun : BvlSem.evaluate bindings env source with
  | mk bindingsResult mid =>
    cases bindingsResult with
    | err error =>
      have bad := evaluate_varList_error bindings env source mid error shape.1 bindingsRun
      rcases bad with ⟨rfl, rfl⟩
      simp [bindingsRun] at run
      exact (notTypeError run.1.symm).elim
    | val values =>
      have unchanged := (evaluate_varList_members bindings env source mid values shape.1 bindingsRun).2
      subst mid
      have valuesLength := BvlSem.evaluate_length bindings env source source values bindingsRun
      have bodyBound : BvlProps.bVarBound values.length [body] := by simpa [valuesLength] using shape.2.1
      rw [bindingsRun] at run
      dsimp only at run
      rw [evaluate_bVarBound [body] values env source bodyBound] at run
      cases bodyRun : BvlSem.evaluate [body] values source with
      | mk bodyResult bodyMid =>
        have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bodyResult
          simp [bodyRun] at run
          exact notTypeError run.1.symm
        have valuesOk : bvOkList source.refs values := by
          have members := (evaluate_varList_members bindings env source source values shape.1 bindingsRun).1
          apply (bvOkList_iff _ _).2
          intro value member
          exact (bvOkList_iff _ _).1 envOk value (members value member)
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
            (sptMem_iff_lookup _ _).2 ⟨_, pieces.2.2.2⟩
          exact (targetCodeGrowth _ member).2.trans pieces.2.2.2
        obtain ⟨targetBody, bodyRelocate, bodyClock, targetBodyRun, relatedBody, valuesEq, refsBodyEq⟩ :=
          bodyIH values n1 bodyResult bodyMid targetMid nBody [bodyCode] bodyAux midRelocate bodyRun bodyNotType
            bodyCompiled relatedMid sourceOk valuesOk bodyInstalled shape.2.2.1 targetGlobal
        have envBodyEq := adjustMap_eq_of_ok midRelocate bodyRelocate env source.refs envOk refsBodyEq
        have finishNoRaise (same : (res, next) = (bodyResult, bodyMid))
            (noRaise : ∀ value, bodyResult ≠ .err (.raise value)) :
            ∃ targetNext newRelocate clock,
              BviSem.evaluate [.call 0 (some (bvlNumStubs + bvlToBviNamespaces * finalName + 1))
                  bindingsCode (some handlerCode)] (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
                (mapSimulationResult newRelocate res, targetNext) ∧
              stateRel newRelocate next targetNext ∧
              env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
              ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
          have ⟨resultEq, stateEq⟩ := Prod.mk.inj same
          rw [resultEq, stateEq]
          have argsFinal : BviSem.evaluate bindingsCode (env.map (adjustBv bodyRelocate))
              (BviProps.incClock bindingsClock target) = (.val (values.map (adjustBv bodyRelocate)), targetMid) := by
            simpa [mapSimulationResult, envBodyEq, valuesEq] using targetBindings
          have auxRun := evaluate_aux_call_handle_noRaise bindingsCode (env.map (adjustBv bodyRelocate))
            (values.map (adjustBv bodyRelocate)) (BviProps.incClock bindingsClock target) targetMid targetBody
            (bvlNumStubs + bvlToBviNamespaces * finalName + 1) bindings.length bodyClock bodyCode handlerCode
            bodyRelocate bodyResult argsFinal (by simpa using valuesLength) auxInstalled targetBodyRun bodyNotType noRaise
          refine ⟨targetBody, bodyRelocate, (bodyClock + 1) + bindingsClock, ?_, relatedBody,
            envMidEq.trans envBodyEq, ?_⟩
          · simpa [BviProps.incClock_add] using auxRun
          · intro key present
            exact (refsMidEq key present).trans (refsBodyEq key present)
        cases bodyResult with
        | val resultValues =>
          simp [bodyRun] at run
          exact finishNoRaise (by rw [run.1, run.2]) (by simp)
        | err error =>
          cases error with
          | abort reason =>
            simp [bodyRun] at run
            exact finishNoRaise (by rw [run.1, run.2]) (by simp)
          | raise exception =>
            have handlerRun : BvlSem.evaluate [handler] (exception :: env) bodyMid = (res, next) := by
              simpa [bodyRun] using run
            have sourceGrowth := BvlProps.evaluateRefsSubset [body] values source bodyMid
              (.err (.raise exception)) bodyRun
            have preserved := evaluateOk [body] values source (.err (.raise exception)) bodyMid
              bodyRun sourceOk valuesOk
            have envBodyOk := bvOkList_domain_mono source.refs env bodyMid.refs envOk sourceGrowth
            have handlerEnvOk : bvOkList bodyMid.refs (exception :: env) := by
              simpa [bvOkList] using And.intro preserved.2.1 envBodyOk
            have targetBodyGrowth := BviProps.evaluate_code_mono [bodyCode]
              (values.map (adjustBv bodyRelocate)) (BviProps.incClock bodyClock targetMid) targetBody
              (.err (.raise (.exn (adjustBv bodyRelocate exception)))) (by
                simpa [mapSimulationResult] using targetBodyRun)
            have targetBodyGlobal := BviProps.evaluate_global_mono [bodyCode]
              (values.map (adjustBv bodyRelocate)) (BviProps.incClock bodyClock targetMid) targetBody
              (.err (.raise (.exn (adjustBv bodyRelocate exception)))) (by
                simpa [mapSimulationResult] using targetBodyRun) (by simpa [BviProps.incClock] using targetGlobal)
            have handlerInstalledMid : auxCodeInstalled (appListAppend handlerAux) targetMid.code := by
              apply auxCodeInstalled_subspt _ target.code targetMid.code pieces.2.2.1
              simpa [BviProps.incClock] using targetCodeGrowth
            have handlerInstalled : auxCodeInstalled (appListAppend handlerAux) targetBody.code := by
              apply auxCodeInstalled_subspt _ targetMid.code targetBody.code handlerInstalledMid
              simpa [BviProps.incClock] using targetBodyGrowth
            have bodyClockBound : bodyMid.clock ≤ source.clock := by
              have clockBound := BvlSem.evaluate_clock_le [body] values source
              simpa [bodyRun] using clockBound
            obtain ⟨targetFinal, finalRelocate, handlerClock, targetHandler, relatedFinal, handlerEq, refsHandlerEq⟩ :=
              handlerIH exception bodyMid bodyClockBound nBody res next targetBody finalName [handlerCode] handlerAux bodyRelocate
                handlerRun notTypeError handlerCompiled relatedBody preserved.1 handlerEnvOk handlerInstalled
                shape.2.2.2 targetBodyGlobal
            simp only [List.map_cons, List.cons.injEq] at handlerEq
            have exceptionEq := handlerEq.1
            have envFinalEq := handlerEq.2
            have refsBodyFinal : ∀ key, source.refs.lookup key ≠ none → bodyRelocate key = finalRelocate key := by
              intro key present
              exact refsHandlerEq key (sourceGrowth key present)
            have valuesFinalEq := adjustMap_eq_of_ok bodyRelocate finalRelocate values source.refs valuesOk refsBodyFinal
            have argsFinal : BviSem.evaluate bindingsCode (env.map (adjustBv finalRelocate))
                (BviProps.incClock bindingsClock target) = (.val (values.map (adjustBv finalRelocate)), targetMid) := by
              simpa [mapSimulationResult, envBodyEq, envFinalEq, valuesEq, valuesFinalEq] using targetBindings
            have bodyFinal : BviSem.evaluate [bodyCode] (values.map (adjustBv finalRelocate))
                (BviProps.incClock bodyClock targetMid) =
                  (.err (.raise (.exn (adjustBv finalRelocate exception))), targetBody) := by
              simpa [mapSimulationResult, valuesFinalEq, exceptionEq] using targetBodyRun
            have handlerFinal : BviSem.evaluate [handlerCode]
                (adjustBv finalRelocate exception :: env.map (adjustBv finalRelocate))
                (BviProps.incClock handlerClock targetBody) = (mapSimulationResult finalRelocate res, targetFinal) := by
              simpa using targetHandler
            have auxRun := evaluate_aux_call_handle_raise bindingsCode (env.map (adjustBv finalRelocate))
              (values.map (adjustBv finalRelocate)) (BviProps.incClock bindingsClock target) targetMid targetBody targetFinal
              (bvlNumStubs + bvlToBviNamespaces * finalName + 1) bindings.length bodyClock handlerClock bodyCode handlerCode
              (adjustBv finalRelocate exception) finalRelocate res argsFinal (by simpa using valuesLength)
              auxInstalled bodyFinal handlerFinal
            refine ⟨targetFinal, finalRelocate, (handlerClock + bodyClock + 1) + bindingsClock, ?_, relatedFinal,
              envMidEq.trans (envBodyEq.trans envFinalEq), ?_⟩
            · simpa [BviProps.incClock_add] using auxRun
            · intro key present
              exact (refsMidEq key present).trans ((refsBodyEq key present).trans (refsBodyFinal key present))

/-- Variable-only protected lets and variable handlers instantiate the
handler simulation. -/
theorem simulation_handle_vars {C F : Type} (indices : List Nat) (body handler : Nat)
    (env : List Value) (source : BvlSem.State (Nat × C) F) :
    simulation [.handle (.let (indices.map Bvl.Exp.var) (.var body)) (.var handler)] env source :=
  simulation_handle (indices.map Bvl.Exp.var) (.var body) (.var handler) env source
    (simulation_vars indices env source) (fun values => simulation_var body values source)
    (fun exception mid _ => simulation_var handler (exception :: env) mid)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
