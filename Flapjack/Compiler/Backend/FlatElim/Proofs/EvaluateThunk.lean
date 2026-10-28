import Flapjack.Compiler.Backend.FlatElim.Proofs.EvaluateCall

/-! Store invariants for the thunk-forcing evaluation case. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- A thunk read from an invariant store has a closed, Eval-free payload.
This is a Flapjack-specific helper for the evaluation induction. -/
theorem destThunk_value_invariants (values : List FlatSem.Value) (refs : Store FlatSem.Value)
    (mode : Flapjack.AstHOL.ThunkMode) (value : FlatSem.Value) (reachable : NumSet)
    (found : FlatSem.destThunk values refs = .isThunk mode value)
    (closed : globalsWithin (findRefsGlobals refs) reachable) (safe : storeHasNoEval refs) :
    globalsWithin (findValueGlobals value) reachable ∧ valueHasEval value = false := by
  cases values with
  | nil => simp [FlatSem.destThunk] at found
  | cons first rest =>
    cases rest with
    | cons second rest => simp [FlatSem.destThunk] at found
    | nil =>
      cases first <;> simp only [FlatSem.destThunk] at found
      all_goals try contradiction
      case loc isRef index =>
        cases lookup : storeLookup index refs with
        | none => simp [lookup] at found
        | some entry =>
          cases entry <;> simp [lookup] at found
          case thunk entryMode entryValue =>
            cases isRef <;> simp at found
            case false =>
              rcases found with ⟨rfl, rfl⟩
              have member : StoreValue.thunk entryMode entryValue ∈ refs := by
                apply List.mem_of_getElem?
                exact lookup
              exact ⟨(findRefsGlobals_within_iff _ _).mp closed _ member, safe _ member⟩

/-- Updating a thunk with a closed, Eval-free result preserves the relation
between stores. This is a Flapjack-specific helper for thunk forcing. -/
theorem updateThunk_flatStateRel {C F : Type} (reachable : NumSet)
    (source target : FlatSem.State C F) (targets values : List FlatSem.Value) (refs : Store FlatSem.Value)
    (related : flatStateRel reachable source target)
    (valuesClosed : globalsWithin (findValuesGlobals values) reachable) (valuesSafe : valuesNoEval values)
    (updated : FlatSem.updateThunk targets source.refs values = some refs) :
    ∃ targetRefs, FlatSem.updateThunk targets target.refs values = some targetRefs ∧
      flatStateRel reachable { source with refs := refs } { target with refs := targetRefs } := by
  cases targets with
  | nil => simp [FlatSem.updateThunk] at updated
  | cons first rest =>
    cases rest with
    | cons second rest => simp [FlatSem.updateThunk] at updated
    | nil =>
      cases values with
      | nil => simp [FlatSem.updateThunk] at updated
      | cons value rest =>
        cases rest with
        | cons second rest => simp [FlatSem.updateThunk] at updated
        | nil =>
          have valueClosed := (findValuesGlobals_within_iff _ _).mp valuesClosed value (by simp)
          have valueSafe := valuesSafe value (by simp)
          cases first <;> simp only [FlatSem.updateThunk] at updated
          all_goals try contradiction
          case loc flag index =>
            cases flag <;> simp only at updated
            all_goals try contradiction
            case false =>
              cases thunk : FlatSem.destThunk [value] source.refs <;> simp [thunk] at updated
              case notThunk =>
                have assignSet : refs = source.refs.set index (.thunk .evaluated value) := by
                  unfold storeAssign at updated
                  cases lookup : source.refs[index]? with
                  | none => simp [lookup] at updated
                  | some old =>
                    simp only [lookup] at updated
                    change (if storeValueSameType old (.thunk .evaluated value) then
                      some (source.refs.set index (.thunk .evaluated value)) else none) = some refs at updated
                    split at updated <;> simp_all
                subst refs
                have refsEq := related.2.1
                refine ⟨target.refs.set index (.thunk .evaluated value), ?_, ?_⟩
                · simpa [FlatSem.updateThunk, ← refsEq, thunk] using updated
                · apply flatStateRel_setRefs reachable source target index (.thunk .evaluated value) related
                  · exact valueClosed
                  · simpa [storeHasNoEval] using valueSafe

/-- Thunk forcing simulation at a fixed initial state, assuming simulation
of the generated application at the clamped state. This is a Flapjack
induction step, not the assembled HOL theorem. -/
theorem evaluate_force_simulation_step {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsIH : evaluationSimulation (C := C) (F := F) args.reverse)
    (forceIH : ∀ (newState : FlatSem.State C F) (value : FlatSem.Value), newState.clock ≤ source.clock →
      evaluationSimulationAt ⟨[(Flapjack.Basis.Pure.MlString.ofString "f", value)]⟩ newState
        [FlatSem.appUnit (.varLocal .none (Flapjack.Basis.Pure.MlString.ofString "f"))]) :
    evaluationSimulationAt env source [.app tra (.src (.thunkOp .forceThunk)) args] := by
  intro next result reachable target run lookupsClosed related envClosed envSafe expressionsSafe notTypeError
  have argsClosed : globalsWithin (findGlobalsList destGlobalVarLookup args.reverse) reachable := by
    apply findLookupsList_reverse_within args reachable
    have appClosed := (findLookupsList_within_iff _ _).mp lookupsClosed (.app tra (.src (.thunkOp .forceThunk)) args) (by simp)
    exact (findLookups_app_within tra (.src (.thunkOp .forceThunk)) args reachable appClosed).1
  have argsSafe : expressionsNoEval args.reverse := by
    apply expressionsNoEval_reverse args
    apply (hasEvalList_eq_false_iff args).mp
    have safe := expressionsSafe (.app tra (.src (.thunkOp .forceThunk)) args) (by simp)
    simpa [hasEval] using safe
  cases argEval : FlatSem.evaluate env source args.reverse with
  | mk argState argResult =>
    simp only [FlatSem.evaluate, argEval, FlatSem.fixClock] at run
    have argNotTypeError : argResult ≠ .err (.abort .typeError) := by
      intro bad
      subst argResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨targetArgState, targetArgEval, argRelated, argClosed, argSafe⟩ :=
      argsIH env source argState argResult reachable target argEval argsClosed related envClosed envSafe argsSafe argNotTypeError
    have clampedRelated := flatStateRel_fixClock reachable source target argState targetArgState argResult related argRelated
    simp only [FlatSem.fixClock] at clampedRelated
    cases argResult with
    | err error =>
      simp only at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, clampedRelated, argClosed, argSafe⟩
      simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock]
    | val values =>
      simp only at run
      have refsEq := clampedRelated.2.1
      cases thunk : FlatSem.destThunk values argState.refs with
      | badRef =>
        simp [thunk] at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      | notThunk =>
        simp [thunk] at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      | isThunk mode value =>
        have invariants := destThunk_value_invariants values argState.refs mode value reachable thunk clampedRelated.2.2.2.2.1 clampedRelated.2.2.2.2.2
        cases mode with
        | evaluated =>
          simp [thunk] at run
          rcases run with ⟨rfl, rfl⟩
          have resultSafe := primitiveResult_value_invariants reachable value invariants.1 invariants.2
          refine ⟨{ targetArgState with clock := min target.clock targetArgState.clock }, ?_, clampedRelated, resultSafe.1, resultSafe.2⟩
          simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock, ← refsEq, thunk]
        | notEvaluated =>
          simp [thunk] at run
          let name := Flapjack.Basis.Pure.MlString.ofString "f"
          let forceEnv : FlatSem.Environment FlatSem.Value := ⟨[(name, value)]⟩
          let forceBody := FlatSem.appUnit (.varLocal .none name)
          have forceClosed : globalsWithin (findGlobalsList destGlobalVarLookup [forceBody]) reachable := by
            simp [forceBody, FlatSem.appUnit, findGlobalsList, findGlobals, destGlobalVarLookup, globalsWithin, sptUnion, sptMem, sptDomain]
          have forceSafe : expressionsNoEval [forceBody] := by
            apply singletonExpression_noEval
            simp [forceBody, FlatSem.appUnit, hasEval, hasEvalList]
          have forceEnvClosed : globalsWithin (findEnvGlobals forceEnv) reachable := by
            change bindingsWithin [(name, value)] reachable
            apply (bindingsWithin_cons name value [] reachable).mpr
            exact ⟨invariants.1, by simp [bindingsWithin, findValuesGlobals, globalsWithin, sptMem, sptDomain]⟩
          have forceEnvSafe : bindingsNoEval forceEnv.v := by
            simpa [forceEnv, bindingsNoEval] using invariants.2
          cases bodyEval : FlatSem.evaluate forceEnv { argState with clock := min source.clock argState.clock } [forceBody] with
          | mk bodyState bodyResult =>
            dsimp [forceEnv, forceBody, name] at bodyEval
            simp only [bodyEval] at run
            have bodyNotTypeError : bodyResult ≠ .err (.abort .typeError) := by
              intro bad
              subst bodyResult
              simp at run
              rcases run with ⟨_, rfl⟩
              exact notTypeError rfl
            obtain ⟨targetBodyState, targetBodyEval, bodyRelated, bodyClosed, bodySafe⟩ :=
              forceIH _ value (Nat.min_le_left _ _) bodyState bodyResult reachable _ bodyEval forceClosed clampedRelated forceEnvClosed forceEnvSafe forceSafe bodyNotTypeError
            cases bodyResult with
            | err error =>
              simp only at run
              rcases run with ⟨rfl, rfl⟩
              refine ⟨targetBodyState, ?_, bodyRelated, bodyClosed, bodySafe⟩
              simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock, ← refsEq, thunk, targetBodyEval]
            | val outputs =>
              simp only at run
              cases updated : FlatSem.updateThunk values bodyState.refs outputs with
              | none =>
                simp [updated] at run
                rcases run with ⟨_, rfl⟩
                exact (notTypeError rfl).elim
              | some refs =>
                simp [updated] at run
                rcases run with ⟨rfl, rfl⟩
                have outputsClosed : globalsWithin (findValuesGlobals outputs) reachable := by simpa [findPrimitiveResultGlobals] using bodyClosed
                have outputsSafe : valuesNoEval outputs := by simpa [Flapjack.Compiler.Backend.FlatProps.resultValues] using bodySafe
                obtain ⟨targetRefs, targetUpdated, updatedRelated⟩ :=
                  updateThunk_flatStateRel reachable bodyState targetBodyState values outputs refs bodyRelated outputsClosed outputsSafe updated
                refine ⟨{ targetBodyState with refs := targetRefs }, ?_, updatedRelated, bodyClosed, bodySafe⟩
                simp [FlatSem.evaluate, targetArgEval, FlatSem.fixClock, ← refsEq, thunk, targetBodyEval, targetUpdated]

end Flapjack.Compiler.Backend.FlatElim
