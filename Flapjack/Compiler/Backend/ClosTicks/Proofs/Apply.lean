module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateLetrec
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean
public import Flapjack.Compiler.Backend.Semantics.ClosSem.AppClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosProps.DestClosure

@[expose] public section

/-! Closure-application relations for tick-removal correctness. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Indexing related lists gives related optional entries. This is Flapjack
infrastructure for recursive closure inspection. -/
theorem list_lookup_related {A B : Type} {relation : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ relation left right) (index : Nat) :
    Flapjack.optionRel relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => simp [Flapjack.optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [Flapjack.optionRel] using head
    | succ index => simpa using ih index

/-- Related recursive bundles yield related closures at each index. This is
Flapjack infrastructure for recursive closure inspection. -/
theorem recursive_bundle_related (location : Option Nat) (env nextEnv : List Value)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (environments : List.Forall₂ ValueRel env nextEnv)
    (bodies : List.Forall₂ FunctionRel functions nextFunctions) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range nextFunctions.length).map (fun i => Value.recclosure location [] nextEnv nextFunctions i)) := by
  rw [← bodies.length_eq]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] env nextEnv functions nextFunctions index environments .nil bodies) ih

/-- Successful closure inspection only accepts a closure or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "dest_closure_SOME_IMP"]
theorem destClosure_some_shape (maxApp : Nat) (location : Option Nat) (function : Value)
    (args : List Value) (result : AppKind) (run : destClosure maxApp location function args = some result) :
    (∃ loc supplied env arity body, function = .closure loc supplied env arity body) ∨
      (∃ loc supplied env functions index, function = .recclosure loc supplied env functions index) := by
  cases function <;> simp_all [destClosure]

/-- Related values and argument lists reject the same closure inspections.
This is Flapjack infrastructure for the reverse application simulation. -/
theorem destClosure_none_related (maxApp : Nat) (requested : Option Nat)
    (source target : Value) (args nextArgs : List Value) (related : ValueRel source target)
    (argsRel : List.Forall₂ ValueRel args nextArgs)
    (rejected : destClosure maxApp requested target nextArgs = none) :
    destClosure maxApp requested source args = none := by
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => rfl
  | closure location supplied nextSupplied env nextEnv arity body nextBody envRel suppliedRel bodyRel =>
    by_cases valid : checkLoc maxApp requested location arity nextArgs.length nextSupplied.length = true ∧
        nextSupplied.length < arity
    · rw [destClosure_closure_source, ite_eq_left valid] at rejected
      split at rejected <;> cases rejected
    · have sourceInvalid : ¬ (checkLoc maxApp requested location arity args.length supplied.length = true ∧
          supplied.length < arity) := by simpa [argsRel.length_eq, suppliedRel.length_eq] using valid
      rw [destClosure_closure_source, ite_eq_right sourceInvalid]
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions index envRel suppliedRel functionsRel =>
    have lookup := list_lookup_related functionsRel index
    cases targetFound : nextFunctions[index]? with
    | none =>
      cases found : functions[index]? with
      | none => simp [destClosure, found]
      | some entry => simp [Flapjack.optionRel, found, targetFound] at lookup
    | some targetEntry =>
      rcases targetEntry with ⟨nextArity, nextBody⟩
      cases found : functions[index]? with
      | none => simp [Flapjack.optionRel, found, targetFound] at lookup
      | some entry =>
        rcases entry with ⟨arity, body⟩
        have entries : FunctionRel (arity, body) (nextArity, nextBody) := by
          simpa [Flapjack.optionRel, found, targetFound] using lookup
        have arityEq : arity = nextArity := entries.1
        subst nextArity
        by_cases valid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity nextArgs.length nextSupplied.length && decide (nextSupplied.length < arity)) = true
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_left valid] at rejected
          split at rejected <;> cases rejected
        · have sourceInvalid : ¬ ((checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
              arity args.length supplied.length && decide (supplied.length < arity)) = true) := by
            simpa [argsRel.length_eq, suppliedRel.length_eq] using valid
          rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, ite_eq_right sourceInvalid]

/-- Partial application of related closures yields related partial closures.
This is Flapjack infrastructure for the reverse application simulation. -/
theorem destClosure_partial_related (maxApp : Nat) (requested : Option Nat)
    (source target : Value) (args nextArgs : List Value) (value : Value)
    (related : ValueRel source target) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested target nextArgs = some (.partialApp value)) :
    ∃ sourceValue, destClosure maxApp requested source args = some (.partialApp sourceValue) ∧
      ValueRel sourceValue value := by
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => simp [destClosure] at run
  | closure location supplied nextSupplied env nextEnv arity body nextBody envRel suppliedRel bodyRel =>
    by_cases valid : checkLoc maxApp requested location arity nextArgs.length nextSupplied.length = true ∧
        nextSupplied.length < arity
    · by_cases partialCase : nextArgs.length + nextSupplied.length < arity
      · rw [destClosure_closure_source, ite_eq_left valid, ite_eq_right (not_not.mpr partialCase)] at run
        cases run
        refine ⟨.closure location (args ++ supplied) env arity body, ?_, ?_⟩
        · have sourceValid : checkLoc maxApp requested location arity args.length supplied.length = true ∧
              supplied.length < arity := by simpa [argsRel.length_eq, suppliedRel.length_eq] using valid
          have sourcePartial : args.length + supplied.length < arity := by
            simpa [argsRel.length_eq, suppliedRel.length_eq] using partialCase
          rw [destClosure_closure_source, ite_eq_left sourceValid, ite_eq_right (not_not.mpr sourcePartial)]
        · exact .closure location (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv arity body nextBody
            envRel (List.rel_append argsRel suppliedRel) bodyRel
      · rw [destClosure_closure_source, ite_eq_left valid, ite_eq_left partialCase] at run
        cases run
    · rw [destClosure_closure_source, ite_eq_right valid] at run
      contradiction
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions index envRel suppliedRel functionsRel =>
    have lookup := list_lookup_related functionsRel index
    cases targetFound : nextFunctions[index]? with
    | none => simp [destClosure, targetFound] at run
    | some targetEntry =>
      rcases targetEntry with ⟨nextArity, nextBody⟩
      cases found : functions[index]? with
      | none => simp [Flapjack.optionRel, found, targetFound] at lookup
      | some entry =>
        rcases entry with ⟨arity, body⟩
        have entries : FunctionRel (arity, body) (nextArity, nextBody) := by
          simpa [Flapjack.optionRel, found, targetFound] using lookup
        have arityEq : arity = nextArity := entries.1
        subst nextArity
        by_cases valid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity nextArgs.length nextSupplied.length && decide (nextSupplied.length < arity)) = true
        · by_cases partialCase : nextArgs.length + nextSupplied.length < arity
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_left valid, ite_eq_left partialCase] at run
            cases run
            refine ⟨.recclosure location (args ++ supplied) env functions index, ?_, ?_⟩
            · have sourceValid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
                  arity args.length supplied.length && decide (supplied.length < arity)) = true := by
                simpa [argsRel.length_eq, suppliedRel.length_eq] using valid
              have sourcePartial : args.length + supplied.length < arity := by
                simpa [argsRel.length_eq, suppliedRel.length_eq] using partialCase
              rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, ite_eq_left sourceValid, ite_eq_left sourcePartial]
            · exact .recclosure location (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv functions nextFunctions
                index envRel (List.rel_append argsRel suppliedRel) functionsRel
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_left valid, ite_eq_right partialCase] at run
            cases run
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_right valid] at run
          contradiction

/-- Full application selects related bodies, environments and remaining
arguments. This is Flapjack infrastructure for the reverse simulation. -/
theorem destClosure_full_related (maxApp : Nat) (requested : Option Nat)
    (source target arg nextArg : Value) (args nextArgs : List Value)
    (body : ClosLang.Exp) (env remaining : List Value)
    (premises : ValueRel source target ∧ ValueRel arg nextArg ∧
      List.Forall₂ ValueRel args nextArgs ∧
      destClosure maxApp requested target (nextArg :: nextArgs) = some (.fullApp body env remaining)) :
    ∃ sourceBody sourceEnv sourceRemaining,
      CodeRel [sourceBody] [body] ∧ List.Forall₂ ValueRel sourceEnv env ∧
      List.Forall₂ ValueRel sourceRemaining remaining ∧
      destClosure maxApp requested source (arg :: args) = some (.fullApp sourceBody sourceEnv sourceRemaining) := by
  obtain ⟨related, argRel, argsRel, run⟩ := premises
  have allArgs : List.Forall₂ ValueRel (arg :: args) (nextArg :: nextArgs) := .cons argRel argsRel
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => simp [destClosure] at run
  | closure location supplied nextSupplied captured nextCaptured arity sourceBody targetBody envRel suppliedRel bodyRel =>
    by_cases valid : checkLoc maxApp requested location arity (nextArg :: nextArgs).length nextSupplied.length = true ∧
        nextSupplied.length < arity
    · by_cases partialCase : (nextArg :: nextArgs).length + nextSupplied.length < arity
      · rw [destClosure_closure_source, ite_eq_left valid, ite_eq_right (not_not.mpr partialCase)] at run
        cases run
      · rw [destClosure_closure_source, ite_eq_left valid, ite_eq_left partialCase] at run
        simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        let needed := arity - supplied.length
        refine ⟨sourceBody, ((arg :: args).reverse.take needed).reverse ++ (supplied ++ captured),
          ((arg :: args).reverse.drop needed).reverse, bodyRel, ?_, ?_, ?_⟩
        · have prefixRel := List.rel_reverse (List.forall₂_take needed (List.rel_reverse allArgs))
          simpa [needed, suppliedRel.length_eq] using List.rel_append prefixRel (List.rel_append suppliedRel envRel)
        · simpa [needed, suppliedRel.length_eq] using List.rel_reverse (List.forall₂_drop needed (List.rel_reverse allArgs))
        · have sourceValid : checkLoc maxApp requested location arity (arg :: args).length supplied.length = true ∧
              supplied.length < arity := by simpa [allArgs.length_eq, suppliedRel.length_eq] using valid
          have sourceFull : ¬ ((arg :: args).length + supplied.length < arity) := by
            simpa [allArgs.length_eq, suppliedRel.length_eq] using partialCase
          rw [destClosure_closure_source, ite_eq_left sourceValid, ite_eq_left sourceFull]
          rfl
    · rw [destClosure_closure_source, ite_eq_right valid] at run
      contradiction
  | recclosure location supplied nextSupplied captured nextCaptured sourceFunctions targetFunctions index envRel suppliedRel functionsRel =>
    have lookup := list_lookup_related functionsRel index
    cases targetFound : targetFunctions[index]? with
    | none => simp [destClosure, targetFound] at run
    | some targetEntry =>
      rcases targetEntry with ⟨targetArity, targetBody⟩
      cases found : sourceFunctions[index]? with
      | none => simp [Flapjack.optionRel, found, targetFound] at lookup
      | some entry =>
        rcases entry with ⟨arity, sourceBody⟩
        have entries : FunctionRel (arity, sourceBody) (targetArity, targetBody) := by
          simpa [Flapjack.optionRel, found, targetFound] using lookup
        have arityEq : arity = targetArity := entries.1
        subst targetArity
        by_cases valid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity (nextArg :: nextArgs).length nextSupplied.length && decide (nextSupplied.length < arity)) = true
        · by_cases partialCase : (nextArg :: nextArgs).length + nextSupplied.length < arity
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_left valid, ite_eq_left partialCase] at run
            cases run
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_left valid, ite_eq_right partialCase] at run
            simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
            obtain ⟨rfl, rfl, rfl⟩ := run
            let needed := arity - supplied.length
            let sourceRecursive := (List.range sourceFunctions.length).map
              (fun i => Value.recclosure location [] captured sourceFunctions i)
            let targetRecursive := (List.range targetFunctions.length).map
              (fun i => Value.recclosure location [] nextCaptured targetFunctions i)
            refine ⟨sourceBody, ((arg :: args).reverse.take needed).reverse ++
              (supplied ++ sourceRecursive ++ captured), ((arg :: args).reverse.drop needed).reverse,
              entries.2, ?_, ?_, ?_⟩
            · have prefixRel := List.rel_reverse (List.forall₂_take needed (List.rel_reverse allArgs))
              have recRel : List.Forall₂ ValueRel sourceRecursive targetRecursive :=
                recursive_bundle_related location captured nextCaptured sourceFunctions targetFunctions envRel functionsRel
              simpa [needed, suppliedRel.length_eq, targetRecursive] using
                List.rel_append prefixRel (List.rel_append suppliedRel (List.rel_append recRel envRel))
            · simpa [needed, suppliedRel.length_eq] using List.rel_reverse (List.forall₂_drop needed (List.rel_reverse allArgs))
            · have sourceValid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
                  arity (arg :: args).length supplied.length && decide (supplied.length < arity)) = true := by
                simpa [allArgs.length_eq, suppliedRel.length_eq] using valid
              have sourceFull : ¬ ((arg :: args).length + supplied.length < arity) := by
                simpa [allArgs.length_eq, suppliedRel.length_eq] using partialCase
              rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, ite_eq_left sourceValid, ite_eq_right sourceFull]
              simp [needed, sourceRecursive, List.append_assoc]
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, ite_eq_right valid] at run
          contradiction

namespace ApplyPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end ApplyPort

/-- Setting both clocks equally preserves related states. This is Flapjack
infrastructure for the application simulation. -/
theorem stateRel_clock {C F : Type} (source target : State C F) (clock : Nat) (related : StateRel source target) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  obtain ⟨aux, codeS, codeT, maxApp, positive, _, ffi, globals, refs, compiler, oracle⟩ := related
  exact ⟨aux, codeS, codeT, maxApp, positive, rfl, ffi, globals, refs, compiler, oracle⟩

/-- Equal clock decrements preserve related states. This is Flapjack
infrastructure for the application simulation. -/
theorem stateRel_dec {C F : Type} (source target : State C F) (amount : Nat) (related : StateRel source target) :
    StateRel (decClock amount source) (decClock amount target) := by
  have clocks : target.clock = source.clock := related.2.2.2.2.2.1
  simpa [decClock, clocks] using stateRel_clock source target (source.clock - amount) related

/-- Reverse expression simulation at a fixed target configuration. This is
Flapjack infrastructure for the mutual evaluator induction. -/
def EvalAt {C F : Type} (code : List ClosLang.Exp) (env : List Value) (target : State C F) : Prop :=
  ∀ (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp),
    evaluate code env target = (result, targetNext) ∧ List.Forall₂ ValueRel envSource env ∧
      StateRel source target ∧ CodeRel sourceCode code →
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext

/-- Reverse application simulation at a fixed target configuration. This is
Flapjack infrastructure for the mutual evaluator induction. -/
def AppAt {C F : Type} (location : Option Nat) (function : Value) (args : List Value) (target : State C F) : Prop :=
  ∀ (result : Result (List Value) Value) (targetNext : State C F)
    (sourceFunction : Value) (sourceArgs : List Value) (source : State C F),
    evaluateApp location function args target = (result, targetNext) ∧ ValueRel sourceFunction function ∧
      List.Forall₂ ValueRel sourceArgs args ∧ StateRel source target →
    ∃ extra sourceResult sourceNext,
      evaluateApp location sourceFunction sourceArgs { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext

/-- The empty-argument case of the reverse application simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_app_nil {C F : Type} (location : Option Nat) (function : Value)
    (target : State C F) (result : Result (List Value) Value) (targetNext : State C F)
    (sourceFunction : Value) (sourceArgs : List Value) (source : State C F)
    (premises : evaluateApp location function [] target = (result, targetNext) ∧
      ValueRel sourceFunction function ∧ List.Forall₂ ValueRel sourceArgs [] ∧ StateRel source target) :
    ∃ extra sourceResult sourceNext,
      evaluateApp location sourceFunction sourceArgs { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, functionRel, argsRel, states⟩ := premises
  cases argsRel
  simp [evaluateApp] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨0, .val [sourceFunction], source, by simp [evaluateApp], .cons functionRel .nil, states⟩

/-- The nonempty closure-application induction case, including rejection,
partial application, timeout, body evaluation and over-application. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_app_cons {C F : Type} (location : Option Nat) (function arg : Value)
    (args : List Value) (target : State C F)
    (bodyIH : ∀ (body : ClosLang.Exp) (env rest : List Value),
      destClosure target.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      ¬ (target.clock < (arg :: args).length - rest.length) →
      EvalAt [body] env (decClock ((arg :: args).length - rest.length) target))
    (appIH : ∀ (body : ClosLang.Exp) (env rest : List Value) (value : Value) (middle : State C F),
      destClosure target.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      ¬ (target.clock < (arg :: args).length - rest.length) →
      evaluate [body] env (decClock ((arg :: args).length - rest.length) target) = (.val [value], middle) →
      AppAt location value rest middle) :
    AppAt location function (arg :: args) target := by
  intro result targetNext sourceFunction sourceArgs source premises
  obtain ⟨run, functions, arguments, states⟩ := premises
  cases arguments with
  | cons argRel tailRel =>
    rename_i sourceArg sourceTail
    have allArgs : List.Forall₂ ValueRel (sourceArg :: sourceTail) (arg :: args) := .cons argRel tailRel
    have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
    have clockEq : target.clock = source.clock := states.2.2.2.2.2.1
    cases closureRun : destClosure target.maxApp location function (arg :: args) with
    | none =>
      have sourceClosure := destClosure_none_related target.maxApp location sourceFunction function
        (sourceArg :: sourceTail) (arg :: args) functions allArgs closureRun
      rw [evaluateApp, closureRun] at run
      dsimp only at run
      cases run
      refine ⟨0, .err (.abort .typeError), source, ?_, rfl, states⟩
      have sourceFound : destClosure source.maxApp location sourceFunction (sourceArg :: sourceTail) = none := by
        simpa [maxEq] using sourceClosure
      simpa using (show evaluateApp location sourceFunction (sourceArg :: sourceTail) source =
          (.err (.abort .typeError), source) by rw [evaluateApp, sourceFound]; rfl)
    | some kind =>
      cases kind with
      | partialApp value =>
        obtain ⟨sourceValue, sourceClosure, valuesRel⟩ :=
          destClosure_partial_related target.maxApp location sourceFunction function
            (sourceArg :: sourceTail) (arg :: args) value functions allArgs closureRun
        have sourceFound : destClosure source.maxApp location sourceFunction (sourceArg :: sourceTail) =
            some (.partialApp sourceValue) := by simpa [maxEq] using sourceClosure
        by_cases short : target.clock < (arg :: args).length
        · have sourceShort : source.clock < (sourceArg :: sourceTail).length := by
            simpa [clockEq, allArgs.length_eq] using short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [ite_eq_left short] at run
          cases run
          refine ⟨0, .err (.abort .timeoutError), { source with clock := 0 }, ?_, rfl,
            stateRel_clock source target 0 states⟩
          simpa using (show evaluateApp location sourceFunction (sourceArg :: sourceTail) source =
              (.err (.abort .timeoutError), { source with clock := 0 }) by
            rw [evaluateApp, sourceFound]; dsimp only; rw [ite_eq_left sourceShort]; rfl)
        · have sourceEnough : ¬ source.clock < (sourceArg :: sourceTail).length := by
            simpa [clockEq, allArgs.length_eq] using short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [ite_eq_right short] at run
          cases run
          refine ⟨0, .val [sourceValue], decClock (arg :: args).length source, ?_, .cons valuesRel .nil,
            stateRel_dec source target (arg :: args).length states⟩
          simpa using (show evaluateApp location sourceFunction (sourceArg :: sourceTail) source =
              (.val [sourceValue], decClock (arg :: args).length source) by
            rw [evaluateApp, sourceFound]; dsimp only; rw [ite_eq_right sourceEnough, allArgs.length_eq])
      | fullApp body env rest =>
        obtain ⟨sourceBody, sourceEnv, sourceRest, codeRel, envRel, restRel, sourceClosure⟩ :=
          destClosure_full_related target.maxApp location sourceFunction function sourceArg arg sourceTail args
            body env rest ⟨functions, argRel, tailRel, closureRun⟩
        let cost := (arg :: args).length - rest.length
        have sourceCost : (sourceArg :: sourceTail).length - sourceRest.length = cost := by
          simp [cost, allArgs.length_eq, restRel.length_eq]
        have sourceFound : destClosure source.maxApp location sourceFunction (sourceArg :: sourceTail) =
            some (.fullApp sourceBody sourceEnv sourceRest) := by simpa [maxEq] using sourceClosure
        by_cases short : target.clock < cost
        · have sourceShort : source.clock < (sourceArg :: sourceTail).length - sourceRest.length := by
            rw [sourceCost, ← clockEq]
            exact short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [ite_eq_left short] at run
          cases run
          refine ⟨0, .err (.abort .timeoutError), { source with clock := 0 }, ?_, rfl,
            stateRel_clock source target 0 states⟩
          simpa using (show evaluateApp location sourceFunction (sourceArg :: sourceTail) source =
              (.err (.abort .timeoutError), { source with clock := 0 }) by
            rw [evaluateApp, sourceFound]; dsimp only; rw [ite_eq_left sourceShort]; rfl)
        · have startRel := stateRel_dec source target cost states
          have sourceEnough : ¬ source.clock < cost := by simpa [clockEq] using short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [ite_eq_right short, fixClock_evaluate] at run
          cases bodyRun : evaluate [body] env (decClock cost target) with
          | mk bodyResult targetMiddle =>
            obtain ⟨bodyExtra, sourceBodyResult, sourceMiddle, sourceBodyRun, bodyRel, middleRel⟩ :=
              bodyIH body env rest closureRun short bodyResult targetMiddle sourceEnv (decClock cost source) [sourceBody]
                ⟨bodyRun, envRel, startRel, codeRel⟩
            have clockShift (extra : Nat) : decClock cost { source with clock := source.clock + extra } =
                { decClock cost source with clock := (decClock cost source).clock + extra } := by
              simp only [decClock]
              congr 1
              omega
            cases bodyResult with
            | err error =>
              rw [bodyRun] at run
              cases run
              cases sourceBodyResult with
              | val values => cases error <;> simp [ResultRel] at bodyRel
              | err sourceError =>
                refine ⟨bodyExtra, .err sourceError, sourceMiddle, ?_, bodyRel, middleRel⟩
                have enough : ¬ source.clock + bodyExtra < cost := by omega
                rw [evaluateApp, sourceFound]
                dsimp only
                rw [sourceCost, ite_eq_right enough, clockShift, fixClock_evaluate, sourceBodyRun]
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body env (decClock cost target) targetMiddle values bodyRun
              cases sourceBodyResult with
              | err error => cases error <;> simp [ResultRel] at bodyRel
              | val sourceValues =>
                cases bodyRel with
                | cons valueRel tailRel =>
                  cases tailRel
                  rename_i sourceValue
                  have appRun : evaluateApp location value rest targetMiddle = (result, targetNext) := by
                    rw [bodyRun] at run
                    exact run
                  obtain ⟨appExtra, sourceResult, sourceNext, sourceAppRun, resultRel, nextRel⟩ :=
                    appIH body env rest value targetMiddle closureRun short bodyRun result targetNext
                      sourceValue sourceRest sourceMiddle ⟨appRun, valueRel, restRel, middleRel⟩
                  have shifted := (evaluate_addClock (C := C) (F := F)).1 [sourceBody] sourceEnv
                    { decClock cost source with clock := (decClock cost source).clock + bodyExtra } sourceMiddle
                    (.val [sourceValue]) appExtra sourceBodyRun (by simp)
                  have shiftedBody : evaluate [sourceBody] sourceEnv
                      { decClock cost source with clock := (decClock cost source).clock + (bodyExtra + appExtra) } =
                        (.val [sourceValue], { sourceMiddle with clock := sourceMiddle.clock + appExtra }) := by
                    simpa [Nat.add_assoc] using shifted
                  refine ⟨bodyExtra + appExtra, sourceResult, sourceNext, ?_, resultRel, nextRel⟩
                  have enough : ¬ source.clock + (bodyExtra + appExtra) < cost := by omega
                  rw [evaluateApp, sourceFound]
                  dsimp only
                  rw [sourceCost, ite_eq_right enough, clockShift, fixClock_evaluate, shiftedBody]
                  exact sourceAppRun

end Flapjack.Compiler.Backend.ClosTicks
