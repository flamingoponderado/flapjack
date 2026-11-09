import Flapjack.Compiler.Backend.ClosFvs.Proofs.EvaluateOp
import Flapjack.Compiler.Backend.Semantics.ClosProps.DestClosure

/-! Mutual closure-application cases for free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Indexing related lists gives related optional entries. -/
theorem list_lookup_related {A B : Type} {relation : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ relation left right) (index : Nat) :
    optionRel relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => simp [optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [optionRel] using head
    | succ index => simpa using ih index

/-- Recursive closures generated from related bundles and environments are
related at each common index. -/
theorem recursive_bundle_related (location : Option Nat) (env nextEnv : List Value)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (environments : List.Forall₂ ValueRel env nextEnv)
    (bodies : List.Forall₂ (FunctionRel (env.length + functions.length)) functions nextFunctions) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range nextFunctions.length).map (fun i => Value.recclosure location [] nextEnv nextFunctions i)) := by
  rw [← bodies.length_eq]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] env nextEnv functions nextFunctions index environments .nil bodies) ih

/-- A successful closure inspection only accepts ordinary or recursive
closures. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_IMP"]
theorem destClosure_some_shape (maxApp : Nat) (location : Option Nat) (function : Value)
    (args : List Value) (result : AppKind) (run : destClosure maxApp location function args = some result) :
    (∃ loc supplied env arity body, function = .closure loc supplied env arity body) ∨
      (∃ loc supplied env functions index, function = .recclosure loc supplied env functions index) := by
  cases function <;> simp_all [destClosure]

/-- The ordinary-closure case of full application preserves the body relation,
the selected argument environment, and the over-application tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_Full_app"]
theorem destClosure_full_closure (maxApp : Nat) (requested location : Option Nat)
    (supplied nextSupplied env nextEnv : List Value) (arity : Nat) (body nextBody : ClosLang.Exp)
    (arg nextArg : Value) (args nextArgs : List Value) (resultBody : ClosLang.Exp)
    (resultEnv remaining : List Value)
    (envRel : List.Forall₂ ValueRel env nextEnv) (suppliedRel : List.Forall₂ ValueRel supplied nextSupplied)
    (bodyRel : CodeRel (env.length + arity) [body] [nextBody])
    (argRel : ValueRel arg nextArg) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested (.closure location supplied env arity body) (arg :: args) =
      some (.fullApp resultBody resultEnv remaining)) :
    ∃ targetBody targetEnv targetRemaining,
      CodeRel resultEnv.length [resultBody] [targetBody] ∧ List.Forall₂ ValueRel resultEnv targetEnv ∧
      List.Forall₂ ValueRel remaining targetRemaining ∧
      destClosure maxApp requested (.closure location nextSupplied nextEnv arity nextBody) (nextArg :: nextArgs) =
        some (.fullApp targetBody targetEnv targetRemaining) := by
  have allArgs : List.Forall₂ ValueRel (arg :: args) (nextArg :: nextArgs) := .cons argRel argsRel
  by_cases valid : checkLoc maxApp requested location arity (arg :: args).length supplied.length = true ∧
      supplied.length < arity
  · by_cases partialCase : (arg :: args).length + supplied.length < arity
    · rw [destClosure_closure_source, if_pos valid, if_neg (not_not.mpr partialCase)] at run
      cases run
    · rw [destClosure_closure_source, if_pos valid, if_pos partialCase] at run
      simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
      obtain ⟨rfl, rfl, rfl⟩ := run
      let needed := arity - supplied.length
      refine ⟨nextBody, ((nextArg :: nextArgs).reverse.take needed).reverse ++ (nextSupplied ++ nextEnv),
        ((nextArg :: nextArgs).reverse.drop needed).reverse, ?_, ?_, ?_, ?_⟩
      · have enough : needed ≤ (arg :: args).length := by
          dsimp [needed]
          simp only [List.length_cons] at partialCase ⊢
          omega
        have enough' : needed ≤ args.length + 1 := by simpa using enough
        have resultLength : (((arg :: args).reverse.take needed).reverse ++ (supplied ++ env)).length =
            env.length + arity := by
          simp only [List.length_append, List.length_reverse, List.length_take, List.length_cons,
            Nat.min_eq_left enough']
          dsimp [needed]
          omega
        change CodeRel (((arg :: args).reverse.take needed).reverse ++ (supplied ++ env)).length [body] [nextBody]
        rw [resultLength]
        exact bodyRel
      · have prefixRel := List.rel_reverse (List.forall₂_take needed (List.rel_reverse allArgs))
        exact List.rel_append prefixRel (List.rel_append suppliedRel envRel)
      · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse allArgs))
      · have targetValid : checkLoc maxApp requested location arity (nextArg :: nextArgs).length nextSupplied.length = true ∧
            nextSupplied.length < arity := by simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using valid
        have targetFull : ¬ ((nextArg :: nextArgs).length + nextSupplied.length < arity) := by
          simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using partialCase
        rw [destClosure_closure_source, if_pos targetValid, if_pos targetFull]
        simp [needed, ← suppliedRel.length_eq]
  · rw [destClosure_closure_source, if_neg valid] at run
    contradiction

/-- The recursive-closure case of full application selects corresponding
bodies and constructs related recursive environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_Full_app"]
theorem destClosure_full_recclosure (maxApp : Nat) (requested location : Option Nat)
    (supplied nextSupplied env nextEnv : List Value) (functions nextFunctions : List (Nat × ClosLang.Exp))
    (index : Nat) (arg nextArg : Value) (args nextArgs : List Value) (resultBody : ClosLang.Exp)
    (resultEnv remaining : List Value)
    (envRel : List.Forall₂ ValueRel env nextEnv) (suppliedRel : List.Forall₂ ValueRel supplied nextSupplied)
    (functionsRel : List.Forall₂ (FunctionRel (env.length + functions.length)) functions nextFunctions)
    (argRel : ValueRel arg nextArg) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested (.recclosure location supplied env functions index) (arg :: args) =
      some (.fullApp resultBody resultEnv remaining)) :
    ∃ targetBody targetEnv targetRemaining,
      CodeRel resultEnv.length [resultBody] [targetBody] ∧ List.Forall₂ ValueRel resultEnv targetEnv ∧
      List.Forall₂ ValueRel remaining targetRemaining ∧
      destClosure maxApp requested (.recclosure location nextSupplied nextEnv nextFunctions index) (nextArg :: nextArgs) =
        some (.fullApp targetBody targetEnv targetRemaining) := by
  have allArgs : List.Forall₂ ValueRel (arg :: args) (nextArg :: nextArgs) := .cons argRel argsRel
  have lookupRel := list_lookup_related functionsRel index
  cases found : functions[index]? with
  | none => simp [destClosure, found] at run
  | some entry =>
    rcases entry with ⟨arity, body⟩
    cases targetFound : nextFunctions[index]? with
    | none => simp [found, targetFound, optionRel] at lookupRel
    | some targetEntry =>
      rcases targetEntry with ⟨targetArity, targetBody⟩
      have entryRel : FunctionRel (env.length + functions.length) (arity, body) (targetArity, targetBody) := by
        simpa [found, targetFound, optionRel] using lookupRel
      have arityEq : arity = targetArity := entryRel.1
      subst targetArity
      have bodyRel : CodeRel (arity + (env.length + functions.length)) [body] [targetBody] := entryRel.2
      by_cases valid : checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity (arg :: args).length supplied.length = true ∧ supplied.length < arity
      · have condition : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity (arg :: args).length supplied.length && decide (supplied.length < arity)) = true := by
          simpa using valid
        by_cases partialCase : (arg :: args).length + supplied.length < arity
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_pos condition, if_pos partialCase] at run
          cases run
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_pos condition, if_neg partialCase] at run
          simp only [Option.some.injEq, AppKind.fullApp.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          let needed := arity - supplied.length
          let recursive := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
          let targetRecursive := (List.range nextFunctions.length).map
            (fun i => Value.recclosure location [] nextEnv nextFunctions i)
          refine ⟨targetBody, ((nextArg :: nextArgs).reverse.take needed).reverse ++
            (nextSupplied ++ targetRecursive ++ nextEnv), ((nextArg :: nextArgs).reverse.drop needed).reverse,
            ?_, ?_, ?_, ?_⟩
          · have enough : needed ≤ (arg :: args).length := by
              dsimp [needed]
              simp only [List.length_cons] at partialCase ⊢
              omega
            have enough' : needed ≤ args.length + 1 := by simpa using enough
            have resultLength : (((arg :: args).reverse.take needed).reverse ++
                (supplied ++ (recursive ++ env))).length = arity + (env.length + functions.length) := by
              simp only [List.length_append, List.length_reverse, List.length_take, List.length_cons,
                Nat.min_eq_left enough', recursive, List.length_map, List.length_range]
              dsimp [needed]
              omega
            change CodeRel (((arg :: args).reverse.take needed).reverse ++ (supplied ++ (recursive ++ env))).length [body] [targetBody]
            rw [resultLength]
            exact bodyRel
          · have prefixRel := List.rel_reverse (List.forall₂_take needed (List.rel_reverse allArgs))
            simpa [recursive, targetRecursive, List.append_assoc] using
              List.rel_append prefixRel (List.rel_append suppliedRel
                (List.rel_append (recursive_bundle_related location env nextEnv functions nextFunctions envRel functionsRel) envRel))
          · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse allArgs))
          · have targetCondition : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
                arity (nextArg :: nextArgs).length nextSupplied.length && decide (nextSupplied.length < arity)) = true := by
              simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using condition
            have targetFull : ¬ ((nextArg :: nextArgs).length + nextSupplied.length < arity) := by
              simpa [← allArgs.length_eq, ← suppliedRel.length_eq] using partialCase
            rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, if_pos targetCondition, if_neg targetFull]
            simp [needed, ← suppliedRel.length_eq, targetRecursive]
      · have condition : ¬ ((checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity (arg :: args).length supplied.length && decide (supplied.length < arity)) = true) := by
          simpa using valid
        rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_neg condition] at run
        contradiction

/-- Full application of related closures selects related bodies,
environments and remaining arguments. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "dest_closure_SOME_Full_app"]
theorem destClosure_full_related (maxApp : Nat) (requested : Option Nat)
    (function targetFunction arg targetArg : Value) (args targetArgs : List Value)
    (body : ClosLang.Exp) (env remaining : List Value)
    (premises : ValueRel function targetFunction ∧ ValueRel arg targetArg ∧
      List.Forall₂ ValueRel args targetArgs ∧
      destClosure maxApp requested function (arg :: args) = some (.fullApp body env remaining)) :
    ∃ targetBody targetEnv targetRemaining,
      CodeRel env.length [body] [targetBody] ∧ List.Forall₂ ValueRel env targetEnv ∧
      List.Forall₂ ValueRel remaining targetRemaining ∧
      destClosure maxApp requested targetFunction (targetArg :: targetArgs) =
        some (.fullApp targetBody targetEnv targetRemaining) := by
  obtain ⟨functions, argument, arguments, run⟩ := premises
  cases functions with
  | closure location supplied nextSupplied captured nextCaptured arity sourceBody targetBody envRel suppliedRel bodyRel =>
    exact destClosure_full_closure maxApp requested location supplied nextSupplied captured nextCaptured
      arity sourceBody targetBody arg targetArg args targetArgs body env remaining
      envRel suppliedRel bodyRel argument arguments run
  | recclosure location supplied nextSupplied captured nextCaptured sourceFunctions targetFunctions index envRel suppliedRel functionsRel =>
    exact destClosure_full_recclosure maxApp requested location supplied nextSupplied captured nextCaptured
      sourceFunctions targetFunctions index arg targetArg args targetArgs body env remaining
      envRel suppliedRel functionsRel argument arguments run
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => simp [destClosure] at run

/-- Related values and argument lists reject the same closure inspections. -/
theorem destClosure_none_related (maxApp : Nat) (requested : Option Nat)
    (source target : Value) (args nextArgs : List Value) (related : ValueRel source target)
    (argsRel : List.Forall₂ ValueRel args nextArgs)
    (rejected : destClosure maxApp requested source args = none) :
    destClosure maxApp requested target nextArgs = none := by
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => rfl
  | closure location supplied nextSupplied env nextEnv arity body nextBody envRel suppliedRel bodyRel =>
    by_cases valid : checkLoc maxApp requested location arity args.length supplied.length = true ∧
        supplied.length < arity
    · rw [destClosure_closure_source, if_pos valid] at rejected
      split at rejected <;> cases rejected
    · have targetInvalid : ¬ (checkLoc maxApp requested location arity nextArgs.length nextSupplied.length = true ∧
          nextSupplied.length < arity) := by simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using valid
      rw [destClosure_closure_source, if_neg targetInvalid]
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions index envRel suppliedRel functionsRel =>
    have lookup := list_lookup_related functionsRel index
    cases found : functions[index]? with
    | none =>
      cases targetFound : nextFunctions[index]? with
      | none => simp [destClosure, targetFound]
      | some entry => simp [optionRel, found, targetFound] at lookup
    | some entry =>
      rcases entry with ⟨arity, body⟩
      cases targetFound : nextFunctions[index]? with
      | none => simp [optionRel, found, targetFound] at lookup
      | some targetEntry =>
        rcases targetEntry with ⟨nextArity, nextBody⟩
        have entries : FunctionRel (env.length + functions.length) (arity, body) (nextArity, nextBody) := by
          simpa [optionRel, found, targetFound] using lookup
        have arityEq : arity = nextArity := entries.1
        subst nextArity
        by_cases valid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity args.length supplied.length && decide (supplied.length < arity)) = true
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_pos valid] at rejected
          split at rejected <;> cases rejected
        · have targetInvalid : ¬ ((checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
              arity nextArgs.length nextSupplied.length && decide (nextSupplied.length < arity)) = true) := by
            simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using valid
          rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, if_neg targetInvalid]

/-- Related closure values preserve partial application and its accumulated
argument list. -/
theorem destClosure_partial_related (maxApp : Nat) (requested : Option Nat)
    (source target : Value) (args nextArgs : List Value) (value : Value)
    (related : ValueRel source target) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested source args = some (.partialApp value)) :
    ∃ nextValue, destClosure maxApp requested target nextArgs = some (.partialApp nextValue) ∧
      ValueRel value nextValue := by
  cases related with
  | number _ | word64 _ | byteVector _ | refPtr _ _ | block _ _ _ _ => simp [destClosure] at run
  | closure location supplied nextSupplied env nextEnv arity body nextBody envRel suppliedRel bodyRel =>
    by_cases valid : checkLoc maxApp requested location arity args.length supplied.length = true ∧
        supplied.length < arity
    · by_cases partialCase : args.length + supplied.length < arity
      · rw [destClosure_closure_source, if_pos valid, if_neg (not_not.mpr partialCase)] at run
        cases run
        refine ⟨.closure location (nextArgs ++ nextSupplied) nextEnv arity nextBody, ?_, ?_⟩
        · have targetValid : checkLoc maxApp requested location arity nextArgs.length nextSupplied.length = true ∧
              nextSupplied.length < arity := by simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using valid
          have targetPartial : nextArgs.length + nextSupplied.length < arity := by
            simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using partialCase
          rw [destClosure_closure_source, if_pos targetValid, if_neg (not_not.mpr targetPartial)]
        · exact .closure location (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv arity body nextBody
            envRel (List.rel_append argsRel suppliedRel) bodyRel
      · rw [destClosure_closure_source, if_pos valid, if_pos partialCase] at run
        cases run
    · rw [destClosure_closure_source, if_neg valid] at run
      contradiction
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions index envRel suppliedRel functionsRel =>
    have lookup := list_lookup_related functionsRel index
    cases found : functions[index]? with
    | none => simp [destClosure, found] at run
    | some entry =>
      rcases entry with ⟨arity, body⟩
      cases targetFound : nextFunctions[index]? with
      | none => simp [optionRel, found, targetFound] at lookup
      | some targetEntry =>
        rcases targetEntry with ⟨nextArity, nextBody⟩
        have entries : FunctionRel (env.length + functions.length) (arity, body) (nextArity, nextBody) := by
          simpa [optionRel, found, targetFound] using lookup
        have arityEq : arity = nextArity := entries.1
        subst nextArity
        by_cases valid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
            arity args.length supplied.length && decide (supplied.length < arity)) = true
        · by_cases partialCase : args.length + supplied.length < arity
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_pos valid, if_pos partialCase] at run
            cases run
            refine ⟨.recclosure location (nextArgs ++ nextSupplied) nextEnv nextFunctions index, ?_, ?_⟩
            · have targetValid : (checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
                  arity nextArgs.length nextSupplied.length && decide (nextSupplied.length < arity)) = true := by
                simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using valid
              have targetPartial : nextArgs.length + nextSupplied.length < arity := by
                simpa [← argsRel.length_eq, ← suppliedRel.length_eq] using partialCase
              rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ targetFound, if_pos targetValid, if_pos targetPartial]
            · exact .recclosure location (args ++ supplied) (nextArgs ++ nextSupplied) env nextEnv functions nextFunctions
                index envRel (List.rel_append argsRel suppliedRel) functionsRel
          · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_pos valid, if_neg partialCase] at run
            cases run
        · rw [destClosure_rec_found _ _ _ _ _ _ _ _ _ _ found, if_neg valid] at run
          contradiction

namespace AppPort
/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The original application-simulation predicate at one source state. -/
def AppAt {C F : Type} (location : Option Nat) (function : Value) (args : List Value)
    (source : State C F) : Prop :=
  ∀ (result : Result (List Value) Value) (next : State C F)
    (targetFunction : Value) (targetArgs : List Value) (target : State C F),
    evaluateApp location function args source = (result, next) ∧
      ValueRel function targetFunction ∧ List.Forall₂ ValueRel args targetArgs ∧ StateRel source target →
    ∃ targetResult targetNext, evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel next targetNext

/-- Setting both clocks to the same value preserves the state relation. -/
theorem stateRel_clock {C F : Type} (source target : State C F) (clock : Nat) (related : StateRel source target) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  obtain ⟨aux, codeS, codeT, maxApp, positive, _, ffi, globals, refs, compiler, oracle⟩ := related
  exact ⟨aux, codeS, codeT, maxApp, positive, rfl, ffi, globals, refs, compiler, oracle⟩

/-- Decrementing both clocks by the same amount preserves the state relation. -/
theorem stateRel_dec {C F : Type} (source target : State C F) (amount : Nat) (related : StateRel source target) :
    StateRel (decClock amount source) (decClock amount target) := by
  have clocks : target.clock = source.clock := related.2.2.2.2.2.1
  simpa [decClock, clocks] using stateRel_clock source target (source.clock - amount) related

/-- Applying a related function to an empty argument list returns the
function unchanged, with its state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_app_nil {C F : Type} (location : Option Nat)
    (function targetFunction : Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetArgs : List Value) (target : State C F)
    (premises : evaluateApp location function [] source = (result, sourceNext) ∧
      ValueRel function targetFunction ∧ List.Forall₂ ValueRel [] targetArgs ∧ StateRel source target) :
    ∃ targetResult targetNext,
      evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, functions, args, states⟩ := premises
  cases args
  simp [evaluateApp] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [targetFunction], target, by simp [evaluateApp], .cons functions .nil, states⟩

/-- The nonempty closure-application induction case, including rejected and
partial calls, timeout, body evaluation and over-application. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_app_cons {C F : Type} (location : Option Nat) (function arg : Value)
    (args : List Value) (source : State C F)
    (bodyIH : ∀ (body : ClosLang.Exp) (env rest : List Value),
      destClosure source.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      ¬ (source.clock < (arg :: args).length - rest.length) →
      EvalAt [body] env (decClock ((arg :: args).length - rest.length) source))
    (appIH : ∀ (body : ClosLang.Exp) (env rest : List Value) (value : Value) (middle : State C F),
      destClosure source.maxApp location function (arg :: args) = some (.fullApp body env rest) →
      ¬ (source.clock < (arg :: args).length - rest.length) →
      evaluate [body] env (decClock ((arg :: args).length - rest.length) source) = (.val [value], middle) →
      AppAt location value rest middle) :
    AppAt location function (arg :: args) source := by
  intro result sourceNext targetFunction targetArgs target premises
  obtain ⟨run, functions, arguments, states⟩ := premises
  cases arguments with
  | cons argRel tailRel =>
    rename_i targetArg targetTail
    have allArgs : List.Forall₂ ValueRel (arg :: args) (targetArg :: targetTail) := .cons argRel tailRel
    have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
    have clockEq : target.clock = source.clock := states.2.2.2.2.2.1
    cases closureRun : destClosure source.maxApp location function (arg :: args) with
    | none =>
      have targetClosure := destClosure_none_related source.maxApp location function targetFunction
        (arg :: args) (targetArg :: targetTail) functions allArgs closureRun
      rw [evaluateApp, closureRun] at run
      dsimp only at run
      cases run
      refine ⟨.err (.abort .typeError), target, ?_, rfl, states⟩
      have targetFound : destClosure target.maxApp location targetFunction (targetArg :: targetTail) = none := by
        simpa [maxEq] using targetClosure
      rw [evaluateApp, targetFound]
      rfl
    | some kind =>
      cases kind with
      | partialApp value =>
        obtain ⟨targetValue, targetClosure, valuesRel⟩ :=
          destClosure_partial_related source.maxApp location function targetFunction
            (arg :: args) (targetArg :: targetTail) value functions allArgs closureRun
        have targetFound : destClosure target.maxApp location targetFunction (targetArg :: targetTail) =
            some (.partialApp targetValue) := by simpa [maxEq] using targetClosure
        by_cases short : source.clock < (arg :: args).length
        · have targetShort : target.clock < (targetArg :: targetTail).length := by
            simpa [clockEq, ← allArgs.length_eq] using short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [if_pos short] at run
          cases run
          refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl,
            stateRel_clock source target 0 states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_pos targetShort]
          rfl
        · have targetEnough : ¬ target.clock < (targetArg :: targetTail).length := by
            simpa [clockEq, ← allArgs.length_eq] using short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [if_neg short] at run
          cases run
          refine ⟨.val [targetValue], decClock (arg :: args).length target, ?_, .cons valuesRel .nil,
            stateRel_dec source target (arg :: args).length states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_neg targetEnough, ← allArgs.length_eq]
      | fullApp body env rest =>
        obtain ⟨targetBody, targetEnv, targetRest, codeRel, envRel, restRel, targetClosure⟩ :=
          destClosure_full_related source.maxApp location function targetFunction arg targetArg args targetTail
            body env rest ⟨functions, argRel, tailRel, closureRun⟩
        let cost := (arg :: args).length - rest.length
        have targetCost : (targetArg :: targetTail).length - targetRest.length = cost := by
          simp [cost, ← allArgs.length_eq, ← restRel.length_eq]
        have targetFound : destClosure target.maxApp location targetFunction (targetArg :: targetTail) =
            some (.fullApp targetBody targetEnv targetRest) := by simpa [maxEq] using targetClosure
        by_cases short : source.clock < cost
        · have targetShort : target.clock < (targetArg :: targetTail).length - targetRest.length := by
            rw [targetCost, clockEq]
            exact short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [if_pos short] at run
          cases run
          refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl,
            stateRel_clock source target 0 states⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_pos targetShort]
          rfl
        · have startRel := stateRel_dec source target cost states
          have targetEnough : ¬ target.clock < (targetArg :: targetTail).length - targetRest.length := by
            rw [targetCost, clockEq]
            exact short
          rw [evaluateApp, closureRun] at run
          dsimp only at run
          rw [if_neg short, fixClock_evaluate] at run
          cases bodyRun : evaluate [body] env (decClock cost source) with
          | mk bodyResult middle =>
            obtain ⟨targetBodyResult, targetMiddle, targetBodyRun, bodyRel, middleRel⟩ :=
              bodyIH body env rest closureRun short bodyResult middle [targetBody] targetEnv (decClock cost target)
                ⟨bodyRun, envRel, startRel, codeRel⟩
            cases bodyResult with
            | err error =>
              rw [bodyRun] at run
              cases run
              cases targetBodyResult with
              | val values => cases error <;> simp [ResultRel] at bodyRel
              | err targetError =>
                refine ⟨.err targetError, targetMiddle, ?_, bodyRel, middleRel⟩
                rw [evaluateApp, targetFound]
                dsimp only
                rw [if_neg targetEnough, targetCost, fixClock_evaluate, targetBodyRun]
            | val values =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value body env (decClock cost source) middle values bodyRun
              cases targetBodyResult with
              | err error => cases error <;> simp [ResultRel] at bodyRel
              | val targetValues =>
                cases bodyRel with
                | cons valueRel tailRel =>
                  cases tailRel
                  rename_i targetValue
                  have appRun : evaluateApp location value rest middle = (result, sourceNext) := by
                    rw [bodyRun] at run
                    exact run
                  obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
                    appIH body env rest value middle closureRun short bodyRun result sourceNext
                      targetValue targetRest targetMiddle ⟨appRun, valueRel, restRel, middleRel⟩
                  refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
                  rw [evaluateApp, targetFound]
                  dsimp only
                  rw [if_neg targetEnough, targetCost, fixClock_evaluate, targetBodyRun]
                  exact targetRun
end AppPort

end Flapjack.Compiler.Backend.ClosFvs
