module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.RecursiveFunctions
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Force

@[expose] public section

/-! Closure application prerequisites for annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Selecting a recursive function selects a corresponding body, preserving
its arity and the hypotheses needed to simulate that body. -/
theorem functionsRel_getElem (env nextEnv : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × ClosLang.Exp)) (i arity : Nat) (body : ClosLang.Exp)
    (related : FunctionsRel env nextEnv count functions nextFunctions)
    (found : functions[i]? = some (arity, body)) :
    ∃ nextBody m index, nextFunctions[i]? = some (arity, nextBody) ∧
      shiftList (altFree [body]).1 m (count + arity) index = [nextBody] ∧
      (∀ n, altFv n [body] = true → arity + count ≤ n →
        EnvOk m 0 index env nextEnv (n - (arity + count))) ∧
      everyFnVarsNone [body] ∧ env.length = m := by
  have pairs := (functionsRel_iff env nextEnv count functions nextFunctions).mp related
  have sourceBound : i < functions.length := (List.getElem?_eq_some_iff.mp found).1
  have sourceEq : functions[i]'sourceBound = (arity, body) := (List.getElem?_eq_some_iff.mp found).2
  have targetBound : i < nextFunctions.length := by simpa only [pairs.length_eq] using sourceBound
  have head := pairs.get sourceBound targetBound
  simp only [List.get_eq_getElem, sourceEq] at head
  cases targetEq : nextFunctions[i]'targetBound with
  | mk nextArity nextBody =>
    rw [targetEq] at head
    obtain ⟨m, index, equalArity, shifted, live, safe, length⟩ := head
    simp only at equalArity shifted
    subst nextArity
    simp only [shiftSource_eq_shiftList, altFreeSource_eq_altFree] at shifted
    simp only [altFvSource_eq_altFv, and_imp] at live
    exact ⟨nextBody, m, index, by simpa [List.getElem?_eq_getElem targetBound] using congrArg some targetEq,
      shifted, live, safe, length⟩

/-- The corresponding function bundles have the same length. -/
theorem functionsRel_length (env nextEnv : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (related : FunctionsRel env nextEnv count functions nextFunctions) :
    functions.length = nextFunctions.length := by
  exact ((functionsRel_iff env nextEnv count functions nextFunctions).mp related).length_eq

/-- Related argument and recursive-closure prefixes provide the local slots
needed to evaluate an annotated closure body. -/
theorem envOk_application_body (body : ClosLang.Exp) (m localCount : Nat) (index : Spt Nat)
    (env nextEnv front nextFront : List Value) (frontRel : List.Forall₂ ValueRel front nextFront)
    (frontLength : front.length = localCount)
    (live : ∀ n, altFv n [body] = true → localCount ≤ n →
      EnvOk m 0 index env nextEnv (n - localCount)) :
    ∀ n, altFv n [body] = true → EnvOk m localCount index (front ++ env) (nextFront ++ nextEnv) n := by
  intro n present
  have extended := envOk_extend front nextFront front.length n m 0 index env nextEnv ⟨frontRel, rfl, by
    intro bound
    simpa [frontLength] using live n present (by simpa [frontLength] using bound)⟩
  simpa [frontLength] using extended

/-- Full applications expose an annotated body together with matching
arguments, captured-variable assumptions, and over-application tails. -/
theorem destClosure_related_full (maxApp : Nat) (requested : Option Nat)
    (function nextFunction : Value) (args nextArgs : List Value)
    (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (related : ValueRel function nextFunction) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested function args = some (.fullApp body bodyEnv remaining)) :
    ∃ nextBody nextBodyEnv nextRemaining m localCount index,
      destClosure maxApp requested nextFunction nextArgs = some (.fullApp nextBody nextBodyEnv nextRemaining) ∧
      shiftList (altFree [body]).1 m localCount index = [nextBody] ∧
      bodyEnv.length = m + localCount ∧
      (∀ n, altFv n [body] = true → EnvOk m localCount index bodyEnv nextBodyEnv n) ∧
      everyFnVarsNone [body] ∧ List.Forall₂ ValueRel remaining nextRemaining := by
  cases related with
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ => simp [destClosure] at run
  | closure location supplied nextSupplied env nextEnv arity m original nextBody index shifted live safe length suppliedRel =>
    simp only [shiftSource_eq_shiftList, altFreeSource_eq_altFree] at shifted
    simp only [altFvSource_eq_altFv, and_imp] at live
    have argsLen := argsRel.length_eq
    have suppliedLen := suppliedRel.length_eq
    by_cases valid : checkLoc maxApp requested location arity args.length supplied.length && supplied.length < arity
    · by_cases part : args.length + supplied.length < arity
      · simp [destClosure, valid, part] at run
      · simp [destClosure, valid, part] at run
        obtain ⟨rfl, rfl, rfl⟩ := run
        let needed := arity - supplied.length
        let front := (args.reverse.take needed).reverse ++ supplied
        let nextFront := (nextArgs.reverse.take needed).reverse ++ nextSupplied
        have suppliedBound : supplied.length < arity := by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          exact valid.2
        have frontLength : front.length = arity := by
          simp only [front, List.length_append, List.length_reverse, List.length_take]
          dsimp [needed]
          omega
        have frontRel : List.Forall₂ ValueRel front nextFront :=
          List.rel_append (List.rel_reverse (List.forall₂_take needed (List.rel_reverse argsRel))) suppliedRel
        refine ⟨nextBody, nextFront ++ nextEnv, (nextArgs.reverse.drop needed).reverse,
          m, arity, index, ?_, shifted, ?_, ?_, safe, ?_⟩
        · simp [destClosure, ← argsLen, ← suppliedLen, valid, part, needed, nextFront, List.append_assoc]
        · have h : (front ++ env).length = m + arity := by simp [frontLength, length, Nat.add_comm]
          simpa [front, List.append_assoc] using h
        · simpa [front, nextFront, List.append_assoc] using
            envOk_application_body original m arity index env nextEnv front nextFront frontRel frontLength live
        · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse argsRel))
    · simp [destClosure, valid] at run
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions funIndex functionsRel suppliedRel bound =>
    cases found : functions[funIndex]? with
    | none => simp [destClosure, found] at run
    | some entry =>
      obtain ⟨arity, original⟩ := entry
      obtain ⟨nextBody, m, index, nextFound, shifted, live, safe, length⟩ :=
        functionsRel_getElem env nextEnv functions.length functions nextFunctions funIndex arity original functionsRel found
      have argsLen := argsRel.length_eq
      have suppliedLen := suppliedRel.length_eq
      have funLength := functionsRel_length env nextEnv functions.length functions nextFunctions functionsRel
      by_cases valid : checkLoc maxApp requested (location.map (fun loc => 2 * funIndex + loc))
          arity args.length supplied.length && supplied.length < arity
      · by_cases part : args.length + supplied.length < arity
        · simp [destClosure, found, valid, part] at run
        · simp [destClosure, found, valid, part] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          let needed := arity - supplied.length
          let recs := (List.range functions.length).map (fun i => Value.recclosure location [] env functions i)
          let nextRecs := (List.range functions.length).map (fun i => Value.recclosure location [] nextEnv nextFunctions i)
          let front := (args.reverse.take needed).reverse ++ supplied ++ recs
          let nextFront := (nextArgs.reverse.take needed).reverse ++ nextSupplied ++ nextRecs
          have suppliedBound : supplied.length < arity := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            exact valid.2
          have frontLength : front.length = arity + functions.length := by
            simp only [front, recs, List.length_append, List.length_reverse, List.length_take,
              List.length_map, List.length_range]
            dsimp [needed]
            omega
          have frontRel : List.Forall₂ ValueRel front nextFront :=
            List.rel_append (List.rel_append (List.rel_reverse (List.forall₂_take needed (List.rel_reverse argsRel))) suppliedRel)
              (recursiveValues_related location env nextEnv functions nextFunctions functionsRel)
          refine ⟨nextBody, nextFront ++ nextEnv, (nextArgs.reverse.drop needed).reverse,
            m, arity + functions.length, index, ?_, ?_, ?_, ?_, safe, ?_⟩
          · simp [destClosure, nextFound, ← argsLen, ← suppliedLen, ← funLength, valid, part,
              needed, nextFront, nextRecs, List.append_assoc]
          · simpa [Nat.add_comm] using shifted
          · have h : (front ++ env).length = m + (arity + functions.length) := by
              simp [frontLength, length, Nat.add_comm]
            simpa [front, recs, List.append_assoc] using h
          · simpa [front, nextFront, recs, nextRecs, List.append_assoc] using
              envOk_application_body original m (arity + functions.length) index env nextEnv front nextFront frontRel frontLength live
          · exact List.rel_reverse (List.forall₂_drop needed (List.rel_reverse argsRel))
      · simp [destClosure, found, valid] at run

/-- A partial application accumulates related arguments in related closures.
This covers both direct and indirect applications and recursive closures. -/
theorem destClosure_related_partial (maxApp : Nat) (requested : Option Nat)
    (function nextFunction : Value) (args nextArgs : List Value) (result : Value)
    (related : ValueRel function nextFunction) (argsRel : List.Forall₂ ValueRel args nextArgs)
    (run : destClosure maxApp requested function args = some (.partialApp result)) :
    ∃ nextResult, destClosure maxApp requested nextFunction nextArgs = some (.partialApp nextResult) ∧
      ValueRel result nextResult := by
  cases related with
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ => simp [destClosure] at run
  | closure location supplied nextSupplied env nextEnv arity m body nextBody index shifted live safe length suppliedRel =>
    have argsLen := argsRel.length_eq
    have suppliedLen := suppliedRel.length_eq
    by_cases valid : checkLoc maxApp requested location arity args.length supplied.length && supplied.length < arity
    · by_cases part : args.length + supplied.length < arity
      · have resultEq : result = .closure location (args ++ supplied) env arity body := by
          simpa [destClosure, valid, part] using run.symm
        subst result
        refine ⟨.closure location (nextArgs ++ nextSupplied) nextEnv arity nextBody, ?_, ?_⟩
        · simp [destClosure, ← argsLen, ← suppliedLen, valid, part]
        · exact .closure location _ _ env nextEnv arity m body nextBody index shifted live safe length
            (List.rel_append argsRel suppliedRel)
      · simp [destClosure, valid, part] at run
    · simp [destClosure, valid] at run
  | recclosure location supplied nextSupplied env nextEnv functions nextFunctions index functionsRel suppliedRel bound =>
    cases found : functions[index]? with
    | none => simp [destClosure, found] at run
    | some entry =>
      obtain ⟨arity, body⟩ := entry
      obtain ⟨nextBody, m, idx, nextFound, shifted, live, safe, length⟩ :=
        functionsRel_getElem env nextEnv functions.length functions nextFunctions index arity body functionsRel found
      have argsLen := argsRel.length_eq
      have suppliedLen := suppliedRel.length_eq
      by_cases valid : checkLoc maxApp requested (location.map (fun loc => 2 * index + loc))
          arity args.length supplied.length && supplied.length < arity
      · by_cases part : args.length + supplied.length < arity
        · have resultEq : result = .recclosure location (args ++ supplied) env functions index := by
            simpa [destClosure, found, valid, part] using run.symm
          subst result
          refine ⟨.recclosure location (nextArgs ++ nextSupplied) nextEnv nextFunctions index, ?_, ?_⟩
          · simp [destClosure, nextFound, ← argsLen, ← suppliedLen, valid, part]
          · exact .recclosure location _ _ env nextEnv functions nextFunctions index functionsRel
              (List.rel_append argsRel suppliedRel) bound
        · simp [destClosure, found, valid, part] at run
      · simp [destClosure, found, valid] at run

/-- Partial application either times out in both states or returns related
closures after consuming the same clock. -/
theorem evaluateApp_partial {C F : Type} (requested : Option Nat) (function nextFunction first : Value)
    (rest nextArgs : List Value) (source target : State C F) (partialValue : Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (sourceNext : State C F)
    (run : evaluateApp requested function (first :: rest) source = (result, sourceNext))
    (found : destClosure source.maxApp requested function (first :: rest) = some (.partialApp partialValue))
    (related : ValueRel function nextFunction)
    (argsRel : List.Forall₂ ValueRel (first :: rest) nextArgs) (states : StateRel source target) :
    ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨nextPartial, nextFound, partialRel⟩ :=
    destClosure_related_partial source.maxApp requested function nextFunction (first :: rest) nextArgs partialValue
      related argsRel found
  have maxEq : source.maxApp = target.maxApp := states.2.2.1
  have clockEq : source.clock = target.clock := states.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    have targetFound : destClosure target.maxApp requested nextFunction (nextFirst :: nextRest) =
        some (.partialApp nextPartial) := by simpa [← maxEq] using nextFound
    by_cases insufficient : source.clock < (first :: rest).length
    · have targetInsufficient : target.clock < (nextFirst :: nextRest).length := by
        simpa [← clockEq, ← lengthEq] using insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [ite_eq_left insufficient] at run
      cases run
      refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [ite_eq_left targetInsufficient]
        rfl
      · exact stateRel_withClock states 0
    · have targetEnough : ¬ target.clock < (nextFirst :: nextRest).length := by
        simpa [← clockEq, ← lengthEq] using insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [ite_eq_right insufficient] at run
      cases run
      refine ⟨.val [nextPartial], decClock (nextFirst :: nextRest).length target, ?_, ?_, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [ite_eq_right targetEnough]
      · exact .cons partialRel .nil
      · simpa [decClock, ← clockEq, ← lengthEq] using
          stateRel_withClock states (source.clock - (first :: rest).length)

/-- Applying no arguments returns related values and leaves the states intact. -/
theorem evaluateApp_empty {C F : Type} (requested : Option Nat) (function nextFunction : Value)
    (source target : State C F) (related : ValueRel function nextFunction)
    (states : StateRel source target) :
    ∃ targetResult targetNext, evaluateApp requested nextFunction [] target = (targetResult, targetNext) ∧
      ResultRel (evaluateApp requested function [] source).1 targetResult ∧
      StateRel (evaluateApp requested function [] source).2 targetNext := by
  refine ⟨.val [nextFunction], target, ?_, ?_, ?_⟩
  · rw [evaluateApp]
  · simpa [evaluateApp, ResultRel, Flapjack.SemanticPrimitivesProps.resultRel, Flapjack.SemanticPrimitivesProps.excRel] using List.Forall₂.cons related .nil
  · simpa [evaluateApp] using states

/-- A failed closure lookup produces the type error excluded by the
simulation theorem's original non-type-error condition. -/
theorem evaluateApp_rejected {C F : Type} (requested : Option Nat) (function first : Value)
    (rest : List Value) (source : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (sourceNext : State C F)
    (run : evaluateApp requested function (first :: rest) source = (result, sourceNext))
    (rejected : destClosure source.maxApp requested function (first :: rest) = none)
    (noType : result ≠ .err (.abort .typeError)) : False := by
  rw [evaluateApp, rejected] at run
  dsimp only at run
  cases run
  exact noType rfl

/-- Simulation of application at clocks below a bound, used for the
recursive application of a full call's result to remaining arguments. -/
def AppSimulationClockBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (requested : Option Nat) (function nextFunction : Value) (args nextArgs : List Value)
    (source target : State C F) (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (sourceNext : State C F),
    source.clock < clock → evaluateApp requested function args source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → ValueRel function nextFunction →
    List.Forall₂ ValueRel args nextArgs → CodeSafe source → OracleSafe source → StateRel source target →
    ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext

/-- A full application composes its smaller-clock body simulation with the
smaller-clock application of any remaining arguments. -/
theorem evaluateApp_full {C F : Type} (requested : Option Nat) (function nextFunction first : Value)
    (rest nextArgs : List Value) (source target : State C F) (body : ClosLang.Exp)
    (bodyEnv remaining : List Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (sourceNext : State C F)
    (run : evaluateApp requested function (first :: rest) source = (result, sourceNext))
    (found : destClosure source.maxApp requested function (first :: rest) = some (.fullApp body bodyEnv remaining))
    (noType : result ≠ .err (.abort .typeError)) (related : ValueRel function nextFunction)
    (argsRel : List.Forall₂ ValueRel (first :: rest) nextArgs)
    (code : CodeSafe source) (oracle : OracleSafe source) (states : StateRel source target)
    (bodyIH : ∀ state : State C F, state.clock < source.clock → EvalSimulationAt state [body])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) source.clock) :
    ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨nextBody, nextEnv, nextRemaining, m, localCount, index, nextFound, shifted,
    envLength, envRel, bodySafe, remainingRel⟩ :=
      destClosure_related_full source.maxApp requested function nextFunction (first :: rest) nextArgs
        body bodyEnv remaining related argsRel found
  have maxEq : source.maxApp = target.maxApp := states.2.2.1
  have clockEq : source.clock = target.clock := states.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  have remainingEq : remaining.length = nextRemaining.length := remainingRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    let cost := (first :: rest).length - remaining.length
    have costPositive : 0 < cost :=
      Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
    have targetCost : (nextFirst :: nextRest).length - nextRemaining.length = cost := by
      simp [cost, ← lengthEq, ← remainingEq]
    have targetFound : destClosure target.maxApp requested nextFunction (nextFirst :: nextRest) =
        some (.fullApp nextBody nextEnv nextRemaining) := by simpa [← maxEq] using nextFound
    by_cases insufficient : source.clock < cost
    · have targetInsufficient : target.clock < (nextFirst :: nextRest).length - nextRemaining.length := by
        rw [targetCost, ← clockEq]
        exact insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [ite_eq_left insufficient] at run
      cases run
      refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl, stateRel_withClock states 0⟩
      rw [evaluateApp, targetFound]
      dsimp only
      rw [ite_eq_left targetInsufficient]
      rfl
    · have bodyClockLess : (decClock cost source).clock < source.clock := by
        simp [decClock]
        omega
      have targetEnough : ¬ target.clock < (nextFirst :: nextRest).length - nextRemaining.length := by
        rw [targetCost, ← clockEq]
        exact insufficient
      have startRel : StateRel (decClock cost source) (decClock cost target) := by
        simpa [decClock, ← clockEq] using stateRel_withClock states (source.clock - cost)
      have startCode : CodeSafe (decClock cost source) := by simpa [CodeSafe, decClock] using code
      have startOracle : OracleSafe (decClock cost source) := by simpa [OracleSafe, decClock] using oracle
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [ite_eq_right insufficient, fixClock_evaluate] at run
      cases bodyRun : evaluate [body] bodyEnv (decClock cost source) with
      | mk bodyResult last =>
        have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bodyResult
          rw [bodyRun] at run
          cases run
          exact noType rfl
        obtain ⟨targetBodyResult, targetLast, targetBodyRun, bodyRel, lastRel⟩ :=
          bodyIH (decClock cost source) bodyClockLess bodyEnv nextEnv (decClock cost target)
            bodyResult last m localCount index bodyRun bodyNoType envLength envRel bodySafe startCode startOracle startRel
        rw [shifted] at targetBodyRun
        cases bodyResult with
        | err error =>
          rw [bodyRun] at run
          cases run
          cases targetBodyResult with
          | val values => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at bodyRel
          | err targetError =>
            refine ⟨.err targetError, targetLast, ?_, bodyRel, lastRel⟩
            rw [evaluateApp, targetFound]
            dsimp only
            rw [ite_eq_right targetEnough, targetCost, fixClock_evaluate, targetBodyRun]
        | val values =>
          have size := (evaluate_length (C := C) (F := F)).1 [body] bodyEnv
            (decClock cost source) last values bodyRun
          cases values with
          | nil => simp at size
          | cons value tail =>
            cases tail with
            | cons value' tail => simp at size
            | nil =>
              cases targetBodyResult with
              | err error => cases error <;> simp [ResultRel, Flapjack.SemanticPrimitivesProps.resultRel] at bodyRel
              | val targetValues =>
                cases bodyRel with
                | cons valueRel tailRel =>
                  cases tailRel
                  rename_i targetValue
                  have appRun : evaluateApp requested value remaining last = (result, sourceNext) := by
                    rw [bodyRun] at run
                    exact run
                  have lastClockLess : last.clock < source.clock := by
                    have bound := evaluate_clock_le [body] bodyEnv (decClock cost source)
                    rw [bodyRun] at bound
                    exact Nat.lt_of_le_of_lt bound bodyClockLess
                  have lastSafe := (evaluate_preserves_safe.1 [body]) bodyEnv (decClock cost source)
                    (.val [value]) last bodyRun startCode startOracle
                  obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                    applicationIH requested value targetValue remaining nextRemaining last targetLast result sourceNext
                      lastClockLess appRun noType valueRel remainingRel lastSafe.1 lastSafe.2 lastRel
                  refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
                  rw [evaluateApp, targetFound]
                  dsimp only
                  rw [ite_eq_right targetEnough, targetCost, fixClock_evaluate, targetBodyRun]
                  exact targetAppRun

/-- One application induction step, using body and recursive application
simulations only at strictly smaller clocks. -/
theorem evaluateApp_clock_step {C F : Type} (requested : Option Nat) (function nextFunction : Value)
    (args nextArgs : List Value) (source target : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value) (sourceNext : State C F)
    (run : evaluateApp requested function args source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError)) (related : ValueRel function nextFunction)
    (argsRel : List.Forall₂ ValueRel args nextArgs)
    (code : CodeSafe source) (oracle : OracleSafe source) (states : StateRel source target)
    (bodyIH : ∀ (body : ClosLang.Exp) (state : State C F), state.clock < source.clock →
      EvalSimulationAt state [body])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) source.clock) :
    ∃ targetResult targetNext, evaluateApp requested nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  cases args with
  | nil =>
    cases argsRel
    have empty := evaluateApp_empty requested function nextFunction source target related states
    rw [run] at empty
    exact empty
  | cons first rest =>
    cases found : destClosure source.maxApp requested function (first :: rest) with
    | none => exact False.elim (evaluateApp_rejected requested function first rest source result sourceNext run found noType)
    | some application =>
      cases application with
      | partialApp partialValue =>
        exact evaluateApp_partial requested function nextFunction first rest nextArgs source target partialValue
          result sourceNext run found related argsRel states
      | fullApp body bodyEnv remaining =>
        exact evaluateApp_full requested function nextFunction first rest nextArgs source target body bodyEnv remaining
          result sourceNext run found noType related argsRel code oracle states (bodyIH body) applicationIH

end Flapjack.Compiler.Backend.ClosAnnotate
