import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.RecursiveFunctions
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Force

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
  induction pairs generalizing i arity body with
  | nil => simp at found
  | @cons left right functions nextFunctions head tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst left
      obtain ⟨m, index, equalArity, shifted, live, safe, length⟩ := head
      obtain ⟨nextArity, nextBody⟩ := right
      simp only at equalArity shifted
      subst nextArity
      exact ⟨nextBody, m, index, by simp, shifted, live, safe, length⟩
    | succ i =>
      have rest : functions[i]? = some (arity, body) := by simpa using found
      obtain ⟨nextBody, m, index, target, shifted, live, safe, length⟩ :=
        ih i arity body ((functionsRel_iff env nextEnv count functions nextFunctions).mpr tail) rest
      exact ⟨nextBody, m, index, by simpa using target, shifted, live, safe, length⟩

/-- The corresponding function bundles have the same length. -/
theorem functionsRel_length (env nextEnv : List Value) (count : Nat)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (related : FunctionsRel env nextEnv count functions nextFunctions) :
    functions.length = nextFunctions.length := by
  exact ((functionsRel_iff env nextEnv count functions nextFunctions).mp related).length_eq

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
      rw [if_pos insufficient] at run
      cases run
      refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [if_pos targetInsufficient]
        rfl
      · exact stateRel_withClock states 0
    · have targetEnough : ¬ target.clock < (nextFirst :: nextRest).length := by
        simpa [← clockEq, ← lengthEq] using insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [if_neg insufficient] at run
      cases run
      refine ⟨.val [nextPartial], decClock (nextFirst :: nextRest).length target, ?_, ?_, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [if_neg targetEnough]
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
  · simpa [evaluateApp, ResultRel] using List.Forall₂.cons related .nil
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

end Flapjack.Compiler.Backend.ClosAnnotate
