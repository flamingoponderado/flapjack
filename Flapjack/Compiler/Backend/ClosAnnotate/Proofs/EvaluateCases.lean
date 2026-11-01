import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Initial cases of closure-annotation evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Related results preserve aborts and relate normal and raised values. -/
def ResultRel : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

/-- All source code bodies lack pre-existing capture annotations. -/
def CodeSafe {C F : Type} (state : State C F) : Prop :=
  ∀ key arity body, state.code.lookup key = some (arity, body) → everyFnVarsNone [body]

/-- All future oracle programs lack pre-existing capture annotations. -/
def OracleSafe {C F : Type} (state : State C F) : Prop :=
  ∀ index, everyFnVarsNone (state.compileOracle index).2.1 ∧
    everyFnVarsNone ((state.compileOracle index).2.2.map (fun (_, _, body) => body))

/-- Source-shaped simulation obligation for shifting an expression list.
The proof-side carriers and evaluator remain pending HOL correspondence review. -/
def EvalSimulation {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (source : State C F) (nextEnv : List Value) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State C F) (m l : Nat) (index : Spt Nat),
    evaluate expressions env source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → env.length = m + l →
    (∀ n, altFv n expressions = true → EnvOk m l index env nextEnv n) →
    everyFnVarsNone expressions → CodeSafe source → OracleSafe source → StateRel source target →
    ∃ targetResult targetNext,
      evaluate (shiftList (altFree expressions).1 m l index) nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext

/-- Preservation obligation for code and oracle safety across evaluation.
The general proof for arbitrary expressions and applications remains open. -/
def PreservesCodeOracle {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (source : State C F) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → CodeSafe source → OracleSafe source →
    CodeSafe next ∧ OracleSafe next

/-- Code and oracle safety preservation from one source state. -/
def PreservesCodeOracleAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env : List Value) (result : Result (List Value) Value) (next : State C F),
    evaluate expressions env source = (result, next) → CodeSafe source → OracleSafe source →
    CodeSafe next ∧ OracleSafe next

/-- Restrict an unrestricted safety proof to one state. -/
theorem preservesCodeOracle_at {C F : Type} {expressions : List ClosLang.Exp}
    (safe : PreservesCodeOracle (C := C) (F := F) expressions) (source : State C F) :
    PreservesCodeOracleAt source expressions := by
  intro env result next run code oracle
  exact safe env source result next run code oracle

/-- Empty expression lists preserve evaluation and state. -/
theorem evaluate_nil {C F : Type} : EvalSimulation (C := C) (F := F) [] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [], target, by simp [altFree_nil, shiftList, evaluate], .nil, states⟩

/-- Variable evaluation is preserved by the compact environment mapping. -/
theorem evaluate_var {C F : Type} (trace : BackendCommon.Tra) (variableIndex : Nat) :
    EvalSimulation (C := C) (F := F) [.var trace variableIndex] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  cases found : env[variableIndex]? with
  | none =>
    simp [evaluate, found] at run
    exact False.elim (noType run.1.symm)
  | some value =>
    have sourceInfo := List.getElem?_eq_some_iff.mp found
    have tracked : variableIndex < l + m := by
      have bound := sourceInfo.1
      omega
    have rel := envOk_getVar m l index env nextEnv variableIndex
      (vars variableIndex (by simp [altFv_var])) tracked
    let _ : Nonempty Value := ⟨unitValue⟩
    let targetValue := Flapjack.holEl (getVar m l index variableIndex) nextEnv
    have sourceValue : Flapjack.holEl variableIndex env = value := by
      rw [Flapjack.holEl_eq_getElem _ _ sourceInfo.1]
      exact sourceInfo.2
    have targetLookup : nextEnv[getVar m l index variableIndex]? = some targetValue := by
      simp [targetValue, Flapjack.holEl_eq_getElem _ _ rel.2.1, rel.2.1]
    have valueRel : ValueRel value targetValue := by
      simpa [sourceValue, targetValue] using rel.2.2
    simp [evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.val [targetValue], target, ?_, .cons valueRel .nil, states⟩
    simp [altFree_var, shiftList, shiftSing, evaluate, targetLookup]

/-- Sequence two or more expressions when their simulations and the first
expression's code/oracle safety preservation are available. -/
theorem evaluate_cons {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (firstIH : EvalSimulation (C := C) (F := F) [first])
    (restIH : EvalSimulation (C := C) (F := F) (second :: rest))
    (firstSafety : PreservesCodeOracle (C := C) (F := F) [first]) :
    EvalSimulation (C := C) (F := F) (first :: second :: rest) := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have firstVars : ∀ n, altFv n [first] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_cons]
    simp [present]
  have restVars : ∀ n, altFv n (second :: rest) = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    rw [altFv_cons]
    simp [present]
  have safety : everyFnVarsNone [first] ∧ everyFnVarsNone (second :: rest) := by
    simpa [everyFnVarsNone] using safe
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      have fullRun := ClosProps.evaluate_cons_error first (second :: rest) env source middle error firstRun
      rw [fullRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        firstIH env source nextEnv target (.err error) sourceNext m l index
          firstRun noType length firstVars safety.1 code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp only [altFree, altFreeList, shiftList]
        exact ClosProps.evaluate_cons_error _ _ _ _ _ _ targetRun
    | val values =>
      have valueLength := (evaluate_length (C := C) (F := F)).1 [first] env source middle values firstRun
      cases values with
      | nil => simp at valueLength
      | cons value tail =>
        cases tail with
        | cons other tail => simp at valueLength
        | nil =>
          have firstNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
            firstIH env source nextEnv target (.val [value]) middle m l index
              firstRun firstNoType length firstVars safety.1 code oracle states
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have middleSafety := firstSafety env source (.val [value]) middle firstRun code oracle
              cases restRun : evaluate (second :: rest) env middle with
              | mk restResult last =>
                have fullRun := ClosProps.evaluate_cons_value first (second :: rest) env source middle value firstRun
                rw [restRun] at fullRun
                cases restResult with
                | err error =>
                  simp only at fullRun
                  rw [fullRun] at run
                  cases run
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    restIH env middle nextEnv targetMiddle (.err error) sourceNext m l index
                      restRun noType length restVars safety.2 middleSafety.1 middleSafety.2 middleRel
                  cases targetRestResult with
                  | val values => cases error <;> simp [ResultRel] at restRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, restRel, lastRel⟩
                    simp only [altFree_singleton, shiftList] at targetRun
                    simp only [altFree, altFreeList, shiftList] at targetRestRun ⊢
                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]

                | val values =>
                  simp only at fullRun
                  rw [fullRun] at run
                  cases run
                  have restNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    restIH env middle nextEnv targetMiddle (.val values) sourceNext m l index
                      restRun restNoType length restVars safety.2 middleSafety.1 middleSafety.2 middleRel
                  cases targetRestResult with
                  | err error => cases error <;> simp [ResultRel] at restRel
                  | val targetValues =>
                    refine ⟨.val (targetValue :: targetValues), targetLast, ?_, .cons valueRel restRel, lastRel⟩
                    simp only [altFree_singleton, shiftList] at targetRun
                    simp only [altFree, altFreeList, shiftList] at targetRestRun ⊢
                    rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]


/-- Tick preserves the annotation simulation when its body does. -/
theorem evaluate_tick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.tick trace body] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have bodyVars : ∀ n, altFv n [body] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_tick] using present
  have bodySafe : everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by rw [← states.1]; exact zero
    simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.err (.abort .timeoutError), target, ?_, rfl, states⟩
    simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetZero]
  · have targetNonzero : target.clock ≠ 0 := by rw [← states.1]; exact zero
    have clocks : StateRel (decClock 1 source) (decClock 1 target) := by
      simpa [decClock, ← states.1] using stateRel_withClock states (source.clock - 1)
    have bodyRun : evaluate [body] env (decClock 1 source) = (result, sourceNext) := by
      simpa [evaluate, zero] using run
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH env (decClock 1 source) nextEnv (decClock 1 target) result sourceNext m l index
        bodyRun noType length bodyVars bodySafe (by simpa [CodeSafe, decClock] using code)
        (by simpa [OracleSafe, decClock] using oracle) clocks
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    simpa [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetNonzero] using targetRun

/-- Raising a value preserves the annotation relation when the body does. -/
theorem evaluate_raise {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.raise trace body] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have bodyVars : ∀ n, altFv n [body] = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_raise] using present
  have bodySafe : everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyNext =>
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      obtain ⟨rfl, rfl⟩ := run
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env source nextEnv target (.err error) bodyNext m l index
          bodyRun noType length bodyVars bodySafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetNext, ?_, resultRel, nextRel⟩
        simp only [altFree_singleton, shiftList] at targetRun
        simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetRun]
    | val values =>
      have valueLength := (evaluate_length (C := C) (F := F)).1 [body] env source bodyNext values bodyRun
      have bodyNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env source nextEnv target (.val values) bodyNext m l index
          bodyRun bodyNoType length bodyVars bodySafe code oracle states
      cases values with
      | nil => simp at valueLength
      | cons value tail =>
        cases tail with
        | cons first rest => simp at valueLength
        | nil =>
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel restRel =>
              cases restRel
              simp [evaluate, bodyRun] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.err (.raise _), targetNext, ?_, valueRel, nextRel⟩
              simp only [altFree_singleton, shiftList] at targetRun
              simp [altFree_singleton, altFreeSing, shiftList, shiftSing, evaluate, targetRun]

end Flapjack.Compiler.Backend.ClosAnnotate
