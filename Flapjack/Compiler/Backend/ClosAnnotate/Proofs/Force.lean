import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.ThunkOperations

/-! Simulation of forcing thunks under closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The evaluator simulation restricted to one source state, for the
clock-and-expression-weight induction used by the evaluator. -/
def EvalSimulationAt {C F : Type} (source : State C F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env nextEnv : List Value) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State C F) (m l : Nat) (index : Spt Nat),
    evaluate expressions env source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → env.length = m + l →
    (∀ n, altFv n expressions = true → EnvOk m l index env nextEnv n) →
    everyFnVarsNone expressions → CodeSafe source → OracleSafe source → StateRel source target →
    ∃ targetResult targetNext,
      evaluate (shiftList (altFree expressions).1 m l index) nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext

/-- An unrestricted simulation supplies its corresponding local induction case. -/
theorem evalSimulation_at {C F : Type} {expressions : List ClosLang.Exp}
    (simulation : EvalSimulation (C := C) (F := F) expressions) (source : State C F) :
    EvalSimulationAt source expressions := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  exact simulation env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states

/-- Specialize the generated-call induction case to its one-slot environment.
The call contains no closures and annotation leaves it unchanged. -/
theorem forceCall_related {C F : Type} (source target : State C F)
    (value nextValue : Value) (result : Result (List Value) Value) (last : State C F)
    (simulation : EvalSimulationAt source [appUnit (.var .none 0)])
    (run : evaluate [appUnit (.var .none 0)] [value] source = (result, last))
    (noType : result ≠ .err (.abort .typeError)) (valueRel : ValueRel value nextValue)
    (code : CodeSafe source) (oracle : OracleSafe source) (states : StateRel source target) :
    ∃ nextResult nextLast, evaluate [appUnit (.var .none 0)] [nextValue] target = (nextResult, nextLast) ∧
      ResultRel result nextResult ∧ StateRel last nextLast := by
  have vars : ∀ n, altFv n [appUnit (.var .none 0)] = true →
      EnvOk 0 1 .ln [value] [nextValue] n := by
    intro n present
    cases n with
    | zero =>
      apply EnvOk.local 0 1 .ln [value] [nextValue] 0 (by decide)
      · simpa [holEl, holHd] using valueRel
      · simp
      · simp
    | succ n => exact EnvOk.outside 0 1 .ln [value] [nextValue] (n + 1) (by omega)
  have safe : everyFnVarsNone [appUnit (.var .none 0)] := by
    simp [appUnit, everyFnVarsNone, fnVarsNoneExp]
  obtain ⟨nextResult, nextLast, nextRun, related, lastRel⟩ :=
    simulation [value] [nextValue] target result last 0 1 .ln run noType (by simp) vars safe code oracle states
  refine ⟨nextResult, nextLast, ?_, related, lastRel⟩
  simpa [appUnit, altFree, altFreeList, altFreeSing, shiftList, shiftSing, getVar] using nextRun

/-- The force case composes argument evaluation, the generated call, and the
store update. The call hypothesis is the smaller-expression induction case at
any state reachable after evaluating the arguments. -/
theorem evaluate_force_step {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (source : State C F) (argsIH : EvalSimulationAt source args)
    (forceIH : ∀ middle : State C F, middle.clock ≤ source.clock →
      EvalSimulationAt middle [appUnit (.var .none 0)]) :
    EvalSimulationAt source [.op trace (.thunkOp .forceThunk) args] := by
  intro env nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_op] using present
  have argsSafe : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [FlatToClos.evaluate_op_error args env source middle error trace _ argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) sourceNext m l index argsRun noType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        rw [altFree_op]
        simp only [shiftList, shiftSing]
        exact FlatToClos.evaluate_op_error _ _ _ _ _ _ _ targetRun
    | val values =>
      have valuesNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle m l index argsRun valuesNoType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val nextValues =>
        have middleClock : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le args env source
          simpa [argsRun] using h
        have middleSafe := (evaluate_preserves_safe.1 args) env source (.val values) middle argsRun code oracle
        have inspected := destThunk_list_related middle targetMiddle values nextValues resultRel middleRel
        rw [evaluate, fixClock_evaluate, argsRun] at run
        dsimp only at run
        cases sourceThunk : destThunk values middle.refs with
        | badRef =>
          rw [sourceThunk] at run
          simp at run
          exact False.elim (noType run.1.symm)
        | notThunk =>
          rw [sourceThunk] at run
          simp at run
          exact False.elim (noType run.1.symm)
        | isThunk mode value =>
          cases targetThunk : destThunk nextValues targetMiddle.refs with
          | badRef => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | notThunk => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | isThunk targetMode targetValue =>
            have rel : mode = targetMode ∧ ValueRel value targetValue := by
              simpa [DestThunkRel, sourceThunk, targetThunk] using inspected
            obtain ⟨rfl, valueRel⟩ := rel
            cases mode with
            | evaluated =>
              rw [sourceThunk] at run
              cases run
              refine ⟨.val [targetValue], targetMiddle, ?_, .cons valueRel .nil, middleRel⟩
              rw [altFree_op]
              simp only [shiftList, shiftSing]
              rw [evaluate, fixClock_evaluate, targetRun]
              dsimp only
              rw [targetThunk]
            | notEvaluated =>
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
              | mk forceResult last =>
                cases forceResult with
                | err error =>
                  rw [sourceThunk] at run
                  dsimp only at run
                  rw [forceRun] at run
                  cases run
                  obtain ⟨targetForceResult, targetLast, targetForceRun, related, lastRel⟩ :=
                    forceCall_related middle targetMiddle value targetValue (.err error) last
                      (forceIH middle middleClock) forceRun noType valueRel middleSafe.1 middleSafe.2 middleRel
                  cases targetForceResult with
                  | val values => cases error <;> simp [ResultRel] at related
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, related, lastRel⟩
                    rw [altFree_op]
                    simp only [shiftList, shiftSing]
                    rw [evaluate, fixClock_evaluate, targetRun]
                    dsimp only
                    rw [targetThunk]
                    dsimp only
                    rw [targetForceRun]
                | val forced =>
                  have forceNoType : (Result.val forced : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetForceResult, targetLast, targetForceRun, related, lastRel⟩ :=
                    forceCall_related middle targetMiddle value targetValue (.val forced) last
                      (forceIH middle middleClock) forceRun forceNoType valueRel middleSafe.1 middleSafe.2 middleRel
                  cases targetForceResult with
                  | err error => cases error <;> simp [ResultRel] at related
                  | val nextForced =>
                    have update := updateThunk_related last targetLast values nextValues forced nextForced
                      resultRel related lastRel
                    cases updateRun : updateThunk values last.refs forced with
                    | none =>
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      simp at run
                      exact False.elim (noType run.1.symm)
                    | some refs =>
                      rw [updateRun] at update
                      obtain ⟨targetRefs, targetUpdate, updatedRel⟩ := update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.val nextForced, { targetLast with refs := targetRefs }, ?_, related, updatedRel⟩
                      rw [altFree_op]
                      simp only [shiftList, shiftSing]
                      rw [evaluate, fixClock_evaluate, targetRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      rw [targetForceRun]
                      dsimp only
                      rw [targetUpdate]

end Flapjack.Compiler.Backend.ClosAnnotate
