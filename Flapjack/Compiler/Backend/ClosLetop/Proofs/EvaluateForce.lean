import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateOp
import Flapjack.Compiler.Backend.ClosLetop.Proofs.Force

/-! Thunk-forcing case of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace EvaluateForcePort
/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateForcePort

/-- Forcing simulates thunk inspection, the generated call, and its update. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_force {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (forceIH : ∀ (values : List Value) (middle : State C F) (value : Value),
      evaluate args env source = (.val values, middle) →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [appUnit (.var .none 0)] [value] middle = (result, next) ∧
          List.Forall₂ ValueRel [value] nextEnv ∧ StateRel middle target ∧
          CodeRel [appUnit (.var .none 0)] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace (.thunkOp .forceThunk) args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.op trace (.thunkOp .forceThunk) args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace (.thunkOp .forceThunk) (compileList args)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (compileList args) nextEnv target
        ⟨argsRun, envRel, states, rfl⟩
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate, fixClock_evaluate, targetArgsRun], argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have inspected := destThunk_list_related middle targetMiddle values targetValues argsRel middleRel
        rw [evaluate, fixClock_evaluate, argsRun] at run
        dsimp only at run
        cases sourceThunk : destThunk values middle.refs with
        | badRef =>
          cases targetThunk : destThunk targetValues targetMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [sourceThunk] at run
          cases run
          refine ⟨.err (.abort .typeError), targetMiddle, ?_, rfl, middleRel⟩
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          dsimp only
          rw [targetThunk]
          simp
        | notThunk =>
          cases targetThunk : destThunk targetValues targetMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [sourceThunk] at run
          cases run
          refine ⟨.err (.abort .typeError), targetMiddle, ?_, rfl, middleRel⟩
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          dsimp only
          rw [targetThunk]
          simp
        | isThunk mode value =>
          cases targetThunk : destThunk targetValues targetMiddle.refs with
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
              rw [evaluate, fixClock_evaluate, targetArgsRun]
              dsimp only
              rw [targetThunk]
            | notEvaluated =>
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
              | mk forceResult last =>
                obtain ⟨targetForceResult, targetLast, targetForceRun, forceRel, lastRel⟩ :=
                  forceIH values middle value argsRun sourceThunk forceResult last [appUnit (.var .none 0)]
                    [targetValue] targetMiddle ⟨forceRun, .cons valueRel .nil, middleRel,
                      by simp [CodeRel, compileList, compileSing, appUnit]⟩
                cases forceResult with
                | err error =>
                  rw [sourceThunk] at run
                  dsimp only at run
                  rw [forceRun] at run
                  cases run
                  cases targetForceResult with
                  | val vals => cases error <;> simp [ResultRel] at forceRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, forceRel, lastRel⟩
                    rw [evaluate, fixClock_evaluate, targetArgsRun]
                    dsimp only
                    rw [targetThunk]
                    dsimp only
                    rw [targetForceRun]
                | val forced =>
                  cases targetForceResult with
                  | err error => cases error <;> simp [ResultRel] at forceRel
                  | val targetForced =>
                    have update := updateThunk_related last targetLast values targetValues forced targetForced
                      argsRel forceRel lastRel
                    cases updateRun : updateThunk values last.refs forced with
                    | none =>
                      have targetUpdate : updateThunk targetValues targetLast.refs targetForced = none := by
                        simpa [updateRun] using update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.err (.abort .typeError), targetLast, ?_, rfl, lastRel⟩
                      rw [evaluate, fixClock_evaluate, targetArgsRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      rw [targetForceRun]
                      dsimp only
                      rw [targetUpdate]
                      simp
                    | some refs =>
                      rw [updateRun] at update
                      obtain ⟨targetRefs, targetUpdate, updatedRel⟩ := update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.val targetForced, { targetLast with refs := targetRefs }, ?_, forceRel, updatedRel⟩
                      rw [evaluate, fixClock_evaluate, targetArgsRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      rw [targetForceRun]
                      dsimp only
                      rw [targetUpdate]

end Flapjack.Compiler.Backend.ClosLetop
