import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Control
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.PureBindings

/-! The let-binding case of the proof-side annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.ClosLang
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Let bindings preserve simulation, including removal of unused pure values.
The evaluator and carriers remain pending HOL correspondence review. -/
theorem evaluate_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bindingsIH : EvalSimulation (C := C) (F := F) bindings)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.let trace bindings body] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : everyFnVarsNone bindings ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp, and_comm] using safe
  by_cases optimized : (noOverlap bindings.length (altFree [body]).2 && pureList bindings) = true
  · have unused : noOverlap bindings.length (altFree [body]).2 = true := (Bool.and_eq_true_iff.mp optimized).1
    have pure : pureList bindings = true := (Bool.and_eq_true_iff.mp optimized).2
    cases bindingsRun : evaluate bindings env source with
    | mk bindingsResult middle =>
      have bindingsNoType : bindingsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst bindingsResult
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        cases run
        exact noType rfl
      obtain ⟨values, resultEq, stateEq, valuesLength⟩ :=
        evaluate_pure_length bindings env source middle bindingsResult pure bindingsRun bindingsNoType
      subst bindingsResult
      subst middle
      have bodyRun : evaluate [body] (values ++ env) source = (result, sourceNext) := by
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        exact run
      have bodyVars : ∀ n, altFv n [body] = true →
          EnvOk m (l + bindings.length) index (values ++ env)
            (List.replicate bindings.length (.number 0) ++ nextEnv) n := by
        intro n present
        exact envOk_unused_bindings trace bindings body m l index env nextEnv values
          valuesLength pure unused vars n present
      have bodyLength : (values ++ env).length = m + (l + bindings.length) := by
        simp only [List.length_append, valuesLength, length]; omega
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH (values ++ env) source (List.replicate bindings.length (.number 0) ++ nextEnv)
          target result sourceNext m (l + bindings.length) index bodyRun noType bodyLength bodyVars
          safeParts.2 code oracle states
      refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
      rw [altFree_let, if_pos optimized]
      simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing, List.length_replicate] at targetRun ⊢
      rw [evaluate, fixClock_evaluate, evaluate_shift_replicate_const0]
      exact targetRun
  · have bindingsVars : ∀ n, altFv n bindings = true → EnvOk m l index env nextEnv n := by
      intro n present
      apply vars n
      rw [altFv_let]
      have noOpt : (noOverlap bindings.length (altFreeList [body]).2 && pureList bindings) ≠ true := optimized
      simp [noOpt, present]
    cases bindingsRun : evaluate bindings env source with
    | mk bindingsResult middle =>
      cases bindingsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, bindingsRun] at run
        cases run
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          bindingsIH env source nextEnv target (.err error) middle m l index bindingsRun
            noType length bindingsVars safeParts.1 code oracle states
        cases targetResult with
        | val values => cases error <;> simp [ResultRel] at resultRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
          rw [altFree_let, if_neg optimized]
          simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing]
          rw [evaluate, fixClock_evaluate, targetRun]
      | val values =>
        have valuesLength := (evaluate_length (C := C) (F := F)).1 bindings env source middle values bindingsRun
        have bindingNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          bindingsIH env source nextEnv target (.val values) middle m l index bindingsRun
            bindingNoType length bindingsVars safeParts.1 code oracle states
        cases targetResult with
        | err error => cases error <;> simp [ResultRel] at resultRel
        | val targetValues =>
          have bodyVars : ∀ n, altFv n [body] = true →
              EnvOk m (l + bindings.length) index (values ++ env) (targetValues ++ nextEnv) n := by
            intro n present
            have extended := envOk_extend m l index values targetValues env nextEnv n resultRel (by
              intro lower
              apply vars (n - values.length)
              rw [altFv_let]
              have shifted : n - values.length + bindings.length = n := by omega
              have noOpt : (noOverlap bindings.length (altFreeList [body]).2 && pureList bindings) ≠ true := optimized
              simp [noOpt, shifted, present])
            simpa [valuesLength] using extended
          have bodyLength : (values ++ env).length = m + (l + bindings.length) := by
            simp only [List.length_append, valuesLength, length]; omega
          have bodyRun : evaluate [body] (values ++ env) middle = (result, sourceNext) := by
            rw [evaluate, fixClock_evaluate, bindingsRun] at run
            exact run
          have middleSafety := (evaluate_preserves_safe.1 bindings) env source (.val values) middle
            bindingsRun code oracle
          obtain ⟨targetBodyResult, targetNext, targetBodyRun, bodyRel, nextRel⟩ :=
            bodyIH (values ++ env) middle (targetValues ++ nextEnv) targetMiddle result sourceNext
              m (l + bindings.length) index bodyRun noType bodyLength bodyVars safeParts.2
              middleSafety.1 middleSafety.2 middleRel
          refine ⟨targetBodyResult, targetNext, ?_, bodyRel, nextRel⟩
          rw [altFree_let, if_neg optimized]
          simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing] at targetBodyRun ⊢
          rw [evaluate, fixClock_evaluate, targetRun]
          simpa [altFree, altFreeList_length] using targetBodyRun

end Flapjack.Compiler.Backend.ClosAnnotate
