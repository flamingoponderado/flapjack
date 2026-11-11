module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateBasic

@[expose] public section

/-! Recursive closure case of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace LetrecPort
/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end LetrecPort

/-- Capture the whole environment or the selected indices. This helper is
Lean-side infrastructure, not a standalone HOL declaration. -/
def captureEnv {α : Type} (selected : Option (List Nat)) (env : List α) : Option (List α) :=
  match selected with | none => some env | some indices => lookupVars indices env

/-- Transformed recursive functions retain related arities and bodies. This
helper is Lean-side infrastructure, not a standalone HOL declaration. -/
theorem compileFuns_related (functions : List (Nat × ClosLang.Exp)) :
    List.Forall₂ FunctionRel functions (compileFuns functions) := by
  induction functions with
  | nil => exact .nil
  | cons function rest ih =>
    rcases function with ⟨arity, body⟩
    exact .cons (by simp [FunctionRel, CodeRel, compileList]) (by simpa [compileFuns] using ih)

/-- Cleanup preserves the number of recursive functions. This helper is
Lean-side infrastructure, not a standalone HOL declaration. -/
theorem compileFuns_length (functions : List (Nat × ClosLang.Exp)) :
    (compileFuns functions).length = functions.length := by
  simp [compileFuns_eq_map]

/-- Cleanup preserves the arity check on recursive functions. This helper is
Lean-side infrastructure, not a standalone HOL declaration. -/
theorem compileFuns_all (maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) :
    (compileFuns functions).all (fun (arity, _) => arity ≤ maxApp && arity != 0) =
      functions.all (fun (arity, _) => arity ≤ maxApp && arity != 0) := by
  simp [compileFuns_eq_map, Function.comp_def]

/-- Recursive closures preserve their indices and related captures. This
helper is Lean-side infrastructure, not a standalone HOL declaration. -/
theorem recursiveClosures_related (location : Option Nat) (env nextEnv : List Value)
    (functions : List (Nat × ClosLang.Exp)) (envRel : List.Forall₂ ValueRel env nextEnv) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range (compileFuns functions).length).map
        (fun i => Value.recclosure location [] nextEnv (compileFuns functions) i)) := by
  rw [compileFuns_length]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] env nextEnv functions _ index envRel .nil
      (compileFuns_related functions)) ih

/-- Recursive closure construction preserves related environments and then
simulates the body under those environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_letrec {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List Value) (source : State C F)
    (bodyIH : ∀ (buildRc : List Value → List Value) (envdelta : Option (List Value)) (ed : List Value),
      functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true →
      buildRc = (fun captured => (List.range functions.length).map
        (fun i => Value.recclosure location [] captured functions i)) →
      envdelta = (captureEnv selected env).map buildRc → envdelta = some ed →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [body] (ed ++ env) source = (result, next) ∧
          List.Forall₂ ValueRel (ed ++ env) nextEnv ∧ StateRel source target ∧
          CodeRel [body] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.letrec names location selected functions body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.letrec names location selected functions body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.letrec names location selected
      (compileFuns functions)
      (compileSing body)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  have success : ∀ (captured nextCaptured : List Value),
      functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true →
      captureEnv selected env = some captured → captureEnv selected nextEnv = some nextCaptured →
      List.Forall₂ ValueRel captured nextCaptured →
      ∃ targetResult targetNext,
        evaluate [.letrec names location selected
          (compileFuns functions)
          (compileSing body)] nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
    intro captured nextCaptured arityOk capture nextCapture captures
    let recs := (List.range functions.length).map (fun i => Value.recclosure location [] captured functions i)
    let nextFunctions := compileFuns functions
    let nextRecs := (List.range nextFunctions.length).map
      (fun i => Value.recclosure location [] nextCaptured nextFunctions i)
    have recRel : List.Forall₂ ValueRel recs nextRecs :=
      recursiveClosures_related location captured nextCaptured functions captures
    have bodyRun : evaluate [body] (recs ++ env) source = (result, sourceNext) := by
      rw [evaluate.eq_def] at run
      simp only [arityOk, ↓reduceIte] at run
      cases selected with
      | none =>
        change some env = some captured at capture
        cases capture
        simpa [recs] using run
      | some indices =>
        change lookupVars indices env = some captured at capture
        simpa [capture, recs] using run
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH (fun captured => (List.range functions.length).map
          (fun i => Value.recclosure location [] captured functions i)) (some recs) recs
        arityOk rfl (by simp [capture, recs]) rfl result sourceNext [compileSing body]
        (nextRecs ++ nextEnv) target
        ⟨bodyRun, List.rel_append recRel envRel, states, by
          simp [CodeRel, compileList]⟩
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    rw [evaluate.eq_def]
    simp only [maxEq, compileFuns_all, arityOk, ↓reduceIte]
    cases selected with
    | none =>
      change some nextEnv = some nextCaptured at nextCapture
      cases nextCapture
      simpa [nextFunctions, nextRecs] using targetRun
    | some indices =>
      change lookupVars indices nextEnv = some nextCaptured at nextCapture
      simpa [nextCapture, nextFunctions, nextRecs] using targetRun
  cases selected with
  | none =>
    by_cases arityOk : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
    · exact success env nextEnv arityOk rfl rfl envRel
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target,
        by simp [evaluate, maxEq, compileFuns_all, arityOk], rfl, states⟩
  | some indices =>
    by_cases arityOk : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
    · have captureRel := environment_lookupVars indices env nextEnv envRel
      cases capture : lookupVars indices env with
      | none =>
        cases nextCapture : lookupVars indices nextEnv with
        | none =>
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.err (.abort .typeError), target,
            by simp [evaluate, maxEq, compileFuns_all, arityOk, nextCapture], rfl, states⟩
        | some values => simp [capture, nextCapture, Flapjack.optionRel] at captureRel
      | some values =>
        cases nextCapture : lookupVars indices nextEnv with
        | none => simp [capture, nextCapture, Flapjack.optionRel] at captureRel
        | some nextValues =>
          exact success values nextValues arityOk capture nextCapture
            (by simpa [capture, nextCapture, Flapjack.optionRel] using captureRel)
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target,
        by simp [evaluate, maxEq, compileFuns_all, arityOk], rfl, states⟩

end Flapjack.Compiler.Backend.ClosLetop
