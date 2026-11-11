module

public import Flapjack.Compiler.Backend.ClosTicks.Proofs.EvaluateFn

@[expose] public section

/-! Recursive-closure case of the tick-removal evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosTicks
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

instance evaluateLetrecInst1 : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- A recursive binding produced by tick removal came from one under ticks. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "remove_ticks_Letrec_IMP_mk_Ticks"]
theorem remove_ticks_Letrec_IMP_mk_Ticks (expression : ClosLang.Exp) (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp)
    (removed : [ClosLang.Exp.letrec names location selected functions body] = removeSource [expression]) :
    ∃ traces sourceFunctions sourceBody,
      expression = mkTicks traces (.letrec names location selected sourceFunctions sourceBody) ∧
      body = Flapjack.holHd (removeSource [sourceBody]) ∧
      functions = sourceFunctions.map (fun (arity, e) => (arity, Flapjack.holHd (removeSource [e]))) := by
  cases expression
  case tick outer inner =>
    have innerRemoved : [ClosLang.Exp.letrec names location selected functions body] = removeSource [inner] := by
      simpa [removeList, removeSing] using removed
    obtain ⟨traces, sourceFunctions, sourceBody, equal, bodyEqual, functionsEqual⟩ :=
      remove_ticks_Letrec_IMP_mk_Ticks inner names location selected functions body innerRemoved
    exact ⟨outer :: traces, sourceFunctions, sourceBody, by simp [mkTicks, equal], bodyEqual, functionsEqual⟩
  case letrec actualNames actualLocation actualSelected sourceFunctions sourceBody =>
    simp [removeList, removeSing] at removed
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := removed
    exact ⟨[], sourceFunctions, sourceBody, rfl, by simp [removeList, Flapjack.holHd], by
      simp [removeFuns_eq_map, removeList, Flapjack.holHd]⟩
  all_goals simp [removeList, removeSing] at removed
termination_by sizeOf expression

/-- Related recursive bodies preserve their arities. This is Flapjack
infrastructure for the recursive-closure case. -/
theorem removeFuns_related (functions : List (Nat × ClosLang.Exp)) :
    List.Forall₂ FunctionRel functions (removeFuns functions) := by
  induction functions with
  | nil => exact .nil
  | cons function rest ih =>
    rcases function with ⟨arity, body⟩
    exact .cons (by simp [FunctionRel, CodeRel, removeList]) ih

/-- Tick removal preserves all recursive arity tests. This is Flapjack
infrastructure for the recursive-closure case. -/
theorem removeFuns_all (maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) :
    (removeFuns functions).all (fun (arity, _) => arity ≤ maxApp && arity != 0) =
      functions.all (fun (arity, _) => arity ≤ maxApp && arity != 0) := by
  simp [removeFuns_eq_map, Function.comp_def]

/-- Related environments yield related recursive closures. This is Flapjack
infrastructure for the recursive-closure case. -/
theorem recursiveClosures_related (location : Option Nat) (source target : List Value)
    (functions : List (Nat × ClosLang.Exp)) (envRel : List.Forall₂ ValueRel source target) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] source functions i))
      ((List.range (removeFuns functions).length).map
        (fun i => Value.recclosure location [] target (removeFuns functions) i)) := by
  have length : (removeFuns functions).length = functions.length := by simp [removeFuns_eq_map]
  rw [length]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] source target functions _ index envRel .nil
      (removeFuns_related functions)) ih

/-- Capture all values or the requested indices. This is Flapjack
infrastructure for stating the original induction hypothesis. -/
def captureEnv (selected : Option (List Nat)) (env : List Value) : Option (List Value) :=
  match selected with | none => some env | some indices => lookupVars indices env

namespace LetrecPort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end LetrecPort

/-- The recursive-closure case of the reverse tick-removal simulation. -/
@[hol "cakeml/compiler/backend/proofs/clos_ticksProofScript.sml" "evaluate_remove_ticks"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_ticks_letrec {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat)) (functions : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (envTarget : List Value) (target : State C F)
    (bodyIH : ∀ (buildRc : List Value → List Value) (envdelta : Option (List Value)) (ed : List Value),
      functions.all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true →
      buildRc = (fun captured => (List.range functions.length).map
        (fun i => Value.recclosure location [] captured functions i)) →
      envdelta = (captureEnv selected envTarget).map buildRc → envdelta = some ed →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (envSource : List Value) (source : State C F) (code : List ClosLang.Exp),
        evaluate [body] (ed ++ envTarget) target = (result, next) ∧
          List.Forall₂ ValueRel envSource (ed ++ envTarget) ∧ StateRel source target ∧ CodeRel code [body] →
        ∃ extra sourceResult sourceNext,
          evaluate code envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
          ResultRel sourceResult result ∧ StateRel sourceNext next)
    (result : Result (List Value) Value) (targetNext : State C F)
    (envSource : List Value) (source : State C F) (sourceCode : List ClosLang.Exp)
    (premises : evaluate [.letrec names location selected functions body] envTarget target = (result, targetNext) ∧
      List.Forall₂ ValueRel envSource envTarget ∧ StateRel source target ∧
      CodeRel sourceCode [.letrec names location selected functions body]) :
    ∃ extra sourceResult sourceNext,
      evaluate sourceCode envSource { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
      ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have length := code_rel_IMP_LENGTH sourceCode [.letrec names location selected functions body] code
  have singleton : ∃ expression, sourceCode = [expression] := by
    cases sourceCode with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => exact ⟨first, rfl⟩
      | cons second rest => simp at length
  obtain ⟨expression, rfl⟩ := singleton
  obtain ⟨traces, sourceFunctions, sourceBody, rfl, bodyCode, functionsCode⟩ :=
    remove_ticks_Letrec_IMP_mk_Ticks expression names location selected functions body code
  simp only [removeSource_eq_list, removeList, Flapjack.holHd] at bodyCode functionsCode
  have functionsEq : functions = removeFuns sourceFunctions := by
    simpa [removeFuns_eq_map] using functionsCode
  clear functionsCode
  subst functions
  subst body
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  have wrapped (extra : Nat) : evaluate [mkTicks traces (.letrec names location selected sourceFunctions sourceBody)] envSource
      { source with clock := source.clock + (extra + traces.length) } =
      evaluate [.letrec names location selected sourceFunctions sourceBody] envSource { source with clock := source.clock + extra } := by
    rw [evaluate_mk_Ticks]
    have enough : ¬ source.clock + (extra + traces.length) < traces.length := by omega
    have clocks : source.clock + (extra + traces.length) - traces.length = source.clock + extra := by omega
    simp [decClock, enough, clocks]
  have success : ∀ (sourceCaptured targetCaptured : List Value),
      (removeFuns sourceFunctions).all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true →
      captureEnv selected envSource = some sourceCaptured → captureEnv selected envTarget = some targetCaptured →
      List.Forall₂ ValueRel sourceCaptured targetCaptured →
      ∃ extra sourceResult sourceNext,
        evaluate [mkTicks traces (.letrec names location selected sourceFunctions sourceBody)] envSource
          { source with clock := source.clock + extra } = (sourceResult, sourceNext) ∧
        ResultRel sourceResult result ∧ StateRel sourceNext targetNext := by
    intro sourceCaptured targetCaptured arityOk sourceCapture targetCapture captures
    have sourceArity : sourceFunctions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
      simpa [maxEq, removeFuns_all] using arityOk
    let targetRecs := (List.range (removeFuns sourceFunctions).length).map
      (fun i => Value.recclosure location [] targetCaptured (removeFuns sourceFunctions) i)
    let sourceRecs := (List.range sourceFunctions.length).map
      (fun i => Value.recclosure location [] sourceCaptured sourceFunctions i)
    have recRel : List.Forall₂ ValueRel sourceRecs targetRecs :=
      recursiveClosures_related location sourceCaptured targetCaptured sourceFunctions captures
    have bodyRun : evaluate [removeSing sourceBody] (targetRecs ++ envTarget) target = (result, targetNext) := by
      rw [evaluate.eq_def] at run
      simp only [arityOk, ↓reduceIte] at run
      cases selected with
      | none =>
        change some envTarget = some targetCaptured at targetCapture
        cases targetCapture
        simpa [targetRecs] using run
      | some indices =>
        change lookupVars indices envTarget = some targetCaptured at targetCapture
        simpa [targetCapture, targetRecs] using run
    obtain ⟨extra, sourceResult, sourceNext, sourceRun, resultRel, nextRel⟩ :=
      bodyIH (fun captured => (List.range (removeFuns sourceFunctions).length).map
          (fun i => Value.recclosure location [] captured (removeFuns sourceFunctions) i)) (some targetRecs) targetRecs
        arityOk rfl (by simp [targetCapture, targetRecs]) rfl result targetNext (sourceRecs ++ envSource)
        source [sourceBody] ⟨bodyRun, List.rel_append recRel envRel, states, by simp [CodeRel, removeList]⟩
    refine ⟨extra + traces.length, sourceResult, sourceNext, ?_, resultRel, nextRel⟩
    rw [wrapped, evaluate.eq_def]
    simp only [sourceArity, ↓reduceIte]
    cases selected with
    | none =>
      change some envSource = some sourceCaptured at sourceCapture
      cases sourceCapture
      simpa [sourceRecs] using sourceRun
    | some indices =>
      change lookupVars indices envSource = some sourceCaptured at sourceCapture
      simpa [sourceCapture, sourceRecs] using sourceRun
  cases selected with
  | none =>
    by_cases arityOk : (removeFuns sourceFunctions).all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true
    · exact success envSource envTarget arityOk rfl rfl envRel
    · have sourceBad : ¬ sourceFunctions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
        simpa [maxEq, removeFuns_all] using arityOk
      simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
      simpa using (show evaluate [mkTicks traces (.letrec names location none sourceFunctions sourceBody)] envSource
          { source with clock := source.clock + (0 + traces.length) } = (.err (.abort .typeError), source) by
        rw [wrapped]
        simp [evaluate, sourceBad])
  | some indices =>
    by_cases arityOk : (removeFuns sourceFunctions).all (fun (arity, _) => arity ≤ target.maxApp && arity != 0) = true
    · have captureRel := environment_lookupVars indices envSource envTarget envRel
      cases targetCapture : lookupVars indices envTarget with
      | none =>
        cases sourceCapture : lookupVars indices envSource with
        | none =>
          simp [evaluate, arityOk, targetCapture] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
          have sourceArity : sourceFunctions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
            simpa [maxEq, removeFuns_all] using arityOk
          simpa using (show evaluate [mkTicks traces (.letrec names location (some indices) sourceFunctions sourceBody)] envSource
              { source with clock := source.clock + (0 + traces.length) } = (.err (.abort .typeError), source) by
            rw [wrapped]
            simp [evaluate, sourceArity, sourceCapture])
        | some values => simp [targetCapture, sourceCapture, Flapjack.optionRel] at captureRel
      | some values =>
        cases sourceCapture : lookupVars indices envSource with
        | none => simp [targetCapture, sourceCapture, Flapjack.optionRel] at captureRel
        | some sourceValues =>
          exact success sourceValues values arityOk sourceCapture targetCapture
            (by simpa [targetCapture, sourceCapture, Flapjack.optionRel] using captureRel)
    · have sourceBad : ¬ sourceFunctions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true := by
        simpa [maxEq, removeFuns_all] using arityOk
      simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨traces.length, .err (.abort .typeError), source, ?_, rfl, states⟩
      simpa using (show evaluate [mkTicks traces (.letrec names location (some indices) sourceFunctions sourceBody)] envSource
          { source with clock := source.clock + (0 + traces.length) } = (.err (.abort .typeError), source) by
        rw [wrapped]
        simp [evaluate, sourceBad])

end Flapjack.Compiler.Backend.ClosTicks
