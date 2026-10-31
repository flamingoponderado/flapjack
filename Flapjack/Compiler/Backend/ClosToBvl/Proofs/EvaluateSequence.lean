import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluatePost
import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateLength

/-! Sequential composition for the closure-to-BVL simulation candidate. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps

/-- Compose a successful singleton simulation with the simulation of a
nonempty tail. The continuation is the tail induction hypothesis; it receives
the state and environment relations established by the head. This is
Flapjack-specific infrastructure until the evaluator and carrier review is
complete. -/
theorem evaluatePost_cons_success {C F : Type}
    (s sMiddle sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (sourceHead : ClosLang.Exp) (targetHead : Bvl.Exp)
    (sourceValue : ClosSem.Value) (tailResult : Result (List ClosSem.Value) ClosSem.Value)
    (targetTail : List Bvl.Exp) (tailNonempty : targetTail ≠ [])
    (headRun : ClosSem.evaluate [sourceHead] sourceEnv s = (.val [sourceValue], sMiddle))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (headPost : evaluatePost s sMiddle t targetEnv f (.val [sourceValue]) [targetHead])
    (tailIH : ∀ (tMiddle : BvlSem.State C F) (fMiddle : HolFiniteMapExact Nat Nat),
      stateRel fMiddle sMiddle tMiddle →
      envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv →
      codeAnnotations sMiddle →
      evaluatePost sMiddle sFinal tMiddle targetEnv fMiddle tailResult targetTail) :
    evaluatePost s sFinal t targetEnv f
      (match tailResult with | .val values => .val (sourceValue :: values) | .err error => .err error)
      (targetHead :: targetTail) := by
  have maxApp : sMiddle.maxApp = s.maxApp := by
    have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [sourceHead] sourceEnv s
    rw [headRun] at h
    exact h
  obtain ⟨clock1, result1, tMiddle, fMiddle, targetRun1, related1, state1, map1, refs1,
    annotations1, clocks1, code1, env1⟩ :=
      evaluatePost_environment s sMiddle t sourceEnv targetEnv f (.val [sourceValue]) [targetHead]
        envRelated headPost
  cases result1 with
  | err error => simp [resultRel] at related1
  | val values1 =>
    cases related1 with
    | @cons a targetValue sourceTail targetTailValues valueRel restRel =>
      cases restRel
      have envMiddle : envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv := by
        simpa [maxApp] using env1
      obtain ⟨clock2, result2, tFinal, fFinal, targetRun2, related2, state2, map2, refs2,
        annotations2, clocks2⟩ := tailIH tMiddle fMiddle state1 envMiddle annotations1
      have shifted := BvlProps.evaluate_addClock [targetHead] targetEnv
        { t with clock := s.clock + clock1 } tMiddle (.val [targetValue]) clock2 targetRun1 (by simp)
      have runHead : BvlSem.evaluate [targetHead] targetEnv
          { t with clock := s.clock + (clock1 + clock2) } =
          (.val [targetValue], { tMiddle with clock := sMiddle.clock + clock2 }) := by
        simpa [Nat.add_assoc, clocks1] using shifted
      have runTail : BvlSem.evaluate targetTail targetEnv
          { tMiddle with clock := sMiddle.clock + clock2 } = (result2, tFinal) := targetRun2
      have growth : sptSubspt tMiddle.code tFinal.code := by
        exact BvlProps.evaluateMono targetTail targetEnv
          { tMiddle with clock := sMiddle.clock + clock2 } result2 tFinal targetRun2
      have finalHead := vRel_grow valueRel map2 refs2 growth
      have targetSequence : BvlSem.evaluate (targetHead :: targetTail) targetEnv
          { t with clock := s.clock + (clock1 + clock2) } =
          (match result2 with | .val values => .val (targetValue :: values) | .err error => .err error, tFinal) := by
        cases targetTail with
        | nil => contradiction
        | cons targetSecond targetRest =>
          rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, runHead]
          cases result2 <;> (simp only at *; rw [runTail]; try rfl)
      refine ⟨clock1 + clock2, _, tFinal, fFinal, targetSequence, ?_, state2,
        relocationSubmap_trans map1 map2, unmappedRefsSubmap_trans refs1 refs2,
        annotations2, clocks2⟩
      cases tailResult with
      | err error =>
        cases result2 with
        | val values => simp [resultRel] at related2
        | err targetError => simpa [resultRel, maxApp] using related2
      | val values =>
        cases result2 with
        | err error => simp [resultRel] at related2
        | val targetValues =>
          simp only [resultRel] at related2 ⊢
          exact .cons finalHead (by simpa [maxApp] using related2)

/-- If the head raises or aborts, evaluating a nonempty list stops at that
head and retains its simulation postcondition. -/
theorem evaluatePost_cons_error {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (targetEnv : List BvlSem.Value) (f : HolFiniteMapExact Nat Nat)
    (targetHead : Bvl.Exp) (targetTail : List Bvl.Exp) (tailNonempty : targetTail ≠ [])
    (error : ErrorResult ClosSem.Value)
    (headPost : evaluatePost s sFinal t targetEnv f (.err error) [targetHead]) :
    evaluatePost s sFinal t targetEnv f (.err error) (targetHead :: targetTail) := by
  obtain ⟨clock, targetResult, tFinal, fFinal, run, related, states, map, refs,
    annotations, clocks⟩ := headPost
  cases targetResult with
  | val values => simp [resultRel] at related
  | err targetError =>
    refine ⟨clock, .err targetError, tFinal, fFinal, ?_, related, states, map, refs, annotations, clocks⟩
    cases targetTail with
    | nil => contradiction
    | cons second rest =>
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, run]

/-- The multi-expression evaluator case follows from the head and tail
simulation induction hypotheses. The hypotheses deliberately leave compiler
accumulator bookkeeping to the enclosing pass proof. -/
theorem evaluate_cons_post {C F : Type}
    (s sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (targetHead : Bvl.Exp) (targetTail : List Bvl.Exp) (tailNonempty : targetTail ≠ [])
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (run : ClosSem.evaluate (first :: second :: rest) sourceEnv s = (result, sFinal))
    (noTypeError : result ≠ .err (.abort .typeError))
    (envRelated : envRel s.maxApp f t.refs t.code sourceEnv targetEnv)
    (headIH : ∀ (headResult : Result (List ClosSem.Value) ClosSem.Value) (sMiddle : ClosSem.State C F),
      ClosSem.evaluate [first] sourceEnv s = (headResult, sMiddle) →
      headResult ≠ .err (.abort .typeError) →
      evaluatePost s sMiddle t targetEnv f headResult [targetHead])
    (tailIH : ∀ (sMiddle sLast : ClosSem.State C F) (tailResult : Result (List ClosSem.Value) ClosSem.Value)
      (tMiddle : BvlSem.State C F) (fMiddle : HolFiniteMapExact Nat Nat),
      ClosSem.evaluate (second :: rest) sourceEnv sMiddle = (tailResult, sLast) →
      tailResult ≠ .err (.abort .typeError) → stateRel fMiddle sMiddle tMiddle →
      envRel sMiddle.maxApp fMiddle tMiddle.refs tMiddle.code sourceEnv targetEnv →
      codeAnnotations sMiddle → evaluatePost sMiddle sLast tMiddle targetEnv fMiddle tailResult targetTail) :
    evaluatePost s sFinal t targetEnv f result (targetHead :: targetTail) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate] at run
  cases headRun : ClosSem.evaluate [first] sourceEnv s with
  | mk headResult sMiddle =>
    rw [headRun] at run
    cases headResult with
    | err error =>
      simp only at run
      cases run
      exact evaluatePost_cons_error s sFinal t targetEnv f targetHead targetTail tailNonempty error
        (headIH (.err error) sFinal headRun noTypeError)
    | val values =>
      obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value first sourceEnv s sMiddle values headRun
      cases tailRun : ClosSem.evaluate (second :: rest) sourceEnv sMiddle with
      | mk tailResult sLast =>
        simp only at run
        rw [tailRun] at run
        cases tailResult with
        | val tailValues =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          apply evaluatePost_cons_success s sMiddle sLast t sourceEnv targetEnv f first targetHead
            value (.val tailValues) targetTail tailNonempty headRun envRelated (headIH _ _ headRun (by simp))
          intro tMiddle fMiddle state env annotations
          exact tailIH sMiddle sLast (.val tailValues) tMiddle fMiddle tailRun (by simp) state env annotations
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          apply evaluatePost_cons_success s sMiddle sLast t sourceEnv targetEnv f first targetHead
            value (.err error) targetTail tailNonempty headRun envRelated (headIH _ _ headRun (by simp))
          intro tMiddle fMiddle state env annotations
          exact tailIH sMiddle sLast (.err error) tMiddle fMiddle tailRun noTypeError state env annotations

end Flapjack.Compiler.Backend.ClosToBvl
