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
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code →
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
        annotations2, clocks2⟩ := tailIH tMiddle fMiddle state1 envMiddle annotations1 code1
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
      codeAnnotations sMiddle → sptSubspt t.code tMiddle.code → sMiddle.maxApp = s.maxApp →
      evaluatePost sMiddle sLast tMiddle targetEnv fMiddle tailResult targetTail) :
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
          intro tMiddle fMiddle state env annotations growth
          have maxApp : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [first] sourceEnv s
            rw [headRun] at h
            exact h
          exact tailIH sMiddle sLast (.val tailValues) tMiddle fMiddle tailRun (by simp) state env annotations growth maxApp
        | err error =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          apply evaluatePost_cons_success s sMiddle sLast t sourceEnv targetEnv f first targetHead
            value (.err error) targetTail tailNonempty headRun envRelated (headIH _ _ headRun (by simp))
          intro tMiddle fMiddle state env annotations growth
          have maxApp : sMiddle.maxApp = s.maxApp := by
            have h := (ClosProps.evaluate_const (C := C) (F := F)).1 [first] sourceEnv s
            rw [headRun] at h
            exact h
          exact tailIH sMiddle sLast (.err error) tMiddle fMiddle tailRun noTypeError state env annotations growth maxApp

/-- The expression-side simulation statement for a fixed source expression
list. It records the hypotheses of the source theorem while the underlying
semantic carriers await correspondence review. -/
def expressionSimulation {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (s sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (aux finalAux : List (Nat × Nat × Bvl.Exp))
    (compiled : List Bvl.Exp) (result : Result (List ClosSem.Value) ClosSem.Value),
    ClosSem.evaluate expressions sourceEnv s = (result, sFinal) →
    result ≠ .err (.abort .typeError) →
    compileExpsHOL s.maxApp expressions aux = (compiled, finalAux) →
    ClosProps.everyFnLocationSome expressions → codeAnnotations s →
    ClosProps.everyFnVarsSome expressions → codeInstalled finalAux t.code →
    envRel s.maxApp f t.refs t.code sourceEnv targetEnv → stateRel f s t →
    evaluatePost s sFinal t targetEnv f result compiled

/-- Expression simulation restricted to source states below a clock bound.
This Flapjack induction interface is untagged while the source and target
semantic carriers await correspondence review. -/
def expressionSimulationBelow {C F : Type} (clockBound : Nat) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (s sFinal : ClosSem.State C F) (t : BvlSem.State C F)
    (sourceEnv : List ClosSem.Value) (targetEnv : List BvlSem.Value)
    (f : HolFiniteMapExact Nat Nat) (aux finalAux : List (Nat × Nat × Bvl.Exp))
    (compiled : List Bvl.Exp) (result : Result (List ClosSem.Value) ClosSem.Value),
    s.clock < clockBound → ClosSem.evaluate expressions sourceEnv s = (result, sFinal) →
    result ≠ .err (.abort .typeError) →
    compileExpsHOL s.maxApp expressions aux = (compiled, finalAux) →
    ClosProps.everyFnLocationSome expressions → codeAnnotations s →
    ClosProps.everyFnVarsSome expressions → codeInstalled finalAux t.code →
    envRel s.maxApp f t.refs t.code sourceEnv targetEnv → stateRel f s t →
    evaluatePost s sFinal t targetEnv f result compiled

/-- A simulation valid without a clock restriction is valid below any bound. -/
theorem expressionSimulation_below {C F : Type} (clockBound : Nat) (expressions : List ClosLang.Exp)
    (simulation : expressionSimulation (C := C) (F := F) expressions) :
    expressionSimulationBelow (C := C) (F := F) clockBound expressions := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result _
  exact simulation s sFinal t sourceEnv targetEnv f aux finalAux compiled result

/-- A simulation below a bound remains available below a smaller bound. -/
theorem expressionSimulationBelow_mono {C F : Type} (small large : Nat) (expressions : List ClosLang.Exp)
    (bound : small ≤ large) (simulation : expressionSimulationBelow (C := C) (F := F) large expressions) :
    expressionSimulationBelow (C := C) (F := F) small expressions := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result clock
  exact simulation s sFinal t sourceEnv targetEnv f aux finalAux compiled result (by omega)

/-- Proving the simulation at every finite clock bound suffices for the
unrestricted expression simulation. -/
theorem expressionSimulation_iff_below {C F : Type} (expressions : List ClosLang.Exp) :
    expressionSimulation (C := C) (F := F) expressions ↔
      ∀ clockBound, expressionSimulationBelow (C := C) (F := F) clockBound expressions := by
  constructor
  · intro simulation clockBound
    exact expressionSimulation_below clockBound expressions simulation
  · intro simulation s sFinal t sourceEnv targetEnv f aux finalAux compiled result
    exact simulation (s.clock + 1) s sFinal t sourceEnv targetEnv f aux finalAux compiled result (by omega)

/-- The nonempty list case of the expression simulation, including the
original compiler accumulator and code-installation premises. The two
hypotheses are the source evaluator's head and tail induction hypotheses.
This candidate remains untagged until semantic carrier correspondence is
reviewed and the remaining cases are assembled. -/
theorem expressionSimulation_cons {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp)
    (headIH : expressionSimulation (C := C) (F := F) [first])
    (tailIH : expressionSimulation (C := C) (F := F) (second :: rest)) :
    expressionSimulation (C := C) (F := F) (first :: second :: rest) := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  cases headCompile : compileExpHOL s.maxApp first aux with
  | mk targetHead auxMiddle =>
    have headCompiled : compileExpsHOL s.maxApp [first] aux = ([targetHead], auxMiddle) := by
      rw [compileExps_eq_list]
      simp [compileExpListHOL, headCompile]
    cases tailCompile : compileExpsHOL s.maxApp (second :: rest) auxMiddle with
    | mk targetTail auxLast =>
      have compiledEq : compileExpsHOL s.maxApp (first :: second :: rest) aux =
          (targetHead :: targetTail, auxLast) := by
        simp [compileExpsHOL, compileExpsSingleton_eq, headCompile, tailCompile]
      have equal := compile.symm.trans compiledEq
      cases equal
      have tailNonempty : targetTail ≠ [] := by
        have length := compileExps_length s.maxApp (second :: rest) auxMiddle targetTail finalAux tailCompile
        intro empty
        simp [empty] at length
      have headInstalled : codeInstalled auxMiddle t.code :=
        compileExps_codeInstalled s.maxApp (second :: rest) auxMiddle finalAux targetTail t.code tailCompile installed
      simp only [ClosProps.everyFnLocationSome] at locations
      simp only [ClosProps.everyFnVarsSome] at varsAnnotated
      have headLocations : ClosProps.everyFnLocationSome [first] := by
        simpa [ClosProps.everyFnLocationSome] using locations.1
      have tailLocations : ClosProps.everyFnLocationSome (second :: rest) := by
        simpa [ClosProps.everyFnLocationSome] using locations.2
      have headVars : ClosProps.everyFnVarsSome [first] := by
        simpa [ClosProps.everyFnVarsSome] using varsAnnotated.1
      have tailVars : ClosProps.everyFnVarsSome (second :: rest) := by
        simpa [ClosProps.everyFnVarsSome] using varsAnnotated.2
      apply evaluate_cons_post s sFinal t sourceEnv targetEnv f first second rest targetHead targetTail
        tailNonempty result run noTypeError envRelated
      · intro headResult sMiddle headRun headNotType
        exact headIH s sMiddle t sourceEnv targetEnv f aux auxMiddle [targetHead] headResult headRun
          headNotType headCompiled headLocations annotations headVars headInstalled envRelated states
      · intro sMiddle sLast tailResult tMiddle fMiddle tailRun tailNotType middleStates middleEnv middleAnnotations growth maxApp
        have tailCompiled : compileExpsHOL sMiddle.maxApp (second :: rest) auxMiddle = (targetTail, finalAux) := by
          simpa [maxApp] using tailCompile
        exact tailIH sMiddle sLast tMiddle sourceEnv targetEnv fMiddle auxMiddle finalAux targetTail tailResult
          tailRun tailNotType tailCompiled tailLocations middleAnnotations tailVars
          (codeInstalled_subspt installed growth) middleEnv middleStates

/-- The empty expression list satisfies the source-shaped simulation. -/
theorem expressionSimulation_nil {C F : Type} : expressionSimulation (C := C) (F := F) [] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  exact evaluate_nil f s sFinal t sourceEnv targetEnv aux finalAux compiled result run noTypeError
    compile locations annotations varsAnnotated installed envRelated states

/-- A variable satisfies the source-shaped simulation. -/
theorem expressionSimulation_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat) :
    expressionSimulation (C := C) (F := F) [.var trace index] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  exact evaluate_var_post f s sFinal t sourceEnv targetEnv trace index aux finalAux compiled result run
    noTypeError compile locations annotations varsAnnotated installed envRelated states

/-- Once each singleton case is established, the list case follows for all
expression lists, with no additional semantic or installation assumptions. -/
theorem expressionSimulation_lists {C F : Type}
    (singleton : ∀ expression : ClosLang.Exp, expressionSimulation (C := C) (F := F) [expression]) :
    ∀ expressions, expressionSimulation (C := C) (F := F) expressions := by
  intro expressions
  induction expressions with
  | nil => exact expressionSimulation_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact singleton first
    | cons second tail => exact expressionSimulation_cons first second tail (singleton first) ih

end Flapjack.Compiler.Backend.ClosToBvl
