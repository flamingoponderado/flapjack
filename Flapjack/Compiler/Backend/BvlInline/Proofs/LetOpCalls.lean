module

public import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpCases
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.SequenceCorrect
public import Flapjack.Compiler.Backend.BvlHandle.Proofs.GeneratedShape
public import Flapjack.Misc.ClockWeightInduction

@[expose] public section


/-! Call and force cases for the combined let-operation and handler pass. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- The handler phase preserves a type-safe run of the let-operation body
at the arity used by code lookup. -/
theorem evaluate_letOpTransform {C F : Type} (splitSeq : Bool) (limit : Nat)
    (body : Bvl.Exp) (env : List Value) (state final : State C F)
    (result : Result (List Value) Value)
    (run : evaluate [letOpSing body] env state = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    evaluate [letOpTransform splitSeq limit env.length body] env state = (result, final) := by
  simpa [letOpTransform, evaluateTuple] using
    BvlHandle.Proofs.compileAny_correct (letOpSing body) env state result final
      env.length splitSeq limit ⟨run, notType, rfl⟩

/-- Setting both clocks to zero preserves a mapped state relation. -/
theorem mappedStateRel_zeroClock {C F : Type} (transform : Nat → Bvl.Exp → Bvl.Exp)
    (source target : State C F) (related : mappedStateRel transform source target) :
    mappedStateRel transform { source with clock := 0 } { target with clock := 0 } := by
  obtain ⟨fields, compiler⟩ := related
  constructor
  · cases source
    cases target
    simp_all
  · simpa using compiler

/-- Calls use the mapped code lookup and the handler preservation theorem
after applying the recursive let-operation simulation to the callee. -/
theorem letOpSimulation_call {C F : Type} (splitSeq : Bool) (limit ticks : Nat)
    (dest : Option Nat) (args : List Bvl.Exp) (env : List Value) (source : State C F)
    (argsIH : letOpSimulation splitSeq limit args env source)
    (bodyIH : ∀ (body : Bvl.Exp) (values : List Value) (next : State C F),
      next.clock < source.clock → letOpSimulation splitSeq limit [body] values next) :
    letOpSimulation splitSeq limit [.call ticks dest args] env source := by
  intro result final target related run notType
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    rw [argsRun] at run
    have clockBound : middle.clock ≤ source.clock := by
      have h := evaluate_clock_le args env source
      simpa [argsRun] using h
    have argsSafe : argsResult ≠ .err (.abort .typeError) := by
      cases argsResult with
      | val values => simp
      | err error =>
        simp at run
        rcases run with ⟨rfl, _⟩
        exact notType
    obtain ⟨targetMiddle, targetArgs, middleRel⟩ :=
      argsIH argsResult middle target related argsRun argsSafe
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetMiddle, ?_, middleRel⟩
      simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
      rw [evaluate, fixClock_evaluate, targetArgs]
    | val values =>
      have foundRel := mappedStateRel_findCode (letOpTransform splitSeq limit)
        middle targetMiddle middleRel dest values
      cases found : findCode dest values middle.code with
      | none =>
        simp [found] at run
        exact False.elim (notType run.1.symm)
      | some pair =>
        obtain ⟨callValues, body⟩ := pair
        have targetFound : findCode dest values targetMiddle.code =
            some (callValues, letOpTransform splitSeq limit callValues.length body) := by
          simpa [found] using foundRel
        have clocks : targetMiddle.clock = middle.clock := by
          simpa using congrArg (fun s : State C F => s.clock) middleRel.1
        by_cases timeout : middle.clock < ticks + 1
        · have targetTimeout : targetMiddle.clock < ticks + 1 := by simpa [clocks] using timeout
          simp [found, timeout] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨{ targetMiddle with clock := 0 }, ?_, mappedStateRel_zeroClock _ middle targetMiddle middleRel⟩
          simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
          rw [evaluate, fixClock_evaluate, targetArgs]
          simp [targetFound, targetTimeout]
        · have targetEnough : ¬targetMiddle.clock < ticks + 1 := by simpa [clocks] using timeout
          have nextSmaller : (decClock (ticks + 1) middle).clock < source.clock := by
            simp only [decClock]
            omega
          simp [found, timeout] at run
          obtain ⟨targetFinal, targetBody, finalRel⟩ :=
            bodyIH body callValues (decClock (ticks + 1) middle) nextSmaller
              result final (decClock (ticks + 1) targetMiddle)
              (mappedStateRel_decClock _ middle targetMiddle middleRel (ticks + 1)) run notType
          have transformedRun : evaluate [letOpTransform splitSeq limit callValues.length body]
              callValues (decClock (ticks + 1) targetMiddle) = (result, targetFinal) := by
            apply evaluate_letOpTransform splitSeq limit body callValues _ _ result ?_ notType
            simpa [letOp, letOpList, letOpSing] using targetBody
          refine ⟨targetFinal, ?_, finalRel⟩
          simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
          rw [evaluate, fixClock_evaluate, targetArgs]
          simpa [targetFound, targetEnough] using transformedRun

/-- Forcing an unevaluated thunk resolves and runs the mapped body, while
already evaluated thunks and timeouts retain their original behavior. -/
theorem letOpSimulation_force {C F : Type} (splitSeq : Bool) (limit location index : Nat)
    (env : List Value) (source : State C F)
    (bodyIH : ∀ (body : Bvl.Exp) (values : List Value) (next : State C F),
      next.clock < source.clock → letOpSimulation splitSeq limit [body] values next) :
    letOpSimulation splitSeq limit [.force location index] env source := by
  intro result final target related run notType
  have refs : target.refs = source.refs := by
    simpa using congrArg (fun s : State C F => s.refs) related.1
  have clocks : target.clock = source.clock := by
    simpa using congrArg (fun s : State C F => s.clock) related.1
  cases valueAt : env[index]? with
  | none =>
    simp [evaluate, valueAt] at run
    exact False.elim (notType run.1.symm)
  | some thunk =>
    cases thunkAt : destThunk thunk source.refs with
    | badRef =>
      simp [evaluate, valueAt, thunkAt] at run
      exact False.elim (notType run.1.symm)
    | notThunk =>
      simp [evaluate, valueAt, thunkAt] at run
      exact False.elim (notType run.1.symm)
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [evaluate, valueAt, thunkAt] at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨target, by simp [letOp, letOpList, letOpOne, evaluate, valueAt, refs, thunkAt], related⟩
      | notEvaluated =>
        have foundRel := mappedStateRel_findCode (letOpTransform splitSeq limit)
          source target related (some location) [thunk, value]
        cases found : findCode (some location) [thunk, value] source.code with
        | none =>
          simp [evaluate, valueAt, thunkAt, found] at run
          exact False.elim (notType run.1.symm)
        | some pair =>
          obtain ⟨values, body⟩ := pair
          have targetFound : findCode (some location) [thunk, value] target.code =
              some (values, letOpTransform splitSeq limit values.length body) := by
            simpa [found] using foundRel
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := clocks.trans zero
            simp [evaluate, valueAt, thunkAt, found, zero] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ target with clock := 0 }, ?_, mappedStateRel_zeroClock _ source target related⟩
            simp [letOp, letOpList, letOpOne, evaluate, valueAt, refs, thunkAt, targetFound, targetZero]
          · have targetNonzero : target.clock ≠ 0 := by simpa [clocks] using zero
            have nextSmaller : (decClock 1 source).clock < source.clock := by
              simp only [decClock]
              omega
            simp [evaluate, valueAt, thunkAt, found, zero] at run
            obtain ⟨targetFinal, targetBody, finalRel⟩ :=
              bodyIH body values (decClock 1 source) nextSmaller result final (decClock 1 target)
                (mappedStateRel_decClock _ source target related 1) run notType
            have transformedRun : evaluate [letOpTransform splitSeq limit values.length body]
                values (decClock 1 target) = (result, targetFinal) := by
              apply evaluate_letOpTransform splitSeq limit body values _ _ result ?_ notType
              simpa [letOp, letOpList, letOpSing] using targetBody
            refine ⟨targetFinal, ?_, finalRel⟩
            simpa [letOp, letOpList, letOpOne, evaluate, valueAt, refs, thunkAt, targetFound, targetNonzero]
              using transformedRun

/-- Full let-operation simulation with mapped code and compiler callbacks.
This assembles the structural cases and decreases the clock when entering
called or forced code. It remains untagged pending evaluator and state-relation
review against HOL. -/
theorem letOpSimulation_all {C F : Type} (splitSeq : Bool) (limit : Nat)
    (expressions : List Bvl.Exp) (env : List Value) (source : State C F) :
    letOpSimulation splitSeq limit expressions env source := by
  refine clockWeightInduction (α := List Bvl.Exp) (σ := State C F) (·.clock) expsWeight
    (motive := fun es s => ∀ environment, letOpSimulation splitSeq limit es environment s) ?_
    expressions source env
  intro es s exprIH₀ smaller₀
  have exprIH := fun (es' : List Bvl.Exp) (environment' : List Value) (s' : State C F)
      h1 h2 => exprIH₀ es' s' h1 h2 environment'
  have smaller := fun (es' : List Bvl.Exp) (environment' : List Value) (s' : State C F)
      h => smaller₀ es' s' h environment'
  intro environment
  cases es with
  | nil => exact letOpSimulation_nil splitSeq limit environment s
  | cons first rest =>
    cases rest with
    | cons second tail =>
      apply letOpSimulation_cons splitSeq limit first second tail environment s ?_ ?_
      · apply exprIH [first] environment s (by omega) ?_
        simp only [expsWeight] at ⊢
        have := expWeight_pos second
        omega
      · intro next bound
        apply exprIH (second :: tail) environment next (by omega) ?_
        simp only [expsWeight] at ⊢
        have := expWeight_pos first
        omega
    | nil =>
      cases first with
      | var index => exact letOpSimulation_var splitSeq limit index environment s
      | force location index =>
        apply letOpSimulation_force splitSeq limit location index environment s
        intro body values next smaller
        exact smaller₀ [body] next (by omega) values
      | tick body =>
        apply letOpSimulation_tick splitSeq limit body environment s
        intro next smaller
        exact smaller₀ [body] next (by omega) environment
      | raise body =>
        apply letOpSimulation_raise splitSeq limit body environment s
        apply exprIH [body] environment s (by omega) ?_
        simp only [expsWeight, expWeight] at ⊢
        omega
      | op op args =>
        apply letOpSimulation_op splitSeq limit op args environment s
        apply exprIH args environment s (by omega) ?_
        simp only [expsWeight, expWeight] at ⊢
        omega
      | call ticks dest args =>
        apply letOpSimulation_call splitSeq limit ticks dest args environment s ?_ ?_
        · apply exprIH args environment s (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro body values next smaller
          exact smaller₀ [body] next (by omega) values
      | «let» bindings body =>
        apply letOpSimulation_let splitSeq limit bindings body environment s ?_ ?_
        · apply exprIH bindings environment s (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro bodyEnv next bound
          apply exprIH [body] bodyEnv next (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
      | handle body handler =>
        apply letOpSimulation_handle splitSeq limit body handler environment s ?_ ?_
        · apply exprIH [body] environment s (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro handlerEnv next bound
          apply exprIH [handler] handlerEnv next (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
      | ifThenElse condition yes no =>
        apply letOpSimulation_if splitSeq limit condition yes no environment s ?_ ?_
        · apply exprIH [condition] environment s (by omega) ?_
          simp only [expsWeight, expWeight] at ⊢
          omega
        · intro choice next bound
          cases choice with
          | false =>
            apply exprIH [no] environment next (by omega) ?_
            simp only [expsWeight, expWeight] at ⊢
            omega
          | true =>
            apply exprIH [yes] environment next (by omega) ?_
            simp only [expsWeight, expWeight] at ⊢
            omega

namespace LetEvaluationCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end LetEvaluationCarrier

/-- Let optimization simulates every source evaluation that is not a type error. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs])]
theorem evaluateLetOp {C F : Type} (expressions : List Bvl.Exp) (env : List Value)
    (source : Flapjack.Compiler.Backend.BvlSem.State C F) (result : Result (List Value) Value)
    (target sourceFinal : Flapjack.Compiler.Backend.BvlSem.State C F) (splitSeq : Bool) (limit : Nat)
    (premises : letStateRel splitSeq limit source target ∧
      evaluateTuple (expressions, env, source) = (result, sourceFinal) ∧
      result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple (letOp expressions, env, target) = (result, targetFinal) ∧
      letStateRel splitSeq limit sourceFinal targetFinal := by
  obtain ⟨related, run, safe⟩ := premises
  exact letOpSimulation_all splitSeq limit expressions env source result sourceFinal target
    related run safe

end Flapjack.Compiler.Backend.BvlInline.Proofs
