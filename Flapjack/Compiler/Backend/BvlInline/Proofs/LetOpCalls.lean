import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpCases
import Flapjack.Compiler.Backend.BvlHandle.Proofs.SequenceCorrect
import Flapjack.Compiler.Backend.BvlHandle.Proofs.GeneratedShape

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
  obtain ⟨output, compiled, evaluation⟩ := BvlHandle.Proofs.evaluate_compileAnyFuel
    0 splitSeq limit (letOpSing body) env state final result run notType
  have source := BvlHandle.compileAnyFuel_eq_source 0 splitSeq limit env.length (letOpSing body)
  rw [compiled] at source
  have same : output = letOpTransform splitSeq limit env.length body := by
    simpa [letOpTransform] using source
  simpa [same] using evaluation

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
  have allRanks : ∀ clock weight : Nat, ∀ (es : List Bvl.Exp) (environment : List Value) (s : State C F),
      s.clock = clock → expsWeight es = weight → letOpSimulation splitSeq limit es environment s := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (es : List Bvl.Exp) (environment : List Value) (s : State C F),
            s.clock ≤ clock → expsWeight es < weight → letOpSimulation splitSeq limit es environment s := by
          intro es environment s clockLe weightLt
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH s.clock clockLt (expsWeight es) es environment s rfl rfl
          · exact weightIH (expsWeight es) weightLt es environment s clockEq rfl
        intro es environment s stateClock measure
        cases es with
        | nil => exact letOpSimulation_nil splitSeq limit environment s
        | cons first rest =>
          cases rest with
          | cons second tail =>
            apply letOpSimulation_cons splitSeq limit first second tail environment s ?_ ?_
            · apply exprIH [first] environment s (by omega) ?_
              simp only [expsWeight] at measure ⊢
              have := expWeight_pos second
              omega
            · intro next bound
              apply exprIH (second :: tail) environment next (by omega) ?_
              simp only [expsWeight] at measure ⊢
              have := expWeight_pos first
              omega
          | nil =>
            cases first with
            | var index => exact letOpSimulation_var splitSeq limit index environment s
            | force location index =>
              apply letOpSimulation_force splitSeq limit location index environment s
              intro body values next smaller
              exact clockIH next.clock (by omega) (expsWeight [body]) [body] values next rfl rfl
            | tick body =>
              apply letOpSimulation_tick splitSeq limit body environment s
              intro next smaller
              exact clockIH next.clock (by omega) (expsWeight [body]) [body] environment next rfl rfl
            | raise body =>
              apply letOpSimulation_raise splitSeq limit body environment s
              apply exprIH [body] environment s (by omega) ?_
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | op op args =>
              apply letOpSimulation_op splitSeq limit op args environment s
              apply exprIH args environment s (by omega) ?_
              simp only [expsWeight, expWeight] at measure ⊢
              omega
            | call ticks dest args =>
              apply letOpSimulation_call splitSeq limit ticks dest args environment s ?_ ?_
              · apply exprIH args environment s (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro body values next smaller
                exact clockIH next.clock (by omega) (expsWeight [body]) [body] values next rfl rfl
            | «let» bindings body =>
              apply letOpSimulation_let splitSeq limit bindings body environment s ?_ ?_
              · apply exprIH bindings environment s (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro bodyEnv next bound
                apply exprIH [body] bodyEnv next (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | handle body handler =>
              apply letOpSimulation_handle splitSeq limit body handler environment s ?_ ?_
              · apply exprIH [body] environment s (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro handlerEnv next bound
                apply exprIH [handler] handlerEnv next (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
            | ifThenElse condition yes no =>
              apply letOpSimulation_if splitSeq limit condition yes no environment s ?_ ?_
              · apply exprIH [condition] environment s (by omega) ?_
                simp only [expsWeight, expWeight] at measure ⊢
                omega
              · intro choice next bound
                cases choice with
                | false =>
                  apply exprIH [no] environment next (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
                | true =>
                  apply exprIH [yes] environment next (by omega) ?_
                  simp only [expsWeight, expWeight] at measure ⊢
                  omega
  exact allRanks source.clock (expsWeight expressions) expressions env source rfl rfl

/-- The combined transformation preserves a non-type-error singleton run
between mapped states, including calls and dynamic code installation. -/
theorem evaluate_letOpTransform_mapped {C F : Type} (splitSeq : Bool) (limit : Nat)
    (body : Bvl.Exp) (env : List Value) (source target final : State C F)
    (result : Result (List Value) Value)
    (related : mappedStateRel (letOpTransform splitSeq limit) source target)
    (run : evaluate [body] env source = (result, final))
    (notType : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluate [letOpTransform splitSeq limit env.length body] env target = (result, targetFinal) ∧
      mappedStateRel (letOpTransform splitSeq limit) final targetFinal := by
  obtain ⟨targetFinal, transformed, finalRel⟩ :=
    letOpSimulation_all splitSeq limit [body] env source result final target related run notType
  have optimized : evaluate [letOpSing body] env target = (result, targetFinal) := by
    simpa [letOp, letOpList, letOpSing] using transformed
  exact ⟨targetFinal, evaluate_letOpTransform splitSeq limit body env target targetFinal result optimized notType, finalRel⟩

/-- Every combined-pass code body satisfies the variable bound and handler
shape required by BVL-to-BVI. -/
theorem letOpTransform_wellFormed (splitSeq : Bool) (limit arity : Nat) (body : Bvl.Exp) :
    BvlProps.bVarBound arity [letOpTransform splitSeq limit arity body] ∧
      BvlHandle.Proofs.handleOk [letOpTransform splitSeq limit arity body] := by
  obtain ⟨bounded, boundRun, bound⟩ :=
    BvlHandle.Proofs.compileAnyFuel_varBound 0 splitSeq limit arity (letOpSing body)
  obtain ⟨shaped, shapeRun, shape⟩ :=
    BvlHandle.Proofs.compileAnyFuel_handleOk 0 splitSeq limit arity (letOpSing body)
  have actual := BvlHandle.compileAnyFuel_eq_source 0 splitSeq limit arity (letOpSing body)
  have boundEq : bounded = letOpTransform splitSeq limit arity body := by
    rw [boundRun] at actual
    simpa [letOpTransform] using actual
  have shapeEq : shaped = letOpTransform splitSeq limit arity body := by
    have actual := BvlHandle.compileAnyFuel_eq_source 0 splitSeq limit arity (letOpSing body)
    rw [shapeRun] at actual
    simpa [letOpTransform] using actual
  simpa [boundEq, shapeEq] using And.intro bound shape

end Flapjack.Compiler.Backend.BvlInline.Proofs
