import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateCases
import Flapjack.Compiler.Backend.ClosMti.Proofs.PrimitiveNumeric

/-! Ordinary primitive-operation cases of the closure introduction simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Introduction preserves an operation and transforms its arguments. -/
theorem introExp_eq_op (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (targetArgs : List ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .op trace op targetArgs) :
    ∃ args, expression = .op trace op args ∧ ClosProps.noMtiList args ∧
      targetArgs = introList maxApp args := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Ordinary operations preserve a clock-bounded simulation when their
primitive dispatcher satisfies the separately proved simulation. -/
theorem evaluateRel_ordinaryWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (targetArgs sourceCode : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetArgs)
    (primitive : @PrimitiveSimulation C F op) :
    @EvaluateRelWithin C F limit sourceCode [.op trace op targetArgs] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .op trace op targetArgs := by
        simpa [introList] using code.2.symm
      obtain ⟨args, rfl, argsUnary, argsEq⟩ :=
        introExp_eq_op source.maxApp expression trace op targetArgs unary transformed
      have argsCode : CodeRel source.maxApp args targetArgs :=
        ⟨ClosProps.noMtiList_iff args |>.mp argsUnary, argsEq⟩
      cases targetArgsRun : evaluate targetArgs targetEnv target with
      | mk argsResult targetMiddle =>
        obtain ⟨sourceArgsResult, sourceMiddle, sourceArgsRun, argsRel, middleStates⟩ :=
          argsIH args targetEnv target sourceEnv targetMiddle source argsResult clock targetArgsRun env states argsCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 args sourceEnv source
          simpa [sourceArgsRun] using preserved
        cases argsResult with
        | err targetError =>
          cases sourceArgsResult with
          | val values => simp [resultRel] at argsRel
          | err sourceError =>
            rw [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce,
              targetArgsRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceMiddle,
              by rw [evaluate_ordinaryOp_eq trace op args sourceEnv source notInstall notForce, sourceArgsRun],
              argsRel, middleStates⟩
        | val targetValues =>
          cases sourceArgsResult with
          | err error => simp [resultRel] at argsRel
          | val sourceValues =>
            have valuesRel : List.Forall₂ (ValueRel sourceMiddle.maxApp)
                sourceValues.reverse targetValues.reverse := by
              have values : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceValues targetValues := by
                simpa [resultRel, maxEq] using argsRel
              exact List.rel_reverse values
            have step := primitive sourceMiddle targetMiddle sourceValues.reverse targetValues.reverse
              middleStates valuesRel
            cases targetApp : doApp op targetValues.reverse targetMiddle with
            | err targetError =>
              simp only [targetApp] at step
              obtain ⟨sourceError, sourceApp, errors⟩ := step
              rw [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce,
                targetArgsRun] at run
              dsimp only at run
              rw [targetApp] at run
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.err sourceError, sourceMiddle, ?_, ?_, middleStates⟩
              · rw [evaluate_ordinaryOp_eq trace op args sourceEnv source notInstall notForce, sourceArgsRun]
                dsimp only
                rw [sourceApp]
              · simpa [resultRel, maxEq] using errors
            | val pair =>
              obtain ⟨targetValue, targetLast⟩ := pair
              simp only [targetApp] at step
              obtain ⟨sourceValue, sourceLast, valueRel, finalStates, sourceApp⟩ := step
              rw [evaluate_ordinaryOp_eq trace op targetArgs targetEnv target notInstall notForce,
                targetArgsRun] at run
              dsimp only at run
              rw [targetApp] at run
              simp only [Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.val [sourceValue], sourceLast, ?_, ?_, finalStates⟩
              · rw [evaluate_ordinaryOp_eq trace op args sourceEnv source notInstall notForce, sourceArgsRun]
                dsimp only
                rw [sourceApp]
              · have valueRel' : ValueRel source.maxApp sourceValue targetValue := by
                  simpa [maxEq] using valueRel
                simpa [resultRel] using List.Forall₂.cons valueRel' List.Forall₂.nil

/-- The unrestricted ordinary-operation case, retained for existing callers. -/
theorem evaluateRel_ordinary {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (targetArgs sourceCode : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs)
    (primitive : @PrimitiveSimulation C F op) :
    @EvaluateRelAt C F sourceCode [.op trace op targetArgs] := by
  intro targetEnv target sourceEnv targetFinal source targetResult
  exact evaluateRel_ordinaryWithin source.clock trace op targetArgs sourceCode notInstall notForce
    (fun code => evaluateRelAt_within source.clock code _ (argsIH code)) primitive
    targetEnv target sourceEnv targetFinal source targetResult (by omega)

/-- Integer expressions satisfy the backward evaluation simulation given the
argument induction hypothesis. -/
theorem evaluateRel_int {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.IntOp)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs) :
    @EvaluateRelAt C F sourceCode [.op trace (.intOp op) targetArgs] :=
  evaluateRel_ordinary trace (.intOp op) targetArgs sourceCode (by simp) (by simp)
    argsIH (primitiveSimulation_int op)

/-- Word expressions satisfy the backward evaluation simulation given the
argument induction hypothesis, using the existing floating-point model. -/
theorem evaluateRel_word {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.WordOp)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs) :
    @EvaluateRelAt C F sourceCode [.op trace (.wordOp op) targetArgs] :=
  evaluateRel_ordinary trace (.wordOp op) targetArgs sourceCode (by simp) (by simp)
    argsIH (primitiveSimulation_word op)

/-- Block construction relates all fields, including closures. -/
theorem primitiveSimulation_block_cons {C F : Type} (tag : Nat) :
    @PrimitiveSimulation C F (.blockOp (.cons tag)) := by
  intro source target left right states values
  simp only [doApp, applyBlock]
  exact ⟨.block tag left, source, .block tag left right values, states, rfl⟩

/-- Block construction satisfies the evaluation simulation. -/
theorem evaluateRel_block_cons {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetArgs) :
    @EvaluateRelAt C F sourceCode [.op trace (.blockOp (.cons tag)) targetArgs] :=
  evaluateRel_ordinary trace (.blockOp (.cons tag)) targetArgs sourceCode (by simp) (by simp)
    argsIH (primitiveSimulation_block_cons tag)

end Flapjack.Compiler.Backend.ClosMti
