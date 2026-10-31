import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpState
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.BvlInline.Proofs.VarListEvaluate

/-! Structural evaluator cases for the let-operation simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Induction proposition for a list of let-operation expressions, with the
same mapped state relation and non-type-error condition as the source proof. -/
def letOpSimulation {C F : Type} (splitSeq : Bool) (limit : Nat)
    (expressions : List Bvl.Exp) (env : List Value) (source : State C F) : Prop :=
  ∀ (result : Result (List Value) Value) (final target : State C F),
    mappedStateRel (letOpTransform splitSeq limit) source target →
    evaluate expressions env source = (result, final) →
    result ≠ .err (.abort .typeError) →
    ∃ targetFinal, evaluate (letOp expressions) env target = (result, targetFinal) ∧
      mappedStateRel (letOpTransform splitSeq limit) final targetFinal

/-- The empty-list case of the let-operation evaluator simulation. -/
theorem letOpSimulation_nil {C F : Type} (splitSeq : Bool) (limit : Nat)
    (env : List Value) (source : State C F) :
    letOpSimulation splitSeq limit [] env source := by
  intro result final target related run _
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨target, by simp [letOp, letOpList, evaluate], related⟩

/-- Variable lookup is unchanged by the let-operation traversal. -/
theorem letOpSimulation_var {C F : Type} (splitSeq : Bool) (limit index : Nat)
    (env : List Value) (source : State C F) :
    letOpSimulation splitSeq limit [.var index] env source := by
  intro result final target related run _
  cases found : env[index]? <;> simp [evaluate, found] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals exact ⟨target, by simp [letOp, letOpList, letOpOne, evaluate, found], related⟩

/-- The tick case follows from its body's induction hypothesis at the
decremented clock. -/
theorem letOpSimulation_tick {C F : Type} (splitSeq : Bool) (limit : Nat)
    (body : Bvl.Exp) (env : List Value) (source : State C F)
    (bodyIH : ∀ state : State C F, state.clock < source.clock →
      letOpSimulation splitSeq limit [body] env state) :
    letOpSimulation splitSeq limit [.tick body] env source := by
  intro result final target related run notType
  have clocks : target.clock = source.clock := by
    simpa using congrArg (fun state : State C F => state.clock) related.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := clocks.trans zero
    simp [evaluate, zero] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨target, by simp [letOp, letOpList, letOpOne, evaluate, targetZero], related⟩
  · have targetNonzero : target.clock ≠ 0 := by simpa [clocks] using zero
    have bodyRun : evaluate [body] env (decClock 1 source) = (result, final) := by
      simpa [evaluate, zero] using run
    obtain ⟨targetFinal, targetRun, finalRel⟩ :=
      bodyIH (decClock 1 source) (by simp [decClock]; omega) result final (decClock 1 target)
        (mappedStateRel_decClock _ source target related 1) bodyRun notType
    refine ⟨targetFinal, ?_, finalRel⟩
    simpa [letOp, letOpList, letOpOne, evaluate, targetNonzero] using targetRun

/-- The raise case follows from the body's induction hypothesis. -/
theorem letOpSimulation_raise {C F : Type} (splitSeq : Bool) (limit : Nat)
    (body : Bvl.Exp) (env : List Value) (source : State C F)
    (bodyIH : letOpSimulation splitSeq limit [body] env source) :
    letOpSimulation splitSeq limit [.raise body] env source := by
  intro result final target related run notType
  rw [evaluate] at run
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyFinal =>
    rw [bodyRun] at run
    have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
      cases bodyResult with
      | val values => simp
      | err error =>
        simp at run
        rcases run with ⟨rfl, _⟩
        exact notType
    obtain ⟨targetFinal, targetRun, finalRel⟩ := bodyIH bodyResult bodyFinal target related bodyRun bodyNotType
    refine ⟨targetFinal, ?_, ?_⟩
    · simp only [letOp, letOpList, letOpOne] at targetRun ⊢
      rw [evaluate, targetRun]
      cases bodyResult <;> simp_all
    · cases bodyResult <;> simp_all

/-- Primitive operations follow from the argument simulation and the
mapped-state dispatcher simulation, including installation. -/
theorem letOpSimulation_op {C F : Type} (splitSeq : Bool) (limit : Nat)
    (op : ClosLang.Op) (args : List Bvl.Exp) (env : List Value) (source : State C F)
    (argsIH : letOpSimulation splitSeq limit args env source) :
    letOpSimulation splitSeq limit [.op op args] env source := by
  intro result final target related run notType
  rw [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    rw [argsRun] at run
    have argsNotType : argsResult ≠ .err (.abort .typeError) := by
      cases argsResult with
      | val values => simp
      | err error =>
        simp at run
        rcases run with ⟨rfl, _⟩
        exact notType
    obtain ⟨targetMiddle, targetArgs, middleRel⟩ :=
      argsIH argsResult middle target related argsRun argsNotType
    cases argsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetMiddle, ?_, middleRel⟩
      simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
      rw [evaluate, fixClock_evaluate, targetArgs]
    | val values =>
      have simulated := letOp_doApp splitSeq limit middle targetMiddle middleRel op values.reverse
      cases appRun : doApp op values.reverse middle with
      | err error =>
        simp [appRun] at run simulated
        rcases run with ⟨rfl, rfl⟩
        refine ⟨targetMiddle, ?_, middleRel⟩
        simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
        rw [evaluate, fixClock_evaluate, targetArgs]
        simp [simulated]
      | val pair =>
        obtain ⟨value, next⟩ := pair
        simp [appRun] at run simulated
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetFinal, finalRel, targetApp⟩ := simulated
        refine ⟨targetFinal, ?_, finalRel⟩
        simp only [letOp, letOpList, letOpOne] at targetArgs ⊢
        rw [evaluate, fixClock_evaluate, targetArgs]
        simp [targetApp]

/-- Sequencing follows by composing the head and tail simulations. -/
theorem letOpSimulation_cons {C F : Type} (splitSeq : Bool) (limit : Nat)
    (first second : Bvl.Exp) (rest : List Bvl.Exp) (env : List Value) (source : State C F)
    (headIH : letOpSimulation splitSeq limit [first] env source)
    (tailIH : ∀ state : State C F, state.clock ≤ source.clock →
      letOpSimulation splitSeq limit (second :: rest) env state) :
    letOpSimulation splitSeq limit (first :: second :: rest) env source := by
  intro result final target related run notType
  rw [evaluate, fixClock_evaluate] at run
  cases headRun : evaluate [first] env source with
  | mk headResult middle =>
    rw [headRun] at run
    have bound : middle.clock ≤ source.clock := by
      have clock := evaluate_clock_le [first] env source
      simpa [headRun] using clock
    have headNotType : headResult ≠ .err (.abort .typeError) := by
      cases headResult with
      | val values => simp
      | err error =>
        simp at run
        rcases run with ⟨rfl, _⟩
        exact notType
    obtain ⟨targetMiddle, targetHead, middleRel⟩ := headIH headResult middle target related headRun headNotType
    simp only [letOp, letOpList] at targetHead
    cases headResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetMiddle, ?_, middleRel⟩
      simp only [letOp, letOpList]
      rw [evaluate, fixClock_evaluate, targetHead]
    | val values =>
      cases tailRun : evaluate (second :: rest) env middle with
      | mk tailResult tailFinal =>
        rw [tailRun] at run
        have tailNotType : tailResult ≠ .err (.abort .typeError) := by
          cases tailResult with
          | val vals => simp
          | err error =>
            simp at run
            rcases run with ⟨rfl, _⟩
            exact notType
        obtain ⟨targetFinal, targetTail, finalRel⟩ :=
          tailIH middle bound tailResult tailFinal targetMiddle middleRel tailRun tailNotType
        simp only [letOp, letOpList] at targetTail
        refine ⟨targetFinal, ?_, ?_⟩
        · simp only [letOp, letOpList]
          rw [evaluate, fixClock_evaluate, targetHead, targetTail]
          cases tailResult <;> simp_all
        · cases tailResult <;> simp_all

/-- The let-operation peephole has the same evaluation as a let with both
subexpressions already transformed. -/
theorem letOp_let_evaluate {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluate (letOp [.let bindings body]) env state =
      evaluate [.let (letOp bindings) (letOpOne body)] env state := by
  simp only [letOp, letOpList, letOpOne]
  cases transformed : letOpOne body with
  | op op variables =>
    simp only [destOp]
    by_cases valid : varListHOL 0 variables (letOpList bindings) = true
    · simp only [valid, ↓reduceIte]
      exact (evaluateLetOpReduction (letOpList bindings) variables op env state valid).symm
    · simp [valid]
  | _ => simp [destOp]

/-- The let case composes binding and body simulations; the local peephole
reduction is valid even when bindings fail. -/
theorem letOpSimulation_let {C F : Type} (splitSeq : Bool) (limit : Nat)
    (bindings : List Bvl.Exp) (body : Bvl.Exp) (env : List Value) (source : State C F)
    (bindingsIH : letOpSimulation splitSeq limit bindings env source)
    (bodyIH : ∀ (bodyEnv : List Value) (state : State C F), state.clock ≤ source.clock →
      letOpSimulation splitSeq limit [body] bodyEnv state) :
    letOpSimulation splitSeq limit [.let bindings body] env source := by
  intro result final target related run notType
  rw [evaluate, fixClock_evaluate] at run
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    rw [bindingsRun] at run
    have bound : middle.clock ≤ source.clock := by
      have clock := evaluate_clock_le bindings env source
      simpa [bindingsRun] using clock
    have bindingsNotType : bindingsResult ≠ .err (.abort .typeError) := by
      cases bindingsResult with
      | val values => simp
      | err error =>
        simp at run
        rcases run with ⟨rfl, _⟩
        exact notType
    obtain ⟨targetMiddle, targetBindings, middleRel⟩ :=
      bindingsIH bindingsResult middle target related bindingsRun bindingsNotType
    cases bindingsResult with
    | err error =>
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨targetMiddle, ?_, middleRel⟩
      rw [letOp_let_evaluate, evaluate, fixClock_evaluate, targetBindings]
    | val values =>
      have bodyRun : evaluate [body] (values ++ env) middle = (result, final) := by simpa using run
      obtain ⟨targetFinal, targetBody, finalRel⟩ :=
        bodyIH (values ++ env) middle bound result final targetMiddle middleRel bodyRun notType
      refine ⟨targetFinal, ?_, finalRel⟩
      rw [letOp_let_evaluate, evaluate, fixClock_evaluate, targetBindings]
      simpa [letOp, letOpList] using targetBody

end Flapjack.Compiler.Backend.BvlInline.Proofs
