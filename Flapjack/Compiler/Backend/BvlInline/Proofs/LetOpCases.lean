import Flapjack.Compiler.Backend.BvlInline.Proofs.LetOpState
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

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

end Flapjack.Compiler.Backend.BvlInline.Proofs
