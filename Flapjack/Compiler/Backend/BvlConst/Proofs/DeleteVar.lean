import Flapjack.Compiler.Backend.BvlConst.Proofs.Relations
import Flapjack.Compiler.Backend.BvlConst.Extract
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Semantic prerequisites for deleting let-bound variable aliases. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

namespace DeleteVarListCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end DeleteVarListCarrier

/-- The shifted alias emitted for a variable refers past the newly introduced
bindings to the same source value. This is a Flapjack proof helper. -/
theorem extracted_var_valueRel (C F : Type) (index : Nat) (tail : List Bvl.Exp)
    (value replacement : Value) (sourceSuffix outputValues env : List Value)
    (lengths : outputValues.length = tail.length) (lookup : env[index]? = some value) :
    valueRel C F (.var (index + tail.length + 1)) value replacement
      (value :: sourceSuffix) (replacement :: (outputValues ++ env)) := by
  simp only [valueRel, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by omega)]
  simpa [lengths, Nat.add_comm] using lookup

/-- Successful variable deletion supplies both the transformed singleton run
and the relation for the newly extracted shifted alias. This is a Flapjack
case lemma for the successful-list simulation. -/
theorem evaluate_deleteVar_var_rel {C F : Type} (index : Nat) (tail : List Bvl.Exp)
    (state next : State C F) (env sourceSuffix outputValues : List Value) (value : Value)
    (run : evaluate [.var index] env state = (.val [value], next))
    (lengths : outputValues.length = tail.length) :
    evaluate [BvlConst.deleteVar (.var index)] env state = (.val [.number 0], next) ∧
      valueRel C F (.var (index + tail.length + 1)) value (.number 0)
        (value :: sourceSuffix) (.number 0 :: (outputValues ++ env)) := by
  cases lookup : env[index]? with
  | none => simp [evaluate, lookup] at run
  | some found =>
    simp [evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    constructor
    · change evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state)
      simp [evaluate, fixClock, doApp, applyNumeric, doIntApp]
    · exact extracted_var_valueRel C F index tail found (.number 0) sourceSuffix outputValues env lengths lookup

/-- Extend the induction relation with an extracted variable alias. This is a
Flapjack case lemma for the successful-list simulation. -/
theorem envRel_extend_extracted_var (C F : Type) (index : Nat) (tail : List Bvl.Exp)
    (annotations : List (Option Bvl.Exp)) (value : Value)
    (values source outputValues env : List Value)
    (lengths : outputValues.length = tail.length) (lookup : env[index]? = some value)
    (related : envRel C F (extractList tail ++ annotations)
      (values ++ source) (outputValues ++ env)) :
    envRel C F (extractList (.var index :: tail) ++ annotations)
      ((value :: values) ++ source) ((.number 0 :: outputValues) ++ env) := by
  simp only [extractList_cons, extractSource, List.cons_append, envRel]
  exact ⟨extracted_var_valueRel C F index tail value (.number 0)
    (values ++ source) outputValues env lengths lookup, related⟩

/-- Integer constants evaluate to the same number in every state and
environment. This Flapjack helper supplies the operation branch of the value
relation for extracted constants. -/
theorem extracted_int_valueRel (C F : Type) (n : Int) (sourceEnv targetEnv : List Value) :
    valueRel C F (.op (.intOp (.const n)) []) (.number n) (.number n) sourceEnv targetEnv := by
  simp only [valueRel, true_and]
  intro state env
  simp [evaluate, fixClock, doApp, applyNumeric, doIntApp]

/-- Empty block constructors evaluate to the same block in every state and
environment. This Flapjack helper supplies the other extracted operation case. -/
theorem extracted_block_valueRel (C F : Type) (tag : Nat) (sourceEnv targetEnv : List Value) :
    valueRel C F (.op (.blockOp (.cons tag)) []) (.block tag []) (.block tag [])
      sourceEnv targetEnv := by
  simp only [valueRel, true_and]
  intro state env
  simp [evaluate, fixClock, doApp, applyBlock]

/-- A successful integer-constant operation has no arguments and leaves the
state unchanged. This is a Flapjack case lemma for extracted bindings. -/
theorem evaluate_intConst_success {C F : Type} (n : Int) (args : List Bvl.Exp)
    (env : List Value) (state next : State C F) (value : Value)
    (run : evaluate [.op (.intOp (.const n)) args] env state = (.val [value], next)) :
    args = [] ∧ value = .number n ∧ next = state := by
  simp only [evaluate, fixClock_evaluate] at run
  cases argsRun : evaluate args env state with
  | mk argResult middle =>
    cases argResult with
    | err error => simp [argsRun] at run
    | val values =>
      have length := evaluate_length args env state middle values argsRun
      cases reverse : values.reverse with
      | nil =>
        have valuesNil : values = [] := by simpa using congrArg List.reverse reverse
        subst values
        have argsNil : args = [] := by cases args <;> simp_all
        subst args
        simp [evaluate] at argsRun
        subst middle
        simp [evaluate, doApp, applyNumeric, doIntApp] at run
        exact ⟨rfl, run.1.symm, run.2.symm⟩
      | cons v vs => simp [argsRun, reverse, doApp, applyNumeric, doIntApp] at run

/-- One successful binding can be transformed while establishing the value
relation for any extracted annotation. This Flapjack induction helper keeps
the original successful evaluation and the arbitrary suffix environment. -/
theorem evaluate_deleteVar_head_rel {C F : Type} (expression : Bvl.Exp)
    (tail : List Bvl.Exp) (env sourceSuffix outputValues : List Value)
    (state next : State C F) (value : Value)
    (run : evaluate [expression] env state = (.val [value], next))
    (lengths : outputValues.length = tail.length) :
    ∃ output, evaluate [BvlConst.deleteVar expression] env state = (.val [output], next) ∧
      match extractSource expression tail with
      | none => value = output
      | some extracted => valueRel C F extracted value output
          (value :: sourceSuffix) (output :: (outputValues ++ env)) := by
  cases expression with
  | var index =>
    refine ⟨.number 0, ?_⟩
    simpa [extractSource] using
      evaluate_deleteVar_var_rel index tail state next env sourceSuffix outputValues value run lengths
  | op op args =>
    cases op with
    | intOp operation =>
      cases operation with
      | const n =>
        obtain ⟨rfl, rfl, rfl⟩ := evaluate_intConst_success n args env state next value run
        refine ⟨.number n, ?_, ?_⟩
        · simpa [BvlConst.deleteVar] using run
        · simpa [extractSource] using extracted_int_valueRel C F n
            (.number n :: sourceSuffix) (.number n :: (outputValues ++ env))
      | _ => exact ⟨value, by simpa [BvlConst.deleteVar] using run, by rfl⟩
    | blockOp operation =>
      cases operation with
      | cons tag =>
        cases args with
        | nil =>
          simp [evaluate, fixClock, doApp, applyBlock] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨.block tag [], ?_, ?_⟩
          · simp [BvlConst.deleteVar, evaluate, fixClock, doApp, applyBlock]
          · simpa [extractSource] using extracted_block_valueRel C F tag
              (.block tag [] :: sourceSuffix) (.block tag [] :: (outputValues ++ env))
        | cons arg args => exact ⟨value, by simpa [BvlConst.deleteVar] using run, by rfl⟩
      | _ => exact ⟨value, by simpa [BvlConst.deleteVar] using run, by rfl⟩
    | _ => exact ⟨value, by simpa [BvlConst.deleteVar] using run, by rfl⟩
  | _ => exact ⟨value, by simpa [BvlConst.deleteVar] using run, by rfl⟩

/-- Successful variable deletion produces values related by the extracted
annotations, preserving the final state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "evaluate_delete_var_Rval"
  (fmap_as_finite_support := [refs])]
theorem evaluate_deleteVar_list_success {C F : Type} (expressions : List Bvl.Exp)
    (targetEnv sourceEnv : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F) (values : List Value)
    (annotations : List (Option Bvl.Exp))
    (run : evaluateTuple (expressions, targetEnv, state) = (.val values, final))
    (related : envRel C F annotations sourceEnv targetEnv) :
    ∃ output, evaluateTuple (expressions.map BvlConst.deleteVar, targetEnv, state) = (.val output, final) ∧
      envRel C F (extractList expressions ++ annotations) (values ++ sourceEnv) (output ++ targetEnv) := by
  induction expressions generalizing state values with
  | nil =>
    simp [evaluateTuple, evaluate] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨[], by simp [evaluateTuple, evaluate], by simpa [extractList] using related⟩
  | cons head tail ih =>
    rw [evaluateCons] at run
    cases headRun : evaluateTuple ([head], targetEnv, state) with
    | mk headResult middle =>
      cases headResult with
      | err error => simp [headRun] at run
      | val headValues =>
        obtain ⟨value, rfl⟩ := evaluateSing head targetEnv state headValues middle headRun
        simp only [headRun] at run
        cases tailRun : evaluateTuple (tail, targetEnv, middle) with
        | mk tailResult last =>
          cases tailResult with
          | err error => simp [tailRun] at run
          | val tailValues =>
            simp [tailRun, Flapjack.holHd] at run
            rcases run with ⟨rfl, rfl⟩
            obtain ⟨outputs, outputRun, tailRel⟩ := ih middle tailValues tailRun
            have outputRun' : evaluate (tail.map BvlConst.deleteVar) targetEnv middle = (.val outputs, last) := outputRun
            have outputLength := evaluate_length (tail.map BvlConst.deleteVar) targetEnv middle last outputs outputRun'
            simp only [List.length_map] at outputLength
            have headRun' : evaluate [head] targetEnv state = (.val [value], middle) := headRun
            obtain ⟨output, transformedHead, headRel⟩ :=
              evaluate_deleteVar_head_rel head tail targetEnv (tailValues ++ sourceEnv)
                outputs state middle value headRun' outputLength
            refine ⟨output :: outputs, ?_, ?_⟩
            · simp only [List.map_cons]
              rw [evaluateCons]
              change evaluateTuple ([BvlConst.deleteVar head], targetEnv, state) = (.val [output], middle) at transformedHead
              simp [transformedHead, outputRun, Flapjack.holHd]
            · simp only [extractList_cons, List.cons_append]
              cases extracted : extractSource head tail with
              | none =>
                simp only [extracted] at headRel
                simp only [envRel]
                exact ⟨headRel, tailRel⟩
              | some expression =>
                simp only [extracted] at headRel
                simp only [envRel]
                exact ⟨headRel, tailRel⟩

/-- A successfully evaluated singleton still succeeds after variable deletion
and leaves the same state, though its value may change. This helper has no
standalone HOL declaration. -/
theorem evaluate_deleteVar_success {C F : Type} (expression : Bvl.Exp)
    (state next : State C F) (env : List Value) (values : List Value)
    (run : evaluate [expression] env state = (.val values, next)) :
    ∃ output, evaluate [BvlConst.deleteVar expression] env state = (.val output, next) := by
  cases expression with
  | var index =>
    cases lookup : env[index]? with
    | none => simp [evaluate, lookup] at run
    | some value =>
      simp [evaluate, lookup] at run
      obtain ⟨_, rfl⟩ := run
      refine ⟨[.number 0], ?_⟩
      change evaluate [.op (.intOp (.const 0)) []] env state = (.val [.number 0], state)
      simp [evaluate, fixClock, doApp, applyNumeric, doIntApp]
  | _ => exact ⟨values, by simpa [BvlConst.deleteVar] using run⟩

/-- Deleting variable aliases in an expression list preserves a non-type-error
result and its final state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "evaluate_delete_var_Rerr"
  (fmap_as_finite_support := [refs])]
theorem evaluate_deleteVar_list_error {C F : Type} (expressions : List Bvl.Exp)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F) (env : List Value)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (run : evaluateTuple (expressions, env, state) = (.err error, final))
    (notTypeError : error ≠ .abort .typeError) :
    evaluateTuple (expressions.map BvlConst.deleteVar, env, state) = (.err error, final) := by
  induction expressions generalizing state with
  | nil => simp [evaluateTuple, evaluate] at run
  | cons head tail ih =>
    rw [evaluateCons] at run
    simp only [List.map_cons]
    rw [evaluateCons]
    cases headRun : evaluateTuple ([head], env, state) with
    | mk headResult next =>
      cases headResult with
      | err headError =>
        simp [headRun] at run
        rcases run with ⟨rfl, rfl⟩
        rw [evaluate_deleteVar_error head state next headError env headRun notTypeError]
      | val values =>
        have headRun' : evaluate [head] env state = (.val values, next) := headRun
        obtain ⟨output, transformedHead⟩ := evaluate_deleteVar_success head state next env values headRun'
        change evaluateTuple ([BvlConst.deleteVar head], env, state) = (.val output, next) at transformedHead
        simp only [headRun] at run
        rw [transformedHead]
        cases tailRun : evaluateTuple (tail, env, next) with
        | mk tailResult last =>
          cases tailResult with
          | val tailValues => simp [tailRun] at run
          | err tailError =>
            simp [tailRun] at run
            rcases run with ⟨rfl, rfl⟩
            dsimp only
            rw [ih next tailRun]

end Flapjack.Compiler.Backend.BvlConst.Proofs
