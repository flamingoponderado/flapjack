import Flapjack.Compiler.Backend.BvlConst.Proofs.SmartOp

/-! Evaluation identities used by the arithmetic constant-folding cases. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Adding zero can be removed whenever the original result is not a type
error. This Flapjack helper retains errors and the exact final state. -/
theorem evaluate_add_zero {C F : Type} (x : Bvl.Exp) (env : List Value)
    (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add) [x, .op (.intOp (.const 0)) []]], env, state) =
      (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([x], env, state) = (result, final) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simpa [evaluate_intOp, evaluate_snoc_const, h] using run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp] at run
      all_goals try exact Prod.ext run.1 run.2
      all_goals exact False.elim (notTypeError run.1.symm)

/-- Multiplying by one can be removed whenever the original result is not a
type error. This Flapjack helper retains errors and the exact final state. -/
theorem evaluate_mul_one {C F : Type} (x : Bvl.Exp) (env : List Value)
    (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult) [x, .op (.intOp (.const 1)) []]], env, state) =
      (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([x], env, state) = (result, final) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simpa [evaluate_intOp, evaluate_snoc_const, h] using run
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp] at run
      all_goals try exact Prod.ext run.1 run.2
      all_goals exact False.elim (notTypeError run.1.symm)

/-- Merge two integer constants in nested additions. This Flapjack helper
preserves all results, including errors and state changes in the operand. -/
theorem evaluate_add_add_constants {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
    evaluateTuple ([.op (.intOp .add) [x, .op (.intOp (.const (n + m))) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error =>
      simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp, Int.add_comm, Int.add_left_comm]

/-- Merge a constant addition into a nested subtraction. This Flapjack
helper preserves the original evaluation and state for every operand. -/
theorem evaluate_add_sub_constants {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
    evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const (n + m))) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp]
      all_goals omega

/-- Fold a nested addition beneath subtraction. This Flapjack helper
preserves errors and the operand's effects. -/
theorem evaluate_sub_add_constants {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
    evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const (n - m))) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp]
      all_goals omega

/-- Fold nested subtractions into addition. This Flapjack helper preserves
errors and the operand's effects. -/
theorem evaluate_sub_sub_constants {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
    evaluateTuple ([.op (.intOp .add) [x, .op (.intOp (.const (n - m))) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp]
      all_goals omega

/-- Merge constants in nested multiplication. This Flapjack helper preserves
all results, including errors and the operand's effects. -/
theorem evaluate_mul_mul_constants {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .mult)
      [.op (.intOp .mult) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
    evaluateTuple ([.op (.intOp .mult) [x, .op (.intOp (.const (n * m))) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xResult next =>
    cases xResult with
    | err error => simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd,
          doApp, applyNumeric, doIntApp, Int.mul_assoc]

/-- The nested-add branch of the source binary rewrite. This is a Flapjack
equation exposing the executed helper's case split. -/
theorem smartOp2_nestedAdd_eq (x : Bvl.Exp) (m n : Int) :
    smartOp2 (.intOp .add,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) []) =
      if n + m = 0 then x else .op (.intOp .add) [x, .op (.intOp (.const (n + m))) []] := by
  change (if n + m == 0 then x else .op (.intOp .add) [x, .op (.intOp (.const (n + m))) []]) = _
  simp

namespace ArithmeticCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end ArithmeticCarrier

/-- Nested-add/constant case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_nestedAdd_correct {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
        (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  have normalized := (evaluate_add_add_constants x m n env state).symm.trans run
  rw [smartOp2_nestedAdd_eq]
  by_cases h : n + m = 0
  · simp only [h, ↓reduceIte]
    apply evaluate_add_zero x env state final result
    · simpa [h] using normalized
    · exact notTypeError
  · simpa [h] using normalized

/-- Nested-subtraction/constant case of addition rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_nestedSub_correct {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
        (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add,
      .op (.intOp .sub) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const (n + m))) []]], env, state) = _
  exact (evaluate_add_sub_constants x m n env state).symm.trans run

/-- Nested-addition/constant case of subtraction rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_nestedAdd_correct {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
        (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const (n - m))) []]], env, state) = _
  exact (evaluate_sub_add_constants x m n env state).symm.trans run

/-- Nested-subtraction/constant case of subtraction rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_nestedSub_correct {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
        (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub,
      .op (.intOp .sub) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  have normalized := (evaluate_sub_sub_constants x m n env state).symm.trans run
  change evaluateTuple ([if n - m == 0 then x else
    .op (.intOp .add) [x, .op (.intOp (.const (n - m))) []]], env, state) = _
  by_cases h : n - m = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    apply evaluate_add_zero x env state final result
    · simpa [h] using normalized
    · exact notTypeError
  · simpa [h] using normalized

/-- Nested-multiplication/constant case of multiplication rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_mul_nestedMul_correct {C F : Type} (x : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult)
      [.op (.intOp .mult) [x, .op (.intOp (.const m)) []], .op (.intOp (.const n)) []]], env, state) =
        (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mult,
      .op (.intOp .mult) [x, .op (.intOp (.const m)) []],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp .mult) [x, .op (.intOp (.const (n * m))) []]], env, state) = _
  exact (evaluate_mul_mul_constants x m n env state).symm.trans run

/-- Two-constant case of addition rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_constants_correct {C F : Type} (m n : Int) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp (.const m)) [], .op (.intOp (.const n)) []]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add, .op (.intOp (.const m)) [],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp (.const (n + m))) []], env, state) = _
  rw [evaluate_intOp, evaluate_const_cons, evaluate_intConst] at run
  simp [doApp, applyNumeric, doIntApp] at run
  rw [evaluate_intConst]
  exact Prod.ext run.1 run.2

/-- Two-constant case of subtraction rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_constants_correct {C F : Type} (m n : Int) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp (.const m)) [], .op (.intOp (.const n)) []]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub, .op (.intOp (.const m)) [],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp (.const (n - m))) []], env, state) = _
  rw [evaluate_intOp, evaluate_const_cons, evaluate_intConst] at run
  simp [doApp, applyNumeric, doIntApp] at run
  rw [evaluate_intConst]
  exact Prod.ext run.1 run.2

/-- Two-constant case of multiplication rewriting. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_mul_constants_correct {C F : Type} (m n : Int) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult)
      [.op (.intOp (.const m)) [], .op (.intOp (.const n)) []]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mult, .op (.intOp (.const m)) [],
      .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp (.const (n * m))) []], env, state) = _
  rw [evaluate_intOp, evaluate_const_cons, evaluate_intConst] at run
  simp [doApp, applyNumeric, doIntApp] at run
  rw [evaluate_intConst]
  exact Prod.ext run.1 run.2

end Flapjack.Compiler.Backend.BvlConst.Proofs
