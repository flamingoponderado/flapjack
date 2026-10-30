import Flapjack.Compiler.Backend.BvlConst
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateList

/-! Correctness prerequisites for BVL constant operation rewrites. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.Compiler.Backend.BvlProps

namespace SmartOpCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end SmartOpCarrier

/-- A recognized simple expression is exactly an argument-free integer
constant. This local theorem is tagged after the typed original proof replay. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "dest_simple_eq"]
theorem simple_eq (expression : Bvl.Exp) (n : Int) :
    simple expression = some n ↔ expression = .op (.intOp (.const n)) [] := by
  cases expression <;> try simp [simple]
  case op op args =>
    cases op <;> try simp
    case intOp operation =>
      cases operation <;> try simp
      case const value => cases args <;> simp

/-- The unary operation rewrite preserves the original evaluation whenever
that evaluation is not a type error. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp1_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp1_correct {C F : Type} (op : ClosLang.Op) (x : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op op [x]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp1 op x], env, state) = (result, final) := by
  cases op <;> try (simpa [smartOp1] using run)
  case blockOp operation =>
    cases operation <;> try (simpa [smartOp1] using run)
    case equalConst part =>
      cases part <;> try (simpa [smartOp1] using run)
      case int a =>
        cases hx : simple x with
        | none => simpa [smartOp1, hx] using run
        | some b =>
          have xeq := (simple_eq x b).1 hx
          subst x
          by_cases same : b = a
          · subst b
            simp [smartOp1, simple, BvlConst.bool, evaluateTuple, evaluate,
              fixClock, doApp, applyNumeric, doIntApp, applyBlock, boolValue,
              BackendCommon.boolToTag, BackendCommon.trueTag] at run ⊢
            exact run
          · have reverse : a ≠ b := Ne.symm same
            simp [smartOp1, simple, BvlConst.bool, evaluateTuple, evaluate,
              fixClock, doApp, applyNumeric, doIntApp, applyBlock, boolValue,
              BackendCommon.boolToTag, BackendCommon.falseTag,
              same, reverse] at run ⊢
            exact run

/-- Evaluating an integer constant neither depends on the environment nor
changes the state. This is a Flapjack proof helper. -/
theorem evaluate_intConst {C F : Type} (n : Int) (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp (.const n)) []], env, state) = (.val [.number n], state) := by
  simp [evaluateTuple, evaluate, fixClock, doApp, applyNumeric, doIntApp]

/-- Expression-list evaluation with a leading integer constant. This helper
has no standalone HOL declaration. -/
theorem evaluate_const_cons {C F : Type} (n : Int) (tail : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ((.op (.intOp (.const n)) []) :: tail, env, state) =
      match evaluateTuple (tail, env, state) with
      | (.val values, next) => (.val (.number n :: values), next)
      | (.err error, next) => (.err error, next) := by
  rw [evaluateCons, evaluate_intConst]
  cases h : evaluateTuple (tail, env, state) with
  | mk result next => cases result <;> simp [h, Flapjack.holHd]

/-- Evaluate a singleton expression followed by an integer constant. This
Flapjack helper preserves the state at which the constant is evaluated. -/
theorem evaluate_snoc_const {C F : Type} (n : Int) (head : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([head, .op (.intOp (.const n)) []], env, state) =
      match evaluateTuple ([head], env, state) with
      | (.val values, next) => (.val [@Flapjack.holHd Value ⟨unitValue⟩ values, .number n], next)
      | (.err error, next) => (.err error, next) := by
  rw [evaluateCons]
  cases h : evaluateTuple ([head], env, state) with
  | mk result next =>
    cases result <;> simp [evaluate_intConst]

/-- Expand integer-operation evaluation after its argument list has run.
This is Flapjack proof infrastructure for operation rewrites. -/
theorem evaluate_intOp {C F : Type} (operation : ClosLang.IntOp) (args : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp operation) args], env, state) =
      match evaluateTuple (args, env, state) with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match doApp (.intOp operation) values.reverse next with
        | .err error => (.err error, next)
        | .val (value, final) => (.val [value], final) := by
  change evaluate [.op (.intOp operation) args] env state = _
  rw [evaluate, fixClock_evaluate]
  cases h : evaluate args env state with
  | mk result next =>
    cases result with
    | val values => simp only [evaluateTuple, h]; rfl
    | err error => simp only [evaluateTuple, h]

/-- Moving a constant across the other operand preserves the three arithmetic
forms used by the source flip. This is a Flapjack proof helper. -/
theorem evaluate_arithmetic_flip {C F : Type} (n : Int) (y : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .add) [.op (.intOp (.const n)) [], y]], env, state) =
        evaluateTuple ([.op (.intOp .add) [y, .op (.intOp (.const n)) []]], env, state) ∧
    evaluateTuple ([.op (.intOp .mult) [.op (.intOp (.const n)) [], y]], env, state) =
        evaluateTuple ([.op (.intOp .mult) [y, .op (.intOp (.const n)) []]], env, state) ∧
    evaluateTuple ([.op (.intOp .sub) [.op (.intOp (.const n)) [], y]], env, state) =
        evaluateTuple ([.op (.intOp .add) [y, .op (.intOp (.const (-n))) []]], env, state) := by
  cases h : evaluateTuple ([y], env, state) with
  | mk result next =>
    cases result with
    | err error =>
      simp [evaluate_intOp, evaluate_const_cons, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing y env state values next h
      cases value <;>
        simp [evaluate_intOp, evaluate_const_cons, evaluate_snoc_const, h,
          Flapjack.holHd, doApp, applyNumeric, doIntApp, Int.add_comm, Int.mul_comm,
          Int.sub_eq_add_neg]

/-- The operand-flipping step preserves a non-type-error result and state. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp_flip_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOpFlip_correct {C F : Type} (op op' : ClosLang.Op)
    (x y x' y' : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (flipped : (op', x', y') = smartOpFlip op x y)
    (run : evaluateTuple ([.op op [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op op' [x', y']], env, state) = (result, final) := by
  cases hx : simple x with
  | none =>
    simp [smartOpFlip, hx] at flipped
    rcases flipped with ⟨rfl, rfl, rfl⟩
    exact run
  | some n =>
    have xeq := (simple_eq x n).1 hx
    subst x
    cases op <;> try (simp [smartOpFlip, simple] at flipped; rcases flipped with ⟨rfl, rfl, rfl⟩; exact run)
    case intOp operation =>
      cases operation <;> try (simp [smartOpFlip, simple] at flipped; rcases flipped with ⟨rfl, rfl, rfl⟩; exact run)
      case add =>
        simp [smartOpFlip, simple] at flipped
        rcases flipped with ⟨rfl, rfl, rfl⟩
        exact (evaluate_arithmetic_flip n x' env state).1.symm.trans run
      case mult =>
        simp [smartOpFlip, simple] at flipped
        rcases flipped with ⟨rfl, rfl, rfl⟩
        exact (evaluate_arithmetic_flip n x' env state).2.1.symm.trans run
      case sub =>
        simp [smartOpFlip, simple] at flipped
        rcases flipped with ⟨rfl, rfl, rfl⟩
        exact (evaluate_arithmetic_flip n x' env state).2.2.symm.trans run

end Flapjack.Compiler.Backend.BvlConst.Proofs
