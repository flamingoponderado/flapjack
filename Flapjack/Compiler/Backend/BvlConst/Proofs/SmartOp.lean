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

/-- The binary-operation recognizer succeeds exactly for a constant second
operand. The local original is captured by a typed HOL proof replay. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "case_op_const_eq"]
theorem opConst_eq (expression : Bvl.Exp) (result : ClosLang.Op × Bvl.Exp × Int) :
    opConst expression = some result ↔
      ∃ op x n, result = (op, x, n) ∧
        expression = .op op [x, .op (.intOp (.const n)) []] := by
  cases expression <;> try simp [opConst]
  case op op args =>
    cases args with
    | nil => simp
    | cons x tail =>
      cases tail with
      | nil => simp
      | cons y rest =>
        cases rest with
        | cons z rest => simp
        | nil =>
          cases y <;> try simp
          case op inner operands =>
            cases inner <;> try simp
            case intOp operation =>
              cases operation <;> try simp
              case const n =>
                cases operands <;> simp
                constructor
                · intro eq; exact ⟨op, x, n, eq.symm, rfl, rfl, rfl⟩
                · rintro ⟨_, _, _, eq, rfl, rfl, rfl⟩; exact eq.symm

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

/-- Expand block-operation evaluation after its argument list has run. This
is Flapjack proof infrastructure for equality rewrites. -/
theorem evaluate_blockOp {C F : Type} (operation : ClosLang.BlockOp) (args : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.blockOp operation) args], env, state) =
      match evaluateTuple (args, env, state) with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match doApp (.blockOp operation) values.reverse next with
        | .err error => (.err error, next)
        | .val (value, final) => (.val [value], final) := by
  change evaluate [.op (.blockOp operation) args] env state = _
  rw [evaluate, fixClock_evaluate]
  cases h : evaluate args env state with
  | mk result next =>
    cases result with
    | val values => simp only [evaluateTuple, h]; rfl
    | err error => simp only [evaluateTuple, h]

/-- Expand memory-operation evaluation after its argument list has run.
This is Flapjack proof infrastructure for the element-access rewrite. -/
theorem evaluate_memOp {C F : Type} (operation : ClosLang.MemOp) (args : List Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.memOp operation) args], env, state) =
      match evaluateTuple (args, env, state) with
      | (.err error, next) => (.err error, next)
      | (.val values, next) =>
        match doApp (.memOp operation) values.reverse next with
        | .err error => (.err error, next)
        | .val (value, final) => (.val [value], final) := by
  change evaluate [.op (.memOp operation) args] env state = _
  rw [evaluate, fixClock_evaluate]
  cases h : evaluate args env state with
  | mk result next =>
    cases result with
    | val values => simp only [evaluateTuple, h]; rfl
    | err error => simp only [evaluateTuple, h]

/-- Comparing an integer constant to an arbitrary expression agrees with the
specialized equality operation on that expression, in either operand order.
This is Flapjack proof infrastructure for the binary source theorem. -/
theorem evaluate_equal_const {C F : Type} (n : Int) (x : Bvl.Exp)
    (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.blockOp .equal) [.op (.intOp (.const n)) [], x]], env, state) =
        evaluateTuple ([.op (.blockOp (.equalConst (.int n))) [x]], env, state) ∧
    evaluateTuple ([.op (.blockOp .equal) [x, .op (.intOp (.const n)) []]], env, state) =
        evaluateTuple ([.op (.blockOp (.equalConst (.int n))) [x]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk result next =>
    cases result with
    | err error => simp [evaluate_blockOp, evaluate_const_cons, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_blockOp, evaluate_const_cons, evaluate_snoc_const, h,
          Flapjack.holHd, doApp, applyBlock, doEq]
      apply congrArg boolValue
      rename_i a
      by_cases same : a = n
      · subst a; rfl
      · have reverse : n ≠ a := Ne.symm same
        simp [same, reverse]

/-- A nonnegative constant index gives the same element-access result in the
memory and specialized block operations. This is a Flapjack proof helper. -/
theorem evaluate_el_const {C F : Type} (n : Int) (x : Bvl.Exp)
    (env : List Value) (state : State C F) (nonnegative : ¬ n < 0) :
    evaluateTuple ([.op (.memOp .el) [.op (.intOp (.const n)) [], x]], env, state) =
      evaluateTuple ([.op (.blockOp (.elemAt n.toNat)) [x]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk result next =>
    cases result with
    | err error => simp [evaluate_memOp, evaluate_blockOp, evaluate_const_cons, h]
    | val values =>
      obtain ⟨value, rfl⟩ := evaluateSing x env state values next h
      cases value <;>
        simp [evaluate_memOp, evaluate_blockOp, evaluate_const_cons, h,
          doApp, applyMemory, applyBlock, nonnegative]
      rfl

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

/-- Division case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_div_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .div) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .div, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases zero : a = 0
      · simpa [smartOp2, simple, zero] using run
      · simp [evaluateTuple, evaluate, fixClock, doApp, applyNumeric, doIntApp, zero] at run
        rcases run with ⟨rfl, rfl⟩
        simp only [smartOp2, simple, beq_iff_eq, if_neg zero]
        change evaluateTuple ([.op (.intOp (.const (b.fdiv a))) []], env, state) = _
        exact evaluate_intConst (b.fdiv a) env state

/-- Remainder case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_mod_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mod) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mod, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases zero : a = 0
      · simpa [smartOp2, simple, zero] using run
      · simp [evaluateTuple, evaluate, fixClock, doApp, applyNumeric, doIntApp, zero] at run
        rcases run with ⟨rfl, rfl⟩
        simp only [smartOp2, simple, beq_iff_eq, if_neg zero]
        change evaluateTuple ([.op (.intOp (.const (b.fmod a))) []], env, state) = _
        exact evaluate_intConst (b.fmod a) env state

/-- Equality case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_equal_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.blockOp .equal) [x, y]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.blockOp .equal, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ey := (simple_eq y b).1 hy
      subst y
      have rewritten := (evaluate_equal_const b x env state).2.symm.trans run
      have hc : simple (.op (.intOp (.const b)) []) = some b := rfl
      simpa only [smartOp2, hx, hc] using rewritten
  | some a =>
    have ex := (simple_eq x a).1 hx
    subst x
    cases hy : simple y with
    | none =>
      have rewritten := (evaluate_equal_const a y env state).1.symm.trans run
      have hc : simple (.op (.intOp (.const a)) []) = some a := rfl
      simpa only [smartOp2, hc, hy] using rewritten
    | some b =>
      have ey := (simple_eq y b).1 hy
      subst y
      have rewritten := (evaluate_equal_const a (.op (.intOp (.const b)) []) env state).1.symm.trans run
      have unary := smartOp1_correct (.blockOp (.equalConst (.int a)))
        (.op (.intOp (.const b)) []) env state final result rewritten notTypeError
      simpa [smartOp2, smartOp1, simple] using unary

/-- Element-access case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_el_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.memOp .el) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.memOp .el, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some n =>
    have ex := (simple_eq x n).1 hx
    subst x
    by_cases negative : n < 0
    · simpa [smartOp2, simple, negative] using run
    · have rewritten := (evaluate_el_const n y env state negative).symm.trans run
      simpa [smartOp2, simple, negative] using rewritten

/-- Less-than case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_less_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .less) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .less, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases h : b < a
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.trueTag, h] at run ⊢
        exact run
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.falseTag, h] at run ⊢
        exact run


/-- Less-or-equal case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_lessEq_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .lessEq) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .lessEq, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases h : b ≤ a
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.trueTag, h] at run ⊢
        exact run
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.falseTag, h] at run ⊢
        exact run


/-- Greater-than case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_greater_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .greater) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .greater, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases h : b > a
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.trueTag, h] at run ⊢
        exact run
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.falseTag, h] at run ⊢
        exact run


/-- Greater-or-equal case of the binary rewrite correctness theorem. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_greaterEq_correct {C F : Type} (x y : Bvl.Exp) (env : List Value)
    (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .greaterEq) [x, y]], env, state) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .greaterEq, x, y)], env, state) = (result, final) := by
  cases hx : simple x with
  | none => simpa [smartOp2, hx] using run
  | some a =>
    cases hy : simple y with
    | none => simpa [smartOp2, hx, hy] using run
    | some b =>
      have ex := (simple_eq x a).1 hx
      have ey := (simple_eq y b).1 hy
      subst x
      subst y
      by_cases h : b ≥ a
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.trueTag, h] at run ⊢
        exact run
      · simp [smartOp2, simple, BvlConst.bool, evaluateTuple, evaluate, fixClock,
          doApp, applyNumeric, doIntApp, applyBlock, boolValue, BackendCommon.boolToTag,
          BackendCommon.falseTag, h] at run ⊢
        exact run

end Flapjack.Compiler.Backend.BvlConst.Proofs
