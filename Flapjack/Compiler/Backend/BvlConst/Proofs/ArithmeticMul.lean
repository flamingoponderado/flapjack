import Flapjack.Compiler.Backend.BvlConst.Proofs.ArithmeticBoth
/-! Multiplication cases of the source binary rewrite correctness theorem. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps
/-- This Flapjack helper preserves evaluation order while combining product constants. -/
theorem evaluate_mul_mul_mul {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult)
      [.op (.intOp .mult) [x, .op (.intOp (.const m)) []],
       .op (.intOp .mult) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .mult) [.op (.intOp (.const (n * m))) [],
      .op (.intOp .mult) [x, y]]], env, state) = (result, final) := by
  cases hx : evaluateTuple ([x], env, state) with
  | mk xr s1 =>
    cases xr with
    | err error => simpa [evaluate_int_pair, evaluate_intConst, hx] using run
    | val values =>
      obtain ⟨v, rfl⟩ := evaluateSing x env state values s1 hx
      cases v with
      | number a =>
        cases hy : evaluateTuple ([y], env, s1) with
        | mk yr s2 =>
          cases yr with
          | err error => simpa [evaluate_int_pair, evaluate_intConst, hx, hy, Flapjack.holHd, doApp, applyNumeric, doIntApp] using run
          | val values =>
            obtain ⟨v, rfl⟩ := evaluateSing y env s1 values s2 hy
            cases v <;> simp [evaluate_int_pair, evaluate_intConst, hx, hy, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run ⊢
            all_goals simp_all [Int.mul_comm, Int.mul_left_comm]
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)

/-- Multiplication by negative one is source subtraction from zero. -/
theorem evaluate_mul_neg_one {C F : Type} (x : Bvl.Exp) (env : List Value) (state : State C F) :
    evaluateTuple ([.op (.intOp .mult) [x, .op (.intOp (.const (-1))) []]], env, state) =
    evaluateTuple ([.op (.intOp .sub) [x, .op (.intOp (.const 0)) []]], env, state) := by
  cases h : evaluateTuple ([x], env, state) with
  | mk xr s1 =>
    cases xr with
    | err error => simp [evaluate_intOp, evaluate_snoc_const, h]
    | val values =>
      obtain ⟨v, rfl⟩ := evaluateSing x env state values s1 h
      cases v <;> simp [evaluate_intOp, evaluate_snoc_const, h, Flapjack.holHd, doApp, applyNumeric, doIntApp]


/-- A generic multiplication by a right-hand constant preserves evaluation. -/
theorem smartOp2_mul_const_general {C F : Type} (x : Bvl.Exp) (n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult) [x, .op (.intOp (.const n)) []]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mult, x, .op (.intOp (.const n)) [])], env, state) = (result, final) := by
  cases hx : opConst x with
  | none =>
    cases hs : simple x with
    | none =>
      change evaluateTuple ([match opConst x with
        | some (.intOp .mult, a, m) => .op (.intOp .mult) [a, .op (.intOp (.const (n * m))) []]
        | some _ => .op (.intOp .mult) [x, .op (.intOp (.const n)) []]
        | none => match simple x with
          | some m => .op (.intOp (.const (n * m))) []
          | none => if n == 1 then x else if n == -1 then
              smartOp2 (.intOp .sub, x, .op (.intOp (.const 0)) [])
            else .op (.intOp .mult) [x, .op (.intOp (.const n)) []]], env, state) = _
      simp only [hx, hs]
      by_cases h1 : n = 1
      · simp only [h1, beq_self_eq_true, ↓reduceIte]
        exact evaluate_mul_one x env state final result (by simpa [h1] using run) notTypeError
      · simp only [h1, beq_iff_eq, ↓reduceIte]
        by_cases hn : n = -1
        · simp only [hn, ↓reduceIte]
          change evaluateTuple ([match opConst x with
            | some (.intOp .add, a, m) => .op (.intOp .sub) [a, .op (.intOp (.const (0 - m))) []]
            | some (.intOp .sub, a, m) => if 0 - m == 0 then a else .op (.intOp .add) [a, .op (.intOp (.const (0 - m))) []]
            | some _ => .op (.intOp .sub) [x, .op (.intOp (.const 0)) []]
            | none => match simple x with
              | some m => .op (.intOp (.const (0 - m))) []
              | none => .op (.intOp .sub) [x, .op (.intOp (.const 0)) []]], env, state) = _
          simp only [hx, hs]
          exact (evaluate_mul_neg_one x env state).symm.trans (by simpa [hn] using run)
        · simpa [hn] using run
    | some m =>
      have ex := (simple_eq x m).1 hs
      subst x
      exact smartOp2_mul_constants_correct m n env state final result run notTypeError
  | some v =>
    obtain ⟨op, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
    subst x
    cases op <;> try (exact run)
    case intOp operation =>
      cases operation <;> try (exact run)
      case mult => exact smartOp2_mul_nestedMul_correct a m n env state final result run notTypeError


namespace BothMulCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end BothMulCarrier

/-- Multiplication of two nested products preserves the source evaluation order. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_mul_mul_mul_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult)
      [.op (.intOp .mult) [x, .op (.intOp (.const m)) []],
       .op (.intOp .mult) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mult,
      .op (.intOp .mult) [x, .op (.intOp (.const m)) []],
      .op (.intOp .mult) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  change evaluateTuple ([.op (.intOp .mult) [.op (.intOp (.const (n * m))) [],
    .op (.intOp .mult) [x, y]]], env, state) = _
  exact evaluate_mul_mul_mul x y m n env state final result run notTypeError

/-- Expose the non-constant right operand branch of the executed rewrite. -/
theorem smartOp2_mul_nonconstant_eq (x y : Bvl.Exp) (hy : simple y = none) :
    smartOp2 (.intOp .mult, x, y) =
      match opConst x, opConst y with
      | some (.intOp .mult, a, m), some (.intOp .mult, b, n) =>
          .op (.intOp .mult) [.op (.intOp (.const (n * m))) [], .op (.intOp .mult) [a, b]]
      | _, _ => .op (.intOp .mult) [x, y] := by
  change ((match simple y with
    | some n => match opConst x with
      | some (.intOp .mult, a, m) => .op (.intOp .mult) [a, .op (.intOp (.const (n * m))) []]
      | some _ => .op (.intOp .mult) [x, y]
      | none => match simple x with
        | some m => .op (.intOp (.const (n * m))) []
        | none => if n == 1 then x else if n == -1 then
          smartOp2 (.intOp .sub, x, .op (.intOp (.const 0)) []) else .op (.intOp .mult) [x, y]
    | none => match opConst x, opConst y with
      | some (.intOp .mult, a, m), some (.intOp .mult, b, n) =>
          .op (.intOp .mult) [.op (.intOp (.const (n * m))) [], .op (.intOp .mult) [a, b]]
      | _, _ => .op (.intOp .mult) [x, y]) : Bvl.Exp) = _
  simp only [hy]

/-- The multiplication case of the binary source rewrite. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_mul_correct {C F : Type} (x y : Bvl.Exp)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .mult) [x, y]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .mult, x, y)], env, state) = (result, final) := by
  cases hy : simple y with
  | some n =>
    have ey := (simple_eq y n).1 hy
    subst y
    exact smartOp2_mul_const_general x n env state final result run notTypeError
  | none =>
    rw [smartOp2_mul_nonconstant_eq x y hy]
    cases hx : opConst x with
    | none => simpa [hx] using run
    | some v =>
      cases hz : opConst y with
      | none => simpa [hx, hz] using run
      | some w =>
        obtain ⟨ox, a, m, rfl, ex⟩ := (opConst_eq x v).1 hx
        obtain ⟨oy, b, n, rfl, ey⟩ := (opConst_eq y w).1 hz
        subst x
        subst y
        cases ox <;> try (exact run)
        case intOp opx =>
          cases opx <;> try (exact run)
          case mult =>
            cases oy <;> try (exact run)
            case intOp opy =>
              cases opy <;> try (exact run)
              case mult =>
                have h := smartOp2_mul_mul_mul_correct a b m n env state final result run notTypeError
                exact h

end Flapjack.Compiler.Backend.BvlConst.Proofs
