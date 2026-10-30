import Flapjack.Compiler.Backend.BvlConst.Proofs.Arithmetic
/-! Two-operand arithmetic rewrite cases; evaluation helpers are Flapjack proof infrastructure. -/
namespace Flapjack.Compiler.Backend.BvlConst.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps

/-- Evaluate two expressions in source order, retaining errors and state. -/
theorem evaluate_pair {C F : Type} (x y : Bvl.Exp) (env : List Value) (s : State C F) :
    evaluateTuple ([x, y], env, s) =
      match evaluateTuple ([x], env, s) with
      | (.val values, next) =>
        match evaluateTuple ([y], env, next) with
        | (.val tail, last) => (.val (@Flapjack.holHd Value ⟨unitValue⟩ values :: tail), last)
        | other => other
      | other => other := evaluateCons x [y] env s

/-- Evaluate a binary integer operation after its operands in source order. -/
theorem evaluate_int_pair {C F : Type} (op : ClosLang.IntOp) (x y : Bvl.Exp) (env : List Value) (s : State C F) :
    evaluateTuple ([.op (.intOp op) [x, y]], env, s) =
      match evaluateTuple ([x], env, s) with
      | (.err error, next) => (.err error, next)
      | (.val xs, next) =>
        match evaluateTuple ([y], env, next) with
        | (.err error, final) => (.err error, final)
        | (.val ys, final) =>
          match doApp (.intOp op) ((@Flapjack.holHd Value ⟨unitValue⟩ xs) :: ys).reverse final with
          | .err error => (.err error, final)
          | .val (value, last) => (.val [value], last) := by
  rw [evaluate_intOp, evaluate_pair]
  cases h : evaluateTuple ([x], env, s) with
  | mk xr s1 =>
    cases xr with
    | err error => rfl
    | val values =>
      obtain ⟨v, rfl⟩ := evaluateSing x env s values s1 h
      cases h2 : evaluateTuple ([y], env, s1) with
      | mk yr s2 => cases yr <;> (simp [h2]; try rfl)

/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_add_add_add {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .add) [.op (.intOp .add) [x, y],
      .op (.intOp (.const (n + m))) []]], env, state) = (result, final) := by
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
            all_goals simp_all [Int.add_comm, Int.add_left_comm]
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)
/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_add_add_sub {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .sub) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .sub) [.op (.intOp .sub) [x, y],
      .op (.intOp (.const (n + m))) []]], env, state) = (result, final) := by
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
            all_goals try exact run
            all_goals constructor
            all_goals try exact run.2
            all_goals rw [← run.1]
            all_goals congr 3
            all_goals omega
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)

/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_add_sub_add {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .add) [.op (.intOp .sub) [x, y],
      .op (.intOp (.const (n + m))) []]], env, state) = (result, final) := by
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
            all_goals try exact run
            all_goals constructor
            all_goals try exact run.2
            all_goals rw [← run.1]
            all_goals congr 3
            all_goals omega
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)

/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_sub_add_add {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .add) [.op (.intOp .sub) [x, y],
      .op (.intOp (.const (n - m))) []]], env, state) = (result, final) := by
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
            all_goals try exact run
            all_goals constructor
            all_goals try exact run.2
            all_goals rw [← run.1]
            all_goals congr 3
            all_goals omega
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)

/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_sub_add_sub {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .sub) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .sub) [.op (.intOp .add) [x, y],
      .op (.intOp (.const (n - m))) []]], env, state) = (result, final) := by
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
            all_goals try exact run
            all_goals constructor
            all_goals try exact run.2
            all_goals rw [← run.1]
            all_goals congr 3
            all_goals omega
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)

/-- This Flapjack helper derives the corresponding arithmetic rearrangement from a non-type-error evaluation, including all state effects. -/
theorem evaluate_sub_sub_add {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([.op (.intOp .add) [.op (.intOp .add) [x, y],
      .op (.intOp (.const (n - m))) []]], env, state) = (result, final) := by
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
            all_goals try exact run
            all_goals constructor
            all_goals try exact run.2
            all_goals rw [← run.1]
            all_goals congr 3
            all_goals omega
      | _ =>
        simp [evaluate_int_pair, evaluate_intConst, hx, Flapjack.holHd, doApp, applyNumeric, doIntApp] at run
        exact False.elim (notTypeError run.1.symm)
namespace BothCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end BothCarrier

/-- Addition of two nested additions, retaining the original evaluation order. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_nestedAdd_nestedAdd_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp .add) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_add_add_add x y m n env state final result run notTypeError
  change evaluateTuple ([if n + m == 0 then .op (.intOp .add) [x, y] else
    .op (.intOp .add) [.op (.intOp .add) [x, y], .op (.intOp (.const (n + m))) []]], env, state) = _
  by_cases h : n + m = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    apply evaluate_add_zero (.op (.intOp .add) [x, y]) env state final result
    · simpa [h] using normalized
    · exact notTypeError
  · simpa [h] using normalized

/-- Two-operand arithmetic rewrite case, preserving evaluation order and effects. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_add_sub_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .sub) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp .sub) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_add_add_sub x y m n env state final result run notTypeError
  change evaluateTuple ([.op (.intOp .sub) [.op (.intOp .sub) [x, y],
    .op (.intOp (.const (n + m))) []]], env, state) = _
  exact normalized

/-- Two-operand arithmetic rewrite case, preserving evaluation order and effects. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_add_sub_add_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .add)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .add,
      .op (.intOp .sub) [x, .op (.intOp (.const m)) []],
      .op (.intOp .add) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_add_sub_add x y m n env state final result run notTypeError
  change evaluateTuple ([if n + m == 0 then .op (.intOp .sub) [x, y] else
    .op (.intOp .add) [.op (.intOp .sub) [x, y], .op (.intOp (.const (n + m))) []]], env, state) = _
  by_cases h : n + m = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    apply evaluate_add_zero (.op (.intOp .sub) [x, y]) env state final result
    · simpa [h] using normalized
    · exact notTypeError
  · simpa [h] using normalized

/-- Two-operand arithmetic rewrite case, preserving evaluation order and effects. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_add_add_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp .add) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_sub_add_add x y m n env state final result run notTypeError
  change evaluateTuple ([.op (.intOp .add) [.op (.intOp .sub) [x, y],
    .op (.intOp (.const (n - m))) []]], env, state) = _
  exact normalized

/-- Two-operand arithmetic rewrite case, preserving evaluation order and effects. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_add_sub_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .add) [x, .op (.intOp (.const m)) []],
       .op (.intOp .sub) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub,
      .op (.intOp .add) [x, .op (.intOp (.const m)) []],
      .op (.intOp .sub) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_sub_add_sub x y m n env state final result run notTypeError
  change evaluateTuple ([.op (.intOp .sub) [.op (.intOp .add) [x, y],
    .op (.intOp (.const (n - m))) []]], env, state) = _
  exact normalized

/-- Two-operand arithmetic rewrite case, preserving evaluation order and effects. -/
@[hol "cakeml/compiler/backend/proofs/bvl_constProofScript.sml" "SmartOp2_thm"
  (fmap_as_finite_support := [refs])]
theorem smartOp2_sub_sub_add_correct {C F : Type} (x y : Bvl.Exp) (m n : Int)
    (env : List Value) (state final : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List Value) Value)
    (run : evaluateTuple ([.op (.intOp .sub)
      [.op (.intOp .sub) [x, .op (.intOp (.const m)) []],
       .op (.intOp .add) [y, .op (.intOp (.const n)) []]]], env, state) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    evaluateTuple ([smartOp2 (.intOp .sub,
      .op (.intOp .sub) [x, .op (.intOp (.const m)) []],
      .op (.intOp .add) [y, .op (.intOp (.const n)) []])], env, state) = (result, final) := by
  have normalized := evaluate_sub_sub_add x y m n env state final result run notTypeError
  change evaluateTuple ([if n - m == 0 then .op (.intOp .add) [x, y] else
    .op (.intOp .add) [.op (.intOp .add) [x, y], .op (.intOp (.const (n - m))) []]], env, state) = _
  by_cases h : n - m = 0
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    apply evaluate_add_zero (.op (.intOp .add) [x, y]) env state final result
    · simpa [h] using normalized
    · exact notTypeError
  · simpa [h] using normalized

end Flapjack.Compiler.Backend.BvlConst.Proofs
