import Flapjack.Compiler.Backend.ClosKnown.Proofs.SizeCorrect

/-! The source short-circuit size traversal and its full-size specification. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang

mutual

private theorem getSizeScAux_correct (n : Nat) (es : List Exp) :
    getSizeScAuxHOL n es = n - getSizeAuxHOL es := by
  cases es with
  | nil => simp [getSizeScAuxHOL, getSizeAuxHOL]
  | cons e es =>
    cases es with
    | nil =>
      simp [getSizeScAuxHOL, getSizeAuxHOL, getSizeScExp_correct n e]
    | cons next rest =>
      simp only [getSizeScAuxHOL, getSizeAuxHOL]
      rw [getSizeScExp_correct n e, getSizeScAux_correct _ (next :: rest)]
      simp only [getSizeAuxHOL]
      (repeat' split) <;> omega
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega

private theorem getSizeScExp_correct (n : Nat) (e : Exp) :
    getSizeScExpHOL n e = n - getSizeExpHOL e := by
  cases e with
  | var => simp [getSizeScExpHOL, getSizeExpHOL]
  | tick trace e =>
    rw [getSizeScExpHOL, getSizeExpHOL]
    exact getSizeScExp_correct n e
  | ifThenElse trace x y z =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScExp_correct _ x, getSizeScExp_correct _ y, getSizeScExp_correct _ z]
    (repeat' split) <;> omega
  | «let» trace xs body =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScAux_correct _ xs, getSizeScExp_correct _ body]
    (repeat' split) <;> omega
  | raise trace e | fn trace loc vars arity e =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScExp_correct _ e]
    (repeat' split) <;> omega
  | handle trace x y =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScExp_correct _ x, getSizeScExp_correct _ y]
    (repeat' split) <;> omega
  | op trace op xs | call trace ticks op xs =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScAux_correct _ xs]
    (repeat' split) <;> omega
  | letrec names loc vars fs body =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScFuns_correct _ fs, getSizeScExp_correct _ body]
    (repeat' split) <;> omega
  | app trace loc e xs =>
    simp only [getSizeScExpHOL, getSizeExpHOL]
    rw [getSizeScExp_correct _ e, getSizeScAux_correct _ xs]
    (repeat' split) <;> omega
termination_by sizeOf e
decreasing_by all_goals simp_wf <;> omega

private theorem getSizeScFuns_correct (n : Nat) (fs : List (Nat × Exp)) :
    getSizeScFunsHOL n fs = n - getSizeFunsHOL fs := by
  cases fs with
  | nil => simp [getSizeScFunsHOL, getSizeFunsHOL]
  | cons f fs =>
    cases f with
    | mk arity e =>
      simp only [getSizeScFunsHOL, getSizeFunsHOL]
      rw [getSizeScExp_correct n e, getSizeScFuns_correct _ fs]
      (repeat' split) <;> omega
termination_by sizeOf fs
decreasing_by all_goals simp_wf <;> omega

end

/-- Short-circuit size traversal subtracts the full expression-list size.
The unused polymorphic argument is retained from HOL's inferred statement. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_aux_correct"]
theorem getSizeScAuxCorrect {A : Type} (es : List Exp) (limit : Nat) (_unused : A) :
    getSizeScAuxHOL limit es = limit - getSizeAuxHOL es :=
  getSizeScAux_correct limit es

/-- A successful short-circuit size result equals the full source size. -/
@[hol "cakeml/compiler/backend/clos_knownScript.sml" "get_size_sc_SOME"]
theorem getSizeScSome (e : Exp) (limit n : Nat) (h : getSizeScHOL limit e = some n) :
    getSizeHOL e = n := by
  unfold getSizeScHOL at h
  rw [getSizeScAux_correct] at h
  simp only [getSizeHOL] at *
  split at h <;> simp_all <;> omega

/-- The source short-circuit test returns the full size exactly when it fits. -/
theorem getSizeSc_eq (limit : Nat) (e : Exp) :
    getSizeScHOL limit e = if getSizeHOL e ≤ limit then some (getSizeHOL e) else none := by
  unfold getSizeScHOL
  rw [getSizeScAux_correct]
  change (if limit + 1 - getSizeHOL e = 0 then none else
    some (limit + 1 - (limit + 1 - getSizeHOL e))) = _
  by_cases bound : getSizeHOL e ≤ limit
  · have positive : limit + 1 - getSizeHOL e ≠ 0 := by omega
    simp only [ite_eq_right positive, ite_eq_left bound, Option.some.injEq]
    omega
  · have zero : limit + 1 - getSizeHOL e = 0 := by omega
    simp [zero, bound]

end Flapjack.Compiler.Backend.ClosKnown
