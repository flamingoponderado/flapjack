module

public import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
public import Aesop

@[expose] public section

/-! BVL integer primitives. -/
namespace Flapjack.Compiler.Backend.BvlSem

/-- Original integer operations, with floor division and remainder and the
source's bounded small-constant comparison. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_int_app_def"]
def doIntApp : ClosLang.IntOp → List Value → Option Value
  | .const n, [] => some (.number n)
  | .add, [.number a, .number b] => some (.number (a + b))
  | .sub, [.number a, .number b] => some (.number (a - b))
  | .mult, [.number a, .number b] => some (.number (a * b))
  | .div, [.number a, .number b] => if b = 0 then none else some (.number (a.fdiv b))
  | .mod, [.number a, .number b] => if b = 0 then none else some (.number (a.fmod b))
  | .less, [.number a, .number b] => some (boolValue (decide (a < b)))
  | .lessEq, [.number a, .number b] => some (boolValue (decide (a ≤ b)))
  | .greater, [.number a, .number b] => some (boolValue (decide (a > b)))
  | .greaterEq, [.number a, .number b] => some (boolValue (decide (a ≥ b)))
  | .lessConstSmall n, [.number i] =>
    if 0 ≤ i ∧ i ≤ 1000000 ∧ n < 1000000 then
      some (boolValue (decide (i < Int.ofNat n))) else none
  | _, _ => none

/-- Every successful original integer operation fixes both the argument list
and the result, in the source's conjunct order. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_int_app_eq_some"]
theorem doIntApp_eq_some (vs : List Value) (res : Value) :
    (∀ n, doIntApp (.const n) vs = some res → vs = [] ∧ res = .number n) ∧
    (doIntApp .add vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧ res = .number (n1 + n2)) ∧
    (doIntApp .sub vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧ res = .number (n1 - n2)) ∧
    (doIntApp .mult vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧ res = .number (n1 * n2)) ∧
    (doIntApp .div vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧ n2 ≠ 0 ∧
        res = .number (n1.fdiv n2)) ∧
    (doIntApp .mod vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧ n2 ≠ 0 ∧
        res = .number (n1.fmod n2)) ∧
    (doIntApp .less vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧
        res = boolValue (decide (n1 < n2))) ∧
    (doIntApp .lessEq vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧
        res = boolValue (decide (n1 ≤ n2))) ∧
    (doIntApp .greater vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧
        res = boolValue (decide (n1 > n2))) ∧
    (doIntApp .greaterEq vs = some res →
      ∃ n1 n2, vs = [.number n1, .number n2] ∧
        res = boolValue (decide (n1 ≥ n2))) ∧
    (∀ n, doIntApp (.lessConstSmall n) vs = some res →
      ∃ i, vs = [.number i] ∧ 0 ≤ i ∧ i ≤ 1000000 ∧ n < 1000000 ∧
        res = boolValue (decide (i < Int.ofNat n))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all
    all_goals aesop
  · intro n h
    simp only [doIntApp] at h
    repeat' split at h
    all_goals simp_all

end Flapjack.Compiler.Backend.BvlSem
