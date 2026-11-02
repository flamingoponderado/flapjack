import Flapjack.Compiler.Backend.Semantics.DataSem.Stack
import Flapjack.HolRef

/-! Source value depth and ancestor chains for the equality resource bound. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem

mutual
/-- Depth of nested nonempty source blocks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_depth_def"]
def vDepth : Value → Nat
  | .block _ _ xs => (if xs = [] then 0 else 1) + vDepthMax xs
  | _ => 0
termination_by value => sizeOf value

/-- Maximum `vDepth` in a value list (Flapjack recursion helper). -/
def vDepthMax : List Value → Nat
  | [] => 0
  | x :: xs => max (vDepth x) (vDepthMax xs)
termination_by values => sizeOf values
end

mutual
/-- The proof-side depth agrees with the evaluator's depth on every value. -/
theorem vDepth_eq_valueDepth (value : Value) : vDepth value = valueDepth value := by
  cases value with
  | block stamp tag xs =>
    simpa [vDepth, valueDepth] using vDepthMax_eq_valuesDepth xs
  | number value => simp [vDepth, valueDepth]
  | word64 value => simp [vDepth, valueDepth]
  | codePtr value => simp [vDepth, valueDepth]
  | refPtr bit value => simp [vDepth, valueDepth]
termination_by sizeOf value

/-- The source maximum with its nonempty increment agrees with list depth. -/
theorem vDepthMax_eq_valuesDepth (values : List Value) :
    (if values = [] then 0 else 1) + vDepthMax values = valuesDepth values := by
  cases values with
  | nil => simp [vDepthMax, valuesDepth]
  | cons x xs =>
    cases xs with
    | nil => simp [vDepthMax, valuesDepth, vDepth_eq_valueDepth x]
    | cons y ys =>
      have head := vDepth_eq_valueDepth x
      have tail := vDepthMax_eq_valuesDepth (y :: ys)
      simp only [List.cons_ne_nil, ↓reduceIte] at tail ⊢
      rw [vDepthMax, valuesDepth, head, ← tail]
      omega
termination_by sizeOf values
end

/-- Each successive value is a block containing the preceding value. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "elements_list_def"]
def elementsList : List Value → Prop
  | [] => True
  | [_] => True
  | v :: w :: vs => ∃ stamp tag before after,
      w = .block stamp tag (before ++ [v] ++ after) ∧ elementsList (w :: vs)
termination_by values => values.length
decreasing_by simp_wf

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
