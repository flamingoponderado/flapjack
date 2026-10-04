import Flapjack.Pancake.Semantics.CrepProps.EveryExpHOL

namespace Flapjack

/-! Flapjack-specific representation infrastructure, with no separate HOL
original: the exact syntax decoder preserves every_exp traversal. -/
mutual
 theorem crepEveryExpHOL_codec {width : Nat} [NeZero width]
    (predicate : CrepExp (BitVec width) → Bool) (e : CrepExpHOL width) :
    crepEveryExpHOL (fun e => predicate (crepExpOfHOL e) = true) e ↔
      crepEveryExp predicate (crepExpOfHOL e) = true := by
  cases e with
  | const v => simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, iff_self]
  | var n => simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, iff_self]
  | loadGlob n => simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, iff_self]
  | baseAddr => simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, iff_self]
  | topAddr => simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, iff_self]
  | load e | load32 e | loadByte e =>
      simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, Bool.and_eq_true]
      exact and_congr Iff.rfl (crepEveryExpHOL_codec predicate e)
  | op op es | crepOp op es =>
      simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, Bool.and_eq_true]
      exact and_congr Iff.rfl (crepEveryExpListHOL_codec predicate es)
  | cmp op a b | shift op a b =>
      simp only [crepEveryExpHOL, crepExpOfHOL, crepEveryExp, Bool.and_eq_true]
      rw [crepEveryExpHOL_codec predicate a, crepEveryExpHOL_codec predicate b]
      exact and_assoc.symm
  termination_by sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

 theorem crepEveryExpListHOL_codec {width : Nat} [NeZero width]
    (predicate : CrepExp (BitVec width) → Bool) (es : List (CrepExpHOL width)) :
    crepEveryExpListHOL (fun e => predicate (crepExpOfHOL e) = true) es ↔
      crepEveryExpList predicate (es.map crepExpOfHOL) = true := by
  cases es with
  | nil => simp only [crepEveryExpListHOL, List.map_nil, crepEveryExpList, iff_self]
  | cons e es =>
      simp only [crepEveryExpListHOL, List.map_cons, crepEveryExpList, Bool.and_eq_true]
      rw [crepEveryExpHOL_codec predicate e, crepEveryExpListHOL_codec predicate es]
  termination_by sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

end Flapjack
