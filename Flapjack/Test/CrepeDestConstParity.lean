import Flapjack.Pancake.Proofs.CrepArith

namespace Flapjack.Test.CrepeDestConstParity

/-! Direct parity for `crep_arith$dest_const_def`
    (`crep_arithScript.sml:10-12`), observed in
    `scripts/hol-probes/crep_arith_dest_const_probe.out`. -/
example (width : Nat) [NeZero width] : (List.finRange width).length = width :=
  List.length_finRange

example : (List.finRange 8).length = 8 := rfl

/-! Exact HOL-carrier parity for the tagged width-indexed definition/theorem.
    The constructor/value shape is `CrepExpHOL`/`BitVec`, as in
    `crepLang$exp`'s word-valued `Const`. -/
example (value : BitVec 8) :
    crepDestConstHOL (.const value : CrepExpHOL 8) = some value := rfl

-- The word_carrier_bool row is a HOL type identity. Under the reviewed
-- words_as_type_indexed_bitvec representation it has no separate Lean coercion.
-- The non-constant rows from crep_arith_dest_const_probe.out.
example : crepDestConstHOL (.var 2 : CrepExpHOL 8) = none := rfl
example : crepDestConstHOL (.load (.const 3) : CrepExpHOL 8) = none := rfl
example : crepDestConstHOL (.crepOp .mul [.const 2, .const 4] : CrepExpHOL 8) = none := rfl

example (expression : CrepExpHOL 8) (value : BitVec 8)
    (h : crepDestConstHOL expression = some value) :
    expression = .const value :=
  crepDestConstHOL_eq_const expression value h

end Flapjack.Test.CrepeDestConstParity
