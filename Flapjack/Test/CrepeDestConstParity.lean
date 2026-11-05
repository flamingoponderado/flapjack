import Flapjack.Pancake.Proofs.CrepArith

namespace Flapjack.Test.CrepeDestConstParity

/-! Direct parity for `crep_arith$dest_const_def`
    (`crep_arithScript.sml:10-12`), observed in
    `scripts/hol-probes/crep_arith_dest_const_probe.out`. -/
def word8 (value : Nat) : RiscV.Word 8 := BitVec.ofNat 8 value

def parityGuard : Bool :=
  (match crepDestConst (.const (word8 7) : CrepExp (RiscV.Word 8)) with
  | some value => value == word8 7
  | _ => false) &&
  (match crepDestConst (.var 2 : CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false) &&
  (match crepDestConst (.load (.const (word8 3)) : CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false) &&
  (match crepDestConst
      (.crepOp .mul [.const (word8 2), .const (word8 4)] :
        CrepExp (RiscV.Word 8)) with
  | none => true
  | _ => false)

#eval parityGuard
#guard parityGuard

example (value : Fin 4 → Bool) :
    crepDestConstHolWord (.const value) = some value := rfl

example (width : Nat) [NeZero width] : (List.finRange width).length = width :=
  List.length_finRange

example : (List.finRange 8).length = 8 := rfl

/-! Exact HOL-carrier parity for the tagged width-indexed definition/theorem.
    The constructor/value shape is `CrepExpHOL`/`BitVec`, as in
    `crepLang$exp`'s word-valued `Const`. -/
example (value : BitVec 8) :
    crepDestConstHOL (.const value : CrepExpHOL 8) = some value := rfl

example (expression : CrepExpHOL 8) (value : BitVec 8)
    (h : crepDestConstHOL expression = some value) :
    expression = .const value :=
  crepDestConstHOL_eq_const expression value h

end Flapjack.Test.CrepeDestConstParity
