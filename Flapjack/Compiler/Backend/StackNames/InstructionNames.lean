import Flapjack.Compiler.Backend.StackNames.OperandNames

namespace Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Encoders.Asm

@[hol "cakeml/compiler/backend/stack_namesScript.sml" "inst_find_name_def"
  (words_as_type_indexed_bitvec)]
def instFindNameHOL {width : Nat} [NeZero width] (names : Flapjack.Spt Nat) :
    HolInst width → HolInst width
  | .skip => .skip
  | .const destination value => .const (findNameSpt names destination) value
  | .arith (.binop operator destination source right) =>
      .arith (.binop operator (findNameSpt names destination) (findNameSpt names source) (riFindNameHOL names right))
  | .arith (.shift operator destination source right) =>
      .arith (.shift operator (findNameSpt names destination) (findNameSpt names source) (riFindNameHOL names right))
  | .arith (.div r1 r2 r3) =>
      .arith (.div (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3))
  | .arith (.addCarry r1 r2 r3 r4) =>
      .arith (.addCarry (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3) (findNameSpt names r4))
  | .arith (.addOverflow r1 r2 r3 r4) =>
      .arith (.addOverflow (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3) (findNameSpt names r4))
  | .arith (.subOverflow r1 r2 r3 r4) =>
      .arith (.subOverflow (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3) (findNameSpt names r4))
  | .arith (.longMul r1 r2 r3 r4) =>
      .arith (.longMul (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3) (findNameSpt names r4))
  | .arith (.longDiv r1 r2 r3 r4 r5) =>
      .arith (.longDiv (findNameSpt names r1) (findNameSpt names r2) (findNameSpt names r3) (findNameSpt names r4) (findNameSpt names r5))
  | .mem operator register (.addr base offset) =>
      .mem operator (findNameSpt names register) (.addr (findNameSpt names base) offset)
  | .fp (.fpLess r f1 f2) => .fp (.fpLess (findNameSpt names r) f1 f2)
  | .fp (.fpLessEqual r f1 f2) => .fp (.fpLessEqual (findNameSpt names r) f1 f2)
  | .fp (.fpEqual r f1 f2) => .fp (.fpEqual (findNameSpt names r) f1 f2)
  | .fp (.fpMovToReg r1 r2 d) => .fp (.fpMovToReg (findNameSpt names r1) (findNameSpt names r2) d)
  | .fp (.fpMovFromReg d r1 r2) => .fp (.fpMovFromReg d (findNameSpt names r1) (findNameSpt names r2))
  | instruction => instruction

/-- Flapjack codec correspondence to the existing lookup-based instruction helper.
No target equality is assumed. Full production naming migration remains open. -/
theorem instFindNameHOL_toWord {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (instruction : HolInst width) :
    HolInst.toWordLangInst (instFindNameHOL names instruction) =
      instFindName (fun key => Flapjack.sptLookup key names) (HolInst.toWordLangInst instruction) := by
  cases instruction with
  | skip => rfl
  | const destination value =>
      simp only [instFindNameHOL, instFindName, HolInst.toWordLangInst, findNameSpt_eq_lookupHelper]
  | arith operation =>
      cases operation <;>
        simp only [instFindNameHOL, instFindName, HolInst.toWordLangInst,
          HolArith.toWordLangArith, findNameSpt_eq_lookupHelper, riFindNameHOL_toWord]
  | mem operator destination address =>
      cases address
      simp only [instFindNameHOL, instFindName, HolInst.toWordLangInst,
        HolAddr.toWordLangAddr, findNameSpt_eq_lookupHelper]
  | fp operation =>
      cases operation <;>
        simp only [instFindNameHOL, instFindName, HolInst.toWordLangInst, findNameSpt_eq_lookupHelper]

end Flapjack.Compiler.Backend.StackNames
