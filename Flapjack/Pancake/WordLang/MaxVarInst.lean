import Flapjack.Pancake.WordLang
import Flapjack.Misc.Max3

namespace Flapjack

/-- Literal instruction maximum. Only integer registers count; the two
floating-point transfer clauses retain HOL's dimension-64 special case. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "max_var_inst_def"
  (words_as_type_indexed_bitvec)]
def maxVarInstHOL {width : Nat} [NeZero width] : WordLangInst (BitVec width) → Nat
  | .skip => 0
  | .const r _ => r
  | .arith (.binop _ a b (.reg c)) => max3HOL a b c
  | .arith (.binop _ a b (.imm _)) => max a b
  | .arith (.shift _ a b (.reg c)) => max3HOL a b c
  | .arith (.shift _ a b (.imm _)) => max a b
  | .arith (.div a b c) => max3HOL a b c
  | .arith (.addCarry a b c d) => max (max a b) (max c d)
  | .arith (.addOverflow a b c d) => max (max a b) (max c d)
  | .arith (.subOverflow a b c d) => max (max a b) (max c d)
  | .arith (.longMul a b c d) => max (max a b) (max c d)
  | .arith (.longDiv a b c d e) => max (max (max a b) (max c d)) e
  | .mem .load r (.addr a _) => max a r
  | .mem .store r (.addr a _) => max a r
  | .mem .load32 r (.addr a _) => max a r
  | .mem .store32 r (.addr a _) => max a r
  | .mem .load8 r (.addr a _) => max a r
  | .mem .store8 r (.addr a _) => max a r
  | .fp (.fpLess r _ _) => r
  | .fp (.fpLessEqual r _ _) => r
  | .fp (.fpEqual r _ _) => r
  | .fp (.fpMovToReg a b _) => if width = 64 then a else max a b
  | .fp (.fpMovFromReg _ a b) => if width = 64 then a else max a b
  | _ => 0

end Flapjack
