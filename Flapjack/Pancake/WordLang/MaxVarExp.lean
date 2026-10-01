import Flapjack.Pancake.WordLang
import Flapjack.PanToCrepMaxList

namespace Flapjack

/-- Literal expression frame bound. The final HOL clause covers Const and
Lookup; their payloads do not contribute a register. Op uses the zero-based
natural MAX_LIST fold, including the empty argument list. Production wrapper
routing and the full program max_var assembly remain separate work. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "max_var_exp_def"
  (words_as_type_indexed_bitvec)]
def maxVarExpHOL {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Nat
  | .var register => register
  | .load address => maxVarExpHOL address
  | .op _ arguments => maxList (arguments.map maxVarExpHOL)
  | .shift _ left right => max (maxVarExpHOL left) (maxVarExpHOL right)
  | _ => 0
termination_by expression => sizeOf expression
decreasing_by
  all_goals first | sizeOf_list_dec | decreasing_trivial | simp_wf

end Flapjack
