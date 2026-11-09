import Flapjack.Compiler.Backend.FlatLang
import Flapjack.AstHOL.GeneratedSize
import Flapjack.Compiler.Backend.BackendCommon.Trace.GeneratedSize
import Flapjack.Misc.GeneratedSize

namespace Flapjack.Compiler.Backend.FlatLang

/-- HOL's datatype-generated `flatLang$op_size`. The typed equations are
captured as `flat_op_size_def_typed` in `flat_elim_value_globals_probe.out`;
the function is needed to reproduce HOL's generated expression size. -/
def opSizeHOL : Op → Nat
  | .src op => 1 + AstHOL.opSizeHOL op
  | .globalVarAlloc n => 1 + n
  | .globalVarInit n => 1 + n
  | .globalVarLookup n => 1 + n
  | .tagLenEq a b => 1 + (a + b)
  | .lenEq n => 1 + n
  | .el n => 1 + n
  | .id => 0

mutual
/-- HOL's generated `pat_size`. Its complete typed equations are captured as
`flat_pat_size_def_typed` in `flat_elim_value_globals_probe.out`. -/
def patSizeHOL : Pat → Nat
  | .pany => 0
  | .pvar name => 1 + mlstringSizeHOL name
  | .plit lit => 1 + AstHOL.litSizeHOL lit
  | .pcon tag pats =>
      1 + (optionSizeHOL (pairSizeHOL id
        (optionSizeHOL (pairSizeHOL id (listSizeHOL (pairSizeHOL id id))))) tag +
        patListSizeHOL pats)
  | .pas pat name => 1 + (patSizeHOL pat + mlstringSizeHOL name)
  | .pref pat => 1 + patSizeHOL pat

/-- The list component `pat1_size` generated along with `pat_size`. -/
def patListSizeHOL : List Pat → Nat
  | [] => 0
  | pat :: pats => 1 + (patSizeHOL pat + patListSizeHOL pats)
end

end Flapjack.Compiler.Backend.FlatLang
