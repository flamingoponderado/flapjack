import Flapjack.Compiler.Backend.FlatLang
import Flapjack.AstHOL.GeneratedSize
import Flapjack.Compiler.Backend.BackendCommon.Trace.GeneratedSize

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

end Flapjack.Compiler.Backend.FlatLang
