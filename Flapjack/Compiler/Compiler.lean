import Flapjack.Compiler.Backend.Backend
import Flapjack.HolRef

/-!
# `compilerScript.sml`

Declarations of the top-level CakeML compiler driver used by the Pancake route.
-/

namespace Flapjack.Compiler

/-- HOL `pancake_backend_conf_def` (`compilerScript.sml:744-747`): the backend configuration
used to compile Pancake, which is the given one with the data configuration's `gc_kind`
set to `None`. -/
@[hol "cakeml/compiler/compilerScript.sml" "pancake_backend_conf_def"]
def pancakeBackendConf (c : Backend.Backend.Config) : Backend.Backend.Config :=
  { c with dataConf := { c.dataConf with gcKind := .none } }

end Flapjack.Compiler
