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
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def pancakeBackendConf (c : Backend.Backend.Config) : Backend.Backend.Config :=
  { c with dataConf := { c.dataConf with gcKind := .none } }

end Flapjack.Compiler
