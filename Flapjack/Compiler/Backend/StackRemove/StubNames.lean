import Flapjack.Compiler.Backend.StackRemove.InitStubs
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Basis.Pure.MlString

/-- Original initializer symbol table, using the exact HOL character bytes
and native mlstring carrier. Artifact formatting is a separate production route. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "stub_names_def"]
def stubNames (_ : Unit) : List (Nat × MlString) :=
  [(0, .implode [95, 73, 110, 105, 116]),
   (1, .implode [95, 72, 97, 108, 116, 48]),
   (2, .implode [95, 72, 97, 108, 116, 50])]

/-- Full original initialization stub count for the actual native initializer,
with arbitrary positive word width and all original initializer parameters. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem checkInitStubsLength {width : Nat} [NeZero width] (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    (@initStubs width _ generateGc maximumHeap pointer start :
      List (Nat × Flapjack.Compiler.Backend.StackLang.HolProg width)).length + 2 =
      Flapjack.stackNumStubs := by
  simp [initStubs, Flapjack.stackNumStubs]

end Flapjack.Compiler.Backend.StackRemove
