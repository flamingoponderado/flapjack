import Flapjack.Compiler.Backend.StackRemove.Comp

/-! Literal stack_removeScript.sml:224–226 section wrapper. HOL's section-name
carrier is independent beta, retained without specializing to numeric labels.
The default Pancake and assembly modes initializedRuntimeLab? executes these native
definitions through StackRemove.compileHOL. hex and sections modes retain the legacy
route; upstream StackAlloc replacement is a separate obligation.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Full original wrapper: preserve the arbitrary section name and compile
only its faithful native program. No successful-pass or safety premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def progComp {width : Nat} [NeZero width] {Name : Type} (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (entry : Name × HolProg width) :
    Name × HolProg width :=
  (entry.1, comp jump bounds pointer entry.2)

end Flapjack.Compiler.Backend.StackRemove
