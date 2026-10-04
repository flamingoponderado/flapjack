import Flapjack.Compiler.Backend.StackRemove.ProgComp
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Full original function-level equality: arbitrary section-name carrier,
all compiler parameters and native programs retained. No hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem progCompEta {width : Nat} [NeZero width] {Name : Type} :
    (progComp : Bool → (BitVec width × BitVec width) → Nat →
      (Name × HolProg width) → (Name × HolProg width)) =
    fun jump bounds pointer entry => (entry.1, comp jump bounds pointer entry.2) := rfl

end Flapjack.Compiler.Backend.StackRemove
