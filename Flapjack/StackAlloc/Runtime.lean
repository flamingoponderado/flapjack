import Flapjack.StackAlloc

/-!
# StackAlloc runtime code

This file ports the non-generational (`Simple`) branch of
`cakeml/compiler/backend/stack_allocScript.sml`.  CakeML's StackLang
instruction set has immediate arithmetic instructions, while Flapjack's
small StackLang carrier currently exposes register-register arithmetic and
`const` separately.  The helpers below materialize an immediate in the
reserved scratch register before applying the corresponding operation.

The resulting program is executable StackLang syntax.  The state-level
simulation of heap copying and bitmap forwarding is deliberately a separate
proof layer, because it requires the full StackLang heap/stack semantics and
the collector invariants from `stack_allocProofScript.sml`.
-/

namespace Flapjack

structure StackGcConfig where
  shiftLength : Nat := 11
  smallShiftLength : Nat := 9
  lenSize : Nat := 32
  wordShift : Nat := 3
  wordBits : Nat := 64
  bytesInWord : Nat := 8
  immediateScratch : Nat := 31
  deriving Repr

end Flapjack
