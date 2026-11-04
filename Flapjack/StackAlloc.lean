import Flapjack.Stack

/-!
# StackLang allocation insertion

This module ports the structural part of CakeML's `stack_alloc` pass.  The
pass replaces heap `Alloc` and stub-backed `StoreConsts` operations with calls
to runtime labels and recursively transforms all structured children,
including return continuations and exception handlers.

The generated call carries CakeML's `(Skip, 0, n, m)` return metadata.  The
full copying collector body is intentionally kept behind the explicit
`stackAllocStub` boundary for the next increment; this module therefore makes
the runtime dependency visible instead of silently dropping heap allocation.
-/

namespace Flapjack

structure StackAllocConfig where
  gcStubLocation : Nat := 0
  returnLabel : Nat := 0
  firstFreshLabel : Nat := 2
  deriving Repr

end Flapjack
