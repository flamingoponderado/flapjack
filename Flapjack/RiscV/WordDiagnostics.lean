module

public import Flapjack.RiscV.WordToStack

@[expose] public section

/-!
# Checked Word-to-Stack diagnostics

The stateless Word-to-Stack API intentionally returns `none` for allocator-
owned `Alloc` and `StoreConsts` nodes because those nodes require the
state-threaded bitmap entrypoint.  This module preserves that API and adds a
checked boundary which identifies the unsupported constructor and its path in
the Word program.
-/

namespace Flapjack.RiscV

inductive WordUnsupportedFeature where
  | alloc
  | storeConsts
  | loweringFailure
  deriving DecidableEq, Repr

end Flapjack.RiscV
