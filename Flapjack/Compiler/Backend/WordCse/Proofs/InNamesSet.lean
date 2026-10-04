import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

/-- Original arithmetic fact self-mapping predicate. Every register read by
any of the eight arithmetic constructors must be present as its own canonical
representative; no flattening, successful run, or desired output is assumed. -/
-- riscv-mi: declaration over the reduced integer carrier.
def inNamesSet {width : Nat} [NeZero width] (operation : HolArith width)
    (canonical : Spt Nat) : Prop :=
  ∀ register ∈ arithReads operation, sptLookup register canonical = some register

end Flapjack.Compiler.Backend.WordCse
