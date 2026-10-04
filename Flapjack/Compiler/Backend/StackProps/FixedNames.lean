import Flapjack.Compiler.Backend.StackNames
import Flapjack.Pancake.Semantics.CrepSem.HOLState

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- HOL fixed-register renaming constraints. Only x86_64 constrains these
three names; all other ISAs satisfy the predicate without additional premises.
The exact sparse tree is projected to the existing lookup/default helper. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def fixedNames {width : Nat} [NeZero width]
    (names : Flapjack.Spt Nat) (config : AsmConfigExact width) : Prop :=
  if config.isa = .x86_64 then
    StackNames.findName (fun key => Flapjack.sptLookup key names) 3 = 2 ∧
    StackNames.findName (fun key => Flapjack.sptLookup key names) 4 = 1 ∧
    StackNames.findName (fun key => Flapjack.sptLookup key names) 0 = 0
  else True

end Flapjack.Compiler.Backend.StackProps
