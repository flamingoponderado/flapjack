import Flapjack.Compiler.Backend.StackNames
import Flapjack.Pancake.Semantics.CrepSem.HOLState

namespace Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- HOL fixed-register renaming constraints. Only x86_64 constrains these
three names; all other ISAs satisfy the predicate without additional premises.
The canonical finite map is projected to the existing lookup/default helper. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "fixed_names_def"
  (fmap_as_finite_support_relation := [names]) (words_as_type_indexed_bitvec)]
def fixedNames {width : Nat} [NeZero width]
    (names : Flapjack.HolFiniteMapExact Nat Nat) (config : AsmConfigExact width) : Prop :=
  if config.isa = .x86_64 then
    StackNames.findName names.lookup 3 = 2 ∧
    StackNames.findName names.lookup 4 = 1 ∧
    StackNames.findName names.lookup 0 = 0
  else True

end Flapjack.Compiler.Backend.StackProps
