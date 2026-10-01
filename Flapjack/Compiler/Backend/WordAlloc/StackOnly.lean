import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Remove temporary-stack keys by the original right fold, preserving the
second component verbatim. Arbitrary trees and repeated keys are allowed. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "remove_temp_stack_def"]
def removeTempStack {α β : Type} (keys : List Nat) (trees : Spt α × β) :
    Spt α × β :=
  (keys.foldr sptDelete trees.1, trees.2)

end Flapjack.WordAlloc
