import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.HolRef
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Remove temporary-stack keys by the original right fold, preserving the
second component verbatim. Arbitrary trees and repeated keys are allowed. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "remove_temp_stack_def"]
def removeTempStack {α β : Type} (keys : List Nat) (trees : Spt α × β) :
    Spt α × β :=
  (keys.foldr sptDelete trees.1, trees.2)

/-- Literal stack-only move analysis. Its lookup and convention branches use
actual sparse trees; no well-formedness or distinctness assumption is added. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "merge_stack_only_def"]
def mergeStackOnly (move : Nat × Nat) (trees : Spt Unit × Spt Unit) :
    Spt Unit × Spt Unit :=
  let (x, y) := move
  let (temporary, fixed) := trees
  if sptLookup x temporary = some () then
    let temporary := if isAllocVar y then sptInsert y () temporary else temporary
    let fixed := if isPhyVar y then fixed else sptInsert x () fixed
    (temporary, fixed)
  else if isStackVar x then
    let temporary := if isAllocVar y then sptInsert y () temporary else temporary
    (temporary, fixed)
  else
    (sptDelete y temporary, fixed)

end Flapjack.WordAlloc
