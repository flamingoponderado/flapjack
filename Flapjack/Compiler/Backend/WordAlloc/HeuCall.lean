import Flapjack.Misc.Sptree.Map

namespace Flapjack.WordAlloc

/-- Literal union of the two source call-name trees, retaining raw structure. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "heu_merge_call_def"]
def heuMergeCall (left right : NumSet) : NumSet :=
  sptUnion left right

/-- Literal approximation of new call names by mapping every tracked payload
to unit, then unioning that tree with the existing calls. The source payload
type remains arbitrary, and payload-only map preserves raw internal nodes.
No well-formedness premise is added. Executed allocator routing remains open. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "add_call_def"]
def addCall {α : Type} (tracked : Spt α) (calls : NumSet) : NumSet :=
  sptUnion (sptMap (fun _ => ()) tracked) calls

end Flapjack.WordAlloc
