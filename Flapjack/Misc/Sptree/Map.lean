import Flapjack.Misc.Sptree

namespace Flapjack

/-- Literal payload-only Spt map. Unlike indexed `mapi0`, this source operation
preserves every tree constructor, including malformed empty internal nodes.
Input and output payload types are independent and no well-formedness premise
is required. The executed allocator route remains a separate dependency. -/
@[hol "hol4/src/finite_maps/sptreeScript.sml" "map_def"]
def sptMap {α β : Type} (f : α → β) : Spt α → Spt β
  | .ln => .ln
  | .ls value => .ls (f value)
  | .bn left right => .bn (sptMap f left) (sptMap f right)
  | .bs left value right => .bs (sptMap f left) (f value) (sptMap f right)

end Flapjack
