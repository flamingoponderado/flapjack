import Flapjack.Misc.Location

/-! Source location merging for context-free parse trees. -/
namespace Flapjack.Misc.Location

@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_locs_def"]
def mergeLocs : Locs → Locs → Locs
  | .locs first _, .locs _ last => .locs first last

@[hol "HOL/examples/formal-languages/context-free/locationScript.sml" "merge_list_locs_def"]
def mergeListLocs : List Locs → Locs
  | [] => unknownLoc
  | [loc] => loc
  | [first, last] => mergeLocs first last
  | first :: _ :: rest => mergeListLocs (first :: rest)
termination_by locs => locs.length

end Flapjack.Misc.Location
