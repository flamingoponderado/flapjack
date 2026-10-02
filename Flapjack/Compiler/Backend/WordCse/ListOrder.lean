import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordCse

/-- Literal numeric lexicographic comparison. Lean Ordering is the direct
three-constructor translation of HOL comparison: Less/Equal/Greater. -/
@[hol "cakeml/compiler/backend/word_cseScript.sml" "listCmp_def"]
def listCmp : List Nat → List Nat → Ordering
  | a :: xs, b :: ys => if a = b then listCmp xs ys else if a > b then .gt else .lt
  | [], [] => .eq
  | _ :: _, [] => .gt
  | [], _ :: _ => .lt

end Flapjack.Compiler.Backend.WordCse
