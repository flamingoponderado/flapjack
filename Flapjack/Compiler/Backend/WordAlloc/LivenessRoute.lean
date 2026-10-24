import Flapjack.Compiler.Backend.WordAlloc.Expressions
import Flapjack.Pancake.LoopToWord.WordExpCarrierCodec

namespace Flapjack.WordAlloc

/-- Constant payloads are unobserved by expression liveness. Erase them into
a positive one-bit carrier so the generic production expression can call the
reviewed word-valued definition. All constructors and variable occurrences
are retained, including both Shift operands. This is Flapjack infrastructure,
not a HOL datatype or evaluator port. -/
def expressionForLiveness {α : Type u} : WordExp α → WordLangExpHOL (BitVec 1)
  | .const _ => .const 0
  | .var name => .var name
  | .lookup store => .lookup (wordStoreToHOL store)
  | .load address => .load (expressionForLiveness address)
  | .op operator arguments => .op operator (arguments.map expressionForLiveness)
  | .shift operator left right =>
      .shift operator (expressionForLiveness left) (expressionForLiveness right)
termination_by expression => sizeOf expression
decreasing_by all_goals decreasing_trivial

/-- Exact set-valued liveness for the generic executable carrier. This calls
the reviewed definition directly; WordDeadCode consumes its canonical key
traversal at the Assign/Store/Set/ShareInst set boundaries. The constant-erasure theorem below justifies this representation
boundary, so this wrapper has no independent HOL original. -/
def getLiveExpExecutable {α : Type u} (expression : WordExp α) : Spt Unit :=
  getLiveExp (expressionForLiveness expression)

/-- Constant erasure preserves the complete numeric tree, not just membership.
For every positive word width this is the reviewed exact liveness result of
the original expression codec. Cross-carrier infrastructure without a HOL
original; no injectivity, evaluation, or output premise is assumed. -/
theorem getLiveExpExecutable_exact {width : Nat} [NeZero width]
    (expression : WordExp (BitVec width)) :
    getLiveExpExecutable expression = getLiveExp (wordExpToHOL expression) := by
  fun_induction expressionForLiveness expression with
  | case5 operator arguments ih =>
      simp only [getLiveExpExecutable, expressionForLiveness, wordExpToHOL, getLiveExp, List.map_map]
      congr 1
      exact List.map_congr_left ih
  | _ => simp_all [getLiveExpExecutable, expressionForLiveness, wordExpToHOL, getLiveExp]


/-- Canonical mixed-tree key traversal for set-valued expression liveness.
Raw occurrence collectors retain their separate duplicate-sensitive API. -/
def liveExpressionKeys {α : Type u} (expression : WordExp α) : List Nat :=
  (sptToAList (getLiveExpExecutable expression)).map Prod.fst

/-- The executed key boundary is exactly the reviewed HOL expression tree's
traversal, for every positive source word width. -/
theorem liveExpressionKeys_exact {width : Nat} [NeZero width]
    (expression : WordExp (BitVec width)) :
    liveExpressionKeys expression =
      (sptToAList (getLiveExp (wordExpToHOL expression))).map Prod.fst := by
  rw [liveExpressionKeys, getLiveExpExecutable_exact]

end Flapjack.WordAlloc
