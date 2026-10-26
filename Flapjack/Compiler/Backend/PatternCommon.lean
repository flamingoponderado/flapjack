import Flapjack.HolRef

/-! Syntax shared by the CakeML pattern compiler and its semantics. -/
namespace Flapjack.Compiler.Backend.PatternCommon

/-- A path into a pattern-matching value. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_commonScript.sml" "position"]
inductive Position where
  | emptyPos
  | pos : Nat → Position → Position
  deriving DecidableEq, Repr

/-- Result of matching one pattern. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_commonScript.sml" "pmatchResult"]
inductive PmatchResult where
  | success | failure | typeFailure
  deriving DecidableEq, Repr

/-- Result of matching a sequence of branches. -/
@[hol "cakeml/compiler/backend/pattern_matching/pattern_commonScript.sml" "matchResult"]
inductive MatchResult where
  | success : Nat → MatchResult
  | failure
  deriving DecidableEq, Repr

end Flapjack.Compiler.Backend.PatternCommon
