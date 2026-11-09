module

public import Flapjack.SemanticPrimitivesHOL
public import Flapjack.HolRef

@[expose] public section

/-! Mapping successful pattern-match results. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.SemanticPrimitivesHOL

/-- Apply a function to successful bindings, preserving the two failures. -/
@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "map_match_def"]
def mapMatch {α : Type} (f : α → α) : MatchResult α → MatchResult α
  | .match value => .match (f value)
  | .noMatch => .noMatch
  | .typeError => .typeError

end Flapjack.SemanticPrimitivesProps
