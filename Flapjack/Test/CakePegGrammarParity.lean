import Flapjack.CakeParser.PegEval

/-! Replay successful trees from the pinned HOL PEG machine. The direct
interpreter intentionally does not expose the HOL machine's diagnostic value. -/
namespace Flapjack.Test.CakePegGrammarParity
open Flapjack.CakeParser Flapjack.CakeParser.PegEval
open Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

private def location : Locs := .locs (.posn 0 1) (.posn 0 4)
private def token : Token := .alphaT (ofString "abc")

#guard match eval 100 (.nt (.inl .nV) .id) [(token, location)] with
  | .success trees rest => trees == [.node (.inl .nV) location [.leaf (.inr token) location]] && rest.isEmpty
  | _ => false

#guard match eval 100 (.nt (.inl .nTopLevelDecs) .id) [] with
  | .success trees rest => trees == [.node (.inl .nTopLevelDecs) unknownLoc []] && rest.isEmpty
  | _ => false

end Flapjack.Test.CakePegGrammarParity
