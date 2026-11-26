module

public import Flapjack.CakeParser.PtreeConversion.Exact

@[expose] public section

/-! The tuple-splitting conversion as an explicit case expression. -/
namespace Flapjack.CakeParser.PtreeConversion.Exact
open Flapjack.AstHOL

@[hol "cakeml/semantics/cmlPtreeConversionScript.sml" "detuplify_pmatch"]
theorem detuplify_pmatch (ty : AstT) :
    detuplify ty = (match ty with | .attup args => args | t => [t]) := by
  cases ty
  all_goals simp [detuplify]

end Flapjack.CakeParser.PtreeConversion.Exact
