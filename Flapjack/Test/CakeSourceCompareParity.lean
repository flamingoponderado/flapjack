module

public import Flapjack.SemanticPrimitivesHOL.Compare

-- Checks below run compiled code from these modules.
public meta import Flapjack.AstHOL
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.SemanticPrimitivesHOL.Compare
@[expose] public section

/-! Source numeric and string-comparison observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceCompareParity
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

#guard numCmp .gt 9 4
#guard intCmp .lt (-3) 1
#guard !strCmp false .lt (ofString "z") (ofString "aa")
#guard strCmp true .lt (ofString "z") (ofString "aa")
#guard strCmp true .lt (ofString "az") (ofString "ba")
#guard strCmp false .gt (.implode [255]) (.implode [128])
#guard strCmp false .leq (ofString "x") (ofString "x")
#guard strCmp true .geq (ofString "x") (ofString "x")

end Flapjack.Test.CakeSourceCompareParity
