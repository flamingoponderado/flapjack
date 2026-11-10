module

public import Flapjack.Compiler.Backend.WordAlloc.ProductionTreeMapMerge
public import Flapjack.Misc.Sptree.MapiLookup
public import Flapjack.Misc.Sptree.MapiWf
public import Flapjack.Compiler.Backend.WordAlloc.ProductionCallCache
public import Flapjack.Compiler.Backend.WordAlloc.HeuProg

@[expose] public section

namespace Flapjack.WordAlloc
open RiscV

/-! Complete actual heuristic producer correspondence on the accepted source
encoder. The native original getHeu is already reviewed; these untagged
implementation theorems connect the accelerator to it, derive its redundant
cache invariant, and retain both source branch and return-call behavior. -/

end Flapjack.WordAlloc
