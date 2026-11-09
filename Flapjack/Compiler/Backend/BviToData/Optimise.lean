module

public import Flapjack.Compiler.Backend.DataLive
public import Flapjack.Compiler.Backend.DataSimp
public import Flapjack.Compiler.Backend.DataSpace.Compile

@[expose] public section

/-! The data optimization sequence used by BVI-to-data lowering. -/
namespace Flapjack.Compiler.Backend.BviToData

/-- Apply liveness, sequence simplification and allocation-space movement. -/
@[hol "cakeml/compiler/backend/bvi_to_dataScript.sml" "optimise_def"]
def optimise (p : DataLang.Prog) : DataLang.Prog :=
  DataSpace.compile (DataSimp.simp (DataLive.compile p .ln).1 .skip)

end Flapjack.Compiler.Backend.BviToData
