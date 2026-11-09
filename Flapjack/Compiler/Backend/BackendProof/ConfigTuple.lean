module

public import Flapjack.Compiler.Backend.Backend
public import Flapjack.HolRef

@[expose] public section

/-! Configuration projections used by the backend compiler oracle. -/
namespace Flapjack.Compiler.Backend.BackendProof

/-- The backend configuration retained below the closure compiler. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "config_tuple2_def"]
def configTuple2 (c : Backend.Config) :=
  (c.bvlConf.inlines, c.bvlConf.nextName1, c.bvlConf.nextName2, c.bvlConf.nextName3,
    c.bvlConf.bviInlines, c.wordConf.bitmapsLength, c.labConf)

/-- The source and closure configurations paired with the lower backend state. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "config_tuple1_def"]
def configTuple1 (c : Backend.Config) :=
  (c.sourceConf, c.closConf.nextLoc, ClosKnown.optionValApproxSpt c.closConf.knownConf,
    c.closConf.callState.1, configTuple2 c)

end Flapjack.Compiler.Backend.BackendProof
