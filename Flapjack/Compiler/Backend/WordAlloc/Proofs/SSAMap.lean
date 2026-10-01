import Flapjack.Misc.Sptree
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Native SSA map bound: every mapped register is nonphysical and below the
next register. The original places no well-formedness or injectivity condition
on the source tree. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_map_ok_def"]
def ssaMapOK (next : Nat) (ssa : Spt Nat) : Prop :=
  ∀ x y, sptLookup x ssa = some y → ¬ isPhyVar y ∧ y < next

end Flapjack.Compiler.Backend.WordAlloc
