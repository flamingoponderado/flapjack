import Flapjack.HolRef

namespace Flapjack.Compiler.Backend.BackendCommon

/-- Reserve the two closure tags when moving source constructor tags to BVL. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "clos_tag_shift_def"]
def closTagShift (tag : Nat) : Nat := if tag < 30 then tag else tag + 2

end Flapjack.Compiler.Backend.BackendCommon
