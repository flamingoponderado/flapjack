module

public import Flapjack.HolRef

@[expose] public section

namespace Flapjack.Compiler.Backend.BackendCommon

/-- The constructor tag used for tuples. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "tuple_tag_def"]
def tupleTag : Nat := 0

/-- The constructor tag used for ordinary closures. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "closure_tag_def"]
def closureTag : Nat := 30

/-- The constructor tag used for partial applications. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "partial_app_tag_def"]
def partialAppTag : Nat := 31

/-- Reserve the two closure tags when moving source constructor tags to BVL. -/
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "clos_tag_shift_def"]
def closTagShift (tag : Nat) : Nat := if tag < 30 then tag else tag + 2

end Flapjack.Compiler.Backend.BackendCommon
