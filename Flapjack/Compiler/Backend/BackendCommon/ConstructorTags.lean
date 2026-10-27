import Flapjack.HolRef

/-! Constructor tags used by source-to-flat and flat semantics. -/
namespace Flapjack.Compiler.Backend.BackendCommon

@[hol "cakeml/compiler/backend/backend_commonScript.sml" "bind_tag_def"]
def bindTag : Nat := 0
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "chr_tag_def"]
def chrTag : Nat := 1
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "div_tag_def"]
def divTag : Nat := 2
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "subscript_tag_def"]
def subscriptTag : Nat := 3
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "nil_tag_def"]
def nilTag : Nat := 0
@[hol "cakeml/compiler/backend/backend_commonScript.sml" "cons_tag_def"]
def consTag : Nat := 0

end Flapjack.Compiler.Backend.BackendCommon
