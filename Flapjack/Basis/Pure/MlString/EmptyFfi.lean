module

public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-! mlstringScript.sml: `empty_ffi_def`, the logging no-op whose calls the
translator turns into empty-name FFI calls. -/
namespace Flapjack.Basis.Pure.MlString

/-- Exact HOL `mlstring$empty_ffi_def`: `empty_ffi (s:mlstring) = ()`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "empty_ffi_def"]
def emptyFfi (_s : MlString) : Unit := ()

end Flapjack.Basis.Pure.MlString
