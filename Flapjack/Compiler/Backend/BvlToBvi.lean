import Flapjack.Compiler.Backend.BackendCommon
import Flapjack.HolRef

/-! Counterpart of `cakeml/compiler/backend/bvl_to_bviScript.sml`. Only the
stub-location constants are ported so far; the language carriers and the
compiler remain open. -/

namespace Flapjack.Compiler.Backend.BvlToBvi

/-- HOL `AllocGlobal_location_def`: `AllocGlobal_location = data_num_stubs`. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "AllocGlobal_location_def"]
def allocGlobalLocation : Nat := dataNumStubs

/-- HOL `CopyGlobals_location_def`: `CopyGlobals_location = AllocGlobal_location + 1`. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "CopyGlobals_location_def"]
def copyGlobalsLocation : Nat := allocGlobalLocation + 1

/-- HOL `InitGlobals_location_def`: `InitGlobals_location = CopyGlobals_location + 1`. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "InitGlobals_location_def"]
def initGlobalsLocation : Nat := copyGlobalsLocation + 1

end Flapjack.Compiler.Backend.BvlToBvi
