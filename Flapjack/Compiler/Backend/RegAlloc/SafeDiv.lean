import Flapjack.HolRef

namespace Flapjack.RegAlloc

/-- Guarded natural-number division used by the original spill-cost scan.
All natural numerators and denominators are retained, including zero. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "safe_div_def"]
def safeDiv (x v : Nat) : Nat := if v = 0 then 0 else x / v

end Flapjack.RegAlloc
