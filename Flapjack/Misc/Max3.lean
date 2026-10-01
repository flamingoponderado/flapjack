import Flapjack.HolRef

namespace Flapjack

@[hol "cakeml/misc/miscScript.sml" "max3_def"]
def max3HOL (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x)
  else (if z > y then z else y)

end Flapjack
