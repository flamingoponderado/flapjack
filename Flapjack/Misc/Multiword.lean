import Flapjack.HolRef

/-! Multiword integer encodings from the HOL multiword library. -/
namespace Flapjack.Misc.Multiword

/-- Natural number represented as little-endian word digits. The production
constant compiler uses it through `i2mw`. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "n2mw_def"
  (words_as_type_indexed_bitvec)]
def n2mw {width : Nat} [NeZero width] (n : Nat) : List (BitVec width) :=
  if n = 0 then [] else
    BitVec.ofNat width (n % 2 ^ width) :: n2mw (n / 2 ^ width)
termination_by n
decreasing_by
  apply Nat.div_lt_self (by omega)
  exact Nat.one_lt_two_pow (NeZero.ne width)

/-- Signed integer represented by its sign and magnitude words. The production
constant compiler uses this definition directly. -/
@[hol "HOL/examples/machine-code/multiword/multiwordScript.sml" "i2mw_def"
  (words_as_type_indexed_bitvec)]
def i2mw {width : Nat} [NeZero width] (i : Int) : Bool × List (BitVec width) :=
  (decide (i < 0), n2mw i.natAbs)

end Flapjack.Misc.Multiword
