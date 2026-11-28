module

public import Flapjack.Basis.Pure.MlString

@[expose] public section

/-!
# Hexadecimal digits and hexadecimal strings

Counterparts of `num_to_hex_digit_def`
(`cakeml/compiler/backend/jsonLangScript.sml`), `num_to_hex_def` and
`num_to_hex_mlstring_def` (`cakeml/compiler/backend/presLangScript.sml`) over
the reviewed `HolChar = BitVec 8` (HOL `char`) and `MlString = implode string`
carriers.
-/

namespace Flapjack.Compiler.Backend.PresLang.Hex

open Flapjack.Basis.Pure.MlString

/-- Original `num_to_hex_digit_def`: one hexadecimal digit as a character
list, empty outside the sixteen digit values. -/
@[hol "cakeml/compiler/backend/jsonLangScript.sml" "num_to_hex_digit_def"]
def numToHexDigit (n : Nat) : List HolChar :=
  if n < 10 then [BitVec.ofNat 8 (48 + n)]
  else if n < 16 then [BitVec.ofNat 8 (55 + n)]
  else []

/-- Original `num_to_hex_def`: the hexadecimal digits of a number, least
significant last, as a character list. -/
@[hol "cakeml/compiler/backend/presLangScript.sml" "num_to_hex_def"]
def numToHex (n : Nat) : List HolChar :=
  (if n < 16 then [] else numToHex (n / 16)) ++ numToHexDigit (n % 16)
termination_by n
decreasing_by
  omega

/-- Original `num_to_hex_mlstring_def`: the `0x`-prefixed hexadecimal string. -/
@[hol "cakeml/compiler/backend/presLangScript.sml" "num_to_hex_mlstring_def"]
def numToHexMlstring (n : Nat) : MlString :=
  .implode ([BitVec.ofNat 8 48, BitVec.ofNat 8 120] ++ numToHex n)

end Flapjack.Compiler.Backend.PresLang.Hex
