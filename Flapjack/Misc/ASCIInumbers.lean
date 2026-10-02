import Flapjack.Misc.Numposrep
import Flapjack.Basis.Pure.MlString

/-! Counterpart of pinned HOL ASCIInumbersScript character formatting. -/
namespace Flapjack
open Basis.Pure.MlString

/-- Complete original digit-to-character conversion, including invalid digits. -/
@[hol "HOL/src/string/ASCIInumbersScript.sml" "HEX"]
def holHex (n : Nat) : HolChar :=
  if n < 10 then BitVec.ofNat 8 (48 + n)
  else if n < 16 then BitVec.ofNat 8 (65 + (n - 10))
  else BitVec.ofNat 8 0

/-- Complete original arbitrary-base character conversion. -/
@[hol "HOL/src/string/ASCIInumbersScript.sml" "n2s_def"]
def holN2s (b : Nat) (f : Nat → HolChar) (n : Nat) : List HolChar :=
  ((holN2l b n).map f).reverse

/-- Original decimal wrapper retains the zero numeral's single digit. -/
@[hol "HOL/src/string/ASCIInumbersScript.sml" "num_to_dec_string_def"]
def holNumToDecString : Nat → List HolChar := holN2s 10 holHex

end Flapjack
