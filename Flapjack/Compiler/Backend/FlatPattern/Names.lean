import Flapjack.Compiler.Backend.FlatPattern.Config
import Flapjack.Compiler.Backend.FlatLang
import Flapjack.Basis.Pure.MlString

/-! Generated-name encoding used by CakeML's flat pattern compiler. -/

namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.Basis.Pure.MlString

/-- Sum the character offsets from position `i` to the end of the HOL string. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "sum_string_ords_def"]
def sumStringOrds (i : Nat) (str : MlString) : Nat :=
  ((str.explode.drop i).map (fun c => c.toNat - 35)).foldr (· + ·) 0

/-- Decode the reserved `..` name prefix; other names decode to zero. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "dec_name_to_num_def"]
def decNameToNum (name : MlString) : Nat :=
  match name.explode with
  | a :: b :: _ => if a = 46 && b = 46 then sumStringOrds 2 name else 0
  | _ => 0

/-- Encode a number into the original byte-string name representation. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "enc_num_to_name_aux_def"]
def encNumToNameAux (i : Nat) (xs : List HolChar) : List HolChar :=
  if i < 90 then 46 :: 46 :: BitVec.ofNat 8 (i + 35) :: xs
  else encNumToNameAux (i - 90) (125 :: xs)
termination_by i
decreasing_by omega

/-- Produce the `mlstring` used for a compiler-generated name. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "enc_num_to_name_def"]
def encNumToName (i : Nat) : MlString := .implode (encNumToNameAux i [])

/-- Largest generated-name index in a list of names. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "max_dec_name_def"]
def maxDecName : List MlString → Nat
  | [] => 0
  | name :: names => max (decNameToNum name) (maxDecName names)

/-- Only global initialization is classified as setting globals. -/
@[hol "cakeml/compiler/backend/flat_patternScript.sml" "op_sets_globals_def"]
def opSetsGlobals : FlatLang.Op → Bool
  | .globalVarInit _ => true
  | _ => false

end Flapjack.Compiler.Backend.FlatPattern
