import Flapjack.SemanticPrimitivesHOL.Control

/-! Source literal type checks and fixed-width shifts. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.Basis.Pure.MlString

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "check_type_def"]
def checkType : PrimType → Value → Bool
  | .boolT, .conv (some (.typeStamp name 0)) [] => name == ofString "True" || name == ofString "False"
  | .intT, .litv (.intLit _) => true
  | .charT, .litv (.char _) => true
  | .strT, .litv (.strLit _) => true
  | .wordT .w8, .litv (.word8 _) => true
  | .wordT .w64, .litv (.word64 _) => true
  | .float64T, .litv (.float64 _) => true
  | _, _ => false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "dest_Litv_def"]
def destLitv : Value → Option Lit
  | .litv lit => some lit
  | _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "shift8_lookup_def"]
def shift8Lookup (shift : Shift) (value : BitVec 8) (amount : Nat) : BitVec 8 :=
  match shift with
  | .lsl => value <<< amount
  | .lsr => value >>> amount
  | .asr => value.sshiftRight amount
  | .ror => value.rotateRight amount

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "shift64_lookup_def"]
def shift64Lookup (shift : Shift) (value : BitVec 64) (amount : Nat) : BitVec 64 :=
  match shift with
  | .lsl => value <<< amount
  | .lsr => value >>> amount
  | .asr => value.sshiftRight amount
  | .ror => value.rotateRight amount

end Flapjack.SemanticPrimitivesHOL
