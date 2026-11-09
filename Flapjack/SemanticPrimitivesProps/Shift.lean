module

public import Flapjack.SemanticPrimitivesHOL.Primitives

@[expose] public section

/-! Shift definitions shared by the flat semantics and semantic primitive proofs. -/
namespace Flapjack.SemanticPrimitivesProps
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "shift_lookup_def"
  (words_as_type_indexed_bitvec)]
def shiftLookup {width : Nat} [NeZero width] (shift : Shift)
    (value : BitVec width) (amount : Nat) : BitVec width :=
  match shift with
  | .lsl => value <<< amount
  | .lsr => value >>> amount
  | .asr => value.sshiftRight amount
  | .ror => value.rotateRight amount

@[hol "cakeml/semantics/proofs/semanticPrimitivesPropsScript.sml" "do_shift_def"]
def doShift (shift : Shift) (amount : Nat) : WordSize → Lit → Option Lit
  | .w8, .word8 word => some (.word8 (shiftLookup shift word amount))
  | .w64, .word64 word => some (.word64 (shiftLookup shift word amount))
  | _, _ => none

end Flapjack.SemanticPrimitivesProps
