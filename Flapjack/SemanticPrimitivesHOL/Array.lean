import Flapjack.SemanticPrimitivesHOL

/-! Source array-copy and byte/character conversions. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.Basis.Pure.MlString

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "copy_array_def"]
def copyArray {α : Type} (source : List α × Int) (length : Int)
    (destination : Option (List α × Int)) : Option (List α) :=
  let (src, offset) := source
  if offset < 0 ∨ length < 0 ∨ src.length < (offset + length).natAbs then none
  else
    let copied := (src.drop offset.natAbs).take length.natAbs
    match destination with
    | none => some copied
    | some (dst, dstOffset) =>
      if dstOffset < 0 ∨ dst.length < (dstOffset + length).natAbs then none
      else some (dst.take dstOffset.natAbs ++ copied ++ dst.drop (dstOffset + length).natAbs)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "ws_to_chars_def"]
def wordsToChars (words : List (BitVec 8)) : List HolChar := words

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "chars_to_ws_def"]
def charsToWords (chars : List HolChar) : List (BitVec 8) := chars

end Flapjack.SemanticPrimitivesHOL
