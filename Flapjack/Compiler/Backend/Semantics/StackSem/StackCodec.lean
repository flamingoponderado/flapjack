import Flapjack.Compiler.Backend.Semantics.StackSem.Bitmap
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
import Flapjack.Pancake.WordLang

/-! Exact StackSem stack encoding/decoding prerequisites. Recursion decreases
stack length using the source's bitmap LENGTH theorems; there is no fuel cutoff.
Bitmap words and stack words retain independent positive dimensions, as in
the standalone HOL definitions. The existing Nat stack machine and full StackSem evaluator remain separate. -/
namespace Flapjack.StackSem

/-- HOL one-based bitmap descriptor; subtraction occurs in the word carrier. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "full_read_bitmap_def"
  (words_as_type_indexed_bitvec)]
def fullReadBitmap {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth)) : WordLocW width → Option (List Bool)
  | .word word => if word = 0 then none else readBitmap (bitmaps.drop (word - 1).toNat)
  | .loc _ _ => none

/-- HOL stack encoding with exactly one terminal zero sentinel. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "enc_stack_def"
  (words_as_type_indexed_bitvec)]
def encStack {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth))
    (stack : List (WordLocW width)) : Option (List (WordLocW width)) :=
  match stack with
  | [] => none
  | header :: tail =>
      if header = .word 0 then
        if tail = [] then some [] else none
      else
        match fullReadBitmap bitmaps header with
        | none => none
        | some bits =>
            match _hfilter : filterBitmap bits tail with
            | none => none
            | some (selected, remainder) =>
                match encStack bitmaps remainder with
                | none => none
                | some roots => some (selected ++ roots)
termination_by stack.length
decreasing_by
  have hb := filterBitmapLength bits tail selected remainder _hfilter
  simp only [List.length_cons]
  omega

/-- HOL stack decoding, preserving headers and unselected values, and consuming
all roots at the final singleton zero sentinel. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "dec_stack_def"
  (words_as_type_indexed_bitvec)]
def decStack {bitmapWidth : Nat} {width : Nat} [NeZero bitmapWidth] [NeZero width]
    (bitmaps : List (BitVec bitmapWidth))
    (roots stack : List (WordLocW width)) : Option (List (WordLocW width)) :=
  match stack with
  | [] => none
  | header :: tail =>
      if header = .word 0 then
        if roots = [] ∧ tail = [] then some [.word 0] else none
      else
        match fullReadBitmap bitmaps header with
        | none => none
        | some bits =>
            match _hmap : mapBitmap bits roots tail with
            | none => none
            | some (front, remainingRoots, remainder) =>
                match decStack bitmaps remainingRoots remainder with
                | none => none
                | some rest => some ([header] ++ front ++ rest)
termination_by stack.length
decreasing_by
  have hb := (mapBitmapLength bits roots tail front remainingRoots remainder _hmap).2
  simp only [List.length_cons]
  omega

end Flapjack.StackSem
