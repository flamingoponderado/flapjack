import Flapjack.Word
import Flapjack.Pancake.WordLang

/-!
# Executable/exact Word expression codec for Loop-to-Word

The executable `WordExp` and exact `WordLangExpHOL` expression carriers share
their expression constructors, but the production carrier parameterizes
`WordStore` by a phantom word type. This module maps that field explicitly and
provides width-specialized conversion in both directions. It is a carrier
bridge only; it does not route production compilation through `compExpHOL`.
-/

namespace Flapjack

/-- Convert the phantom-parameterized executable store names to the exact HOL
store carrier. The only payload-bearing constructor, `temp`, has the same
fixed five-bit address in both carriers. -/
def wordStoreToHOL {α : Type u} : WordStore α → WordStoreHOL
  | .temp address => .temp address
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .currHeap => .currHeap
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd

/-- Convert exact HOL store names back to the executable phantom-parameterized
carrier. -/
def wordStoreFromHOL {α : Type u} : WordStoreHOL → WordStore α
  | .temp address => .temp address
  | .nextFree => .nextFree
  | .endOfHeap => .endOfHeap
  | .triggerGC => .triggerGC
  | .currHeap => .currHeap
  | .heapLength => .heapLength
  | .progStart => .progStart
  | .bitmapBase => .bitmapBase
  | .otherHeap => .otherHeap
  | .allocSize => .allocSize
  | .globals => .globals
  | .globReal => .globReal
  | .handler => .handler
  | .genStart => .genStart
  | .codeBuffer => .codeBuffer
  | .codeBufferEnd => .codeBufferEnd
  | .bitmapBuffer => .bitmapBuffer
  | .bitmapBufferEnd => .bitmapBufferEnd

@[simp] theorem wordStoreToHOL_fromHOL {α : Type u} (store : WordStoreHOL) :
    wordStoreToHOL (wordStoreFromHOL (α := α) store) = store := by
  cases store <;> rfl

@[simp] theorem wordStoreFromHOL_toHOL {α : Type u} (store : WordStore α) :
    wordStoreFromHOL (α := α) (wordStoreToHOL store) = store := by
  cases store <;> rfl

/-- The executed expression carrier specialized to the machine word width and
the exact HOL `wordLang$exp` carrier. -/
def wordExpToHOL {width : Nat} :
    WordExp (BitVec width) → WordLangExpHOL (BitVec width)
  | .const value => .const value
  | .var name => .var name
  | .lookup store => .lookup (wordStoreToHOL store)
  | .load address => .load (wordExpToHOL address)
  | .op operator arguments => .op operator (arguments.map wordExpToHOL)
  | .shift operator left right => .shift operator
      (wordExpToHOL left) (wordExpToHOL right)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first
    | exact sizeOf_list_dec _ _
    | decreasing_trivial

/-- Exact HOL `wordLang$exp` decoded to the executed expression carrier at the
same fixed width. -/
def wordExpFromHOL {width : Nat} :
    WordLangExpHOL (BitVec width) → WordExp (BitVec width)
  | .const value => .const value
  | .var name => .var name
  | .lookup store => .lookup (wordStoreFromHOL store)
  | .load address => .load (wordExpFromHOL address)
  | .op operator arguments => .op operator (arguments.map wordExpFromHOL)
  | .shift operator left right => .shift operator
      (wordExpFromHOL left) (wordExpFromHOL right)
termination_by expression => sizeOf expression
decreasing_by
  all_goals first
    | exact sizeOf_list_dec _ _
    | decreasing_trivial

theorem wordExpToHOL_fromHOL {width : Nat}
    (expression : WordLangExpHOL (BitVec width)) :
    wordExpToHOL (wordExpFromHOL expression) = expression := by
  refine WordLangExpHOL.rec
    (motive_1 := fun expression =>
      wordExpToHOL (wordExpFromHOL expression) = expression)
    (motive_2 := fun expressions =>
      (expressions.map wordExpFromHOL).map wordExpToHOL = expressions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp [wordExpToHOL, wordExpFromHOL]
  · intro name
    simp [wordExpToHOL, wordExpFromHOL]
  · intro store
    simp [wordExpToHOL, wordExpFromHOL]
  · intro address ih
    simp [wordExpToHOL, wordExpFromHOL, ih]
  · intro operator arguments ih
    simpa [wordExpToHOL, wordExpFromHOL] using ih
  · intro operator left right ihLeft ihRight
    simp [wordExpToHOL, wordExpFromHOL, ihLeft, ihRight]
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

theorem wordExpFromHOL_toHOL {width : Nat}
    (expression : WordExp (BitVec width)) :
    wordExpFromHOL (wordExpToHOL expression) = expression := by
  refine WordExp.rec
    (motive_1 := fun expression =>
      wordExpFromHOL (wordExpToHOL expression) = expression)
    (motive_2 := fun expressions =>
      (expressions.map wordExpToHOL).map wordExpFromHOL = expressions)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ expression
  · intro value
    simp [wordExpToHOL, wordExpFromHOL]
  · intro name
    simp [wordExpToHOL, wordExpFromHOL]
  · intro store
    simp [wordExpToHOL, wordExpFromHOL]
  · intro address ih
    simp [wordExpToHOL, wordExpFromHOL, ih]
  · intro operator arguments ih
    simpa [wordExpToHOL, wordExpFromHOL] using ih
  · intro operator left right ihLeft ihRight
    simp [wordExpToHOL, wordExpFromHOL, ihLeft, ihRight]
  · rfl
  · intro head tail ihHead ihTail
    simp [ihHead, ihTail]

end Flapjack
