import Flapjack.Word
import Flapjack.Pancake.WordLang

/-!
# Executable/exact Word expression codec for Loop-to-Word

The executable `WordExp` and exact `WordLangExpHOL` expression carriers share
their expression constructors, but the production carrier parameterizes
`WordStore` by a phantom word type. This module maps that field explicitly and
provides polymorphic conversion in both directions, including machine-word
specializations. It is a carrier
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

/-- Convert the executed expression carrier to the constructor-matching HOL
carrier. The codec is generic infrastructure; exact ports specialize to words. -/
def wordExpToHOL {α : Type u} :
    WordExp α → WordLangExpHOL α
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

/-- Decode the constructor-matching HOL expression carrier to execution,
retaining constant values and the fixed five-bit store-name payload. -/
def wordExpFromHOL {α : Type u} :
    WordLangExpHOL α → WordExp α
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

theorem wordExpToHOL_fromHOL {α : Type u}
    (expression : WordLangExpHOL α) :
    wordExpToHOL (wordExpFromHOL expression) = expression := by
  fun_induction wordExpFromHOL expression with
  | case5 _ arguments ih =>
      simp only [wordExpToHOL, List.map_map]
      congr 1
      exact (List.map_congr_left (g := id) ih).trans (List.map_id _)
  | _ => simp_all [wordExpToHOL]

theorem wordExpFromHOL_toHOL {α : Type u}
    (expression : WordExp α) :
    wordExpFromHOL (wordExpToHOL expression) = expression := by
  fun_induction wordExpToHOL expression with
  | case5 _ arguments ih =>
      simp only [wordExpFromHOL, List.map_map]
      congr 1
      exact (List.map_congr_left (g := id) ih).trans (List.map_id _)
  | _ => simp_all [wordExpFromHOL]

end Flapjack
