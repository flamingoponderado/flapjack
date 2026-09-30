import Flapjack.Pancake.WordLang
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Shared constructor recursion for exact and executed expression colouring.
This polymorphic implementation is Flapjack infrastructure; `applyColourExp`
below retains HOL's word-valued signature. -/
def applyColourExpCore {α : Type u} (f : Nat → Nat) :
    WordLangExpHOL α → WordLangExpHOL α
  | .var n => .var (f n)
  | .load e => .load (applyColourExpCore f e)
  | .op op es => .op op (es.map (applyColourExpCore f))
  | .shift sh e n => .shift sh (applyColourExpCore f e) (applyColourExpCore f n)
  | .const v => .const v
  | .lookup name => .lookup name
termination_by e => sizeOf e
decreasing_by all_goals decreasing_trivial

/-- Exact HOL expression renaming over the faithful word-valued carrier.
The executed allocator uses this same constructor recursion through the
roundtrip expression codecs. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_colour_exp_def"
  (words_as_type_indexed_bitvec)]
def applyColourExp {width : Nat} [NeZero width] (f : Nat → Nat) :
    WordLangExpHOL (BitVec width) → WordLangExpHOL (BitVec width) :=
  applyColourExpCore f

/-- HOL big_union uses a right fold and the exact left-biased Spt union. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "big_union_def"]
def bigUnion (sets : List (Spt Unit)) : Spt Unit :=
  sets.foldr sptUnion .ln

/-- Exact HOL get_live_exp, including both expression-valued Shift operands. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_live_exp_def"
  (words_as_type_indexed_bitvec)]
def getLiveExp {width : Nat} [NeZero width] : WordLangExpHOL (BitVec width) → Spt Unit
  | .var n => sptInsert n () .ln
  | .load e => getLiveExp e
  | .op _ es => bigUnion (es.map getLiveExp)
  | .shift _ e n => sptUnion (getLiveExp e) (getLiveExp n)
  | .const _ => .ln
  | .lookup _ => .ln
termination_by e => sizeOf e
decreasing_by all_goals decreasing_trivial

end Flapjack.WordAlloc
