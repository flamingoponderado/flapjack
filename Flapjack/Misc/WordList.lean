import Flapjack.Misc.SetSep
import Flapjack.Compiler.Backend.StackRemove

/-! Heap-list predicates from miscScript.sml, distinct from the bitmap-word
chunking helper in WordToStack. Address words and payload types are independent;
address arithmetic is modular and assertions retain full set separation.
-/

namespace Flapjack.Misc

/-- Complete forward heap-list assertion: the current address is used for the
singleton, then increased by the source bytes_in_word for the recursive tail. -/
@[hol "cakeml/misc/miscScript.sml" "word_list_def" (words_as_type_indexed_bitvec)]
def wordList {width : Nat} [NeZero width] {β : Type} (address : BitVec width) :
    List β → ((BitVec width × β) → Prop) → Prop
  | [] => Flapjack.SetSep.emp
  | value :: values =>
      Flapjack.SetSep.star (Flapjack.SetSep.one (address, value))
        (wordList (address + Flapjack.Compiler.Backend.StackRemove.bytesInWord width) values)

/-- Original existential list assertion with its exact pure length condition.
No concrete list, successful representation or list-length premise replaces the
existential; cond retains its empty-heap requirement inside STAR. -/
@[hol "cakeml/misc/miscScript.sml" "word_list_exists_def" (words_as_type_indexed_bitvec)]
def wordListExists {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (length : Nat) : ((BitVec width × β) → Prop) → Prop :=
  Flapjack.SetSep.sepExists (fun values : List β =>
    Flapjack.SetSep.star (wordList address values)
      (Flapjack.SetSep.cond (values.length = length)))

end Flapjack.Misc
