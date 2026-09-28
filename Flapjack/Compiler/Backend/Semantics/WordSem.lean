import Flapjack.HolRef
import Flapjack.Pancake.WordLang

/-!
# `wordSem` helpers shared by the Loop semantics

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml` for the
declarations the exact loopSem evaluator needs.
-/

namespace Flapjack

/-- Exact HOL `wordSem$the_words_def` (`wordSemScript.sml:297-302`):

    ```
    the_words [] = SOME []
    the_words (w::ws) = case (w, the_words ws) of
                          | SOME (Word x), SOME xs => SOME (x::xs)
                          | _ => NONE
    ```

    over the exact `word_loc` carrier `WordLocW`, HOL `'a word` rendered as
    `BitVec width`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "the_words_def"
  (words_as_type_indexed_bitvec)]
def theWords {width : Nat} [NeZero width] :
    List (Option (WordLocW width)) → Option (List (BitVec width))
  | [] => some []
  | w :: ws =>
      match w, theWords ws with
      | some (.word x), some xs => some (x :: xs)
      | _, _ => none

end Flapjack
