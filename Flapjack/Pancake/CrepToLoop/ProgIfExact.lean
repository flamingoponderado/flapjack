import Flapjack.Pancake.CrepToLoop
import Flapjack.Misc.Sptree

/-!
Exact `crep_to_loop$prog_if` over the faithful `HolLoopProg` and `HolLoopExp`
carriers. The production helper in CrepToLoop.lean stays untagged because its
program FFI names are String-backed rather than HOL `mlstring`.
-/

namespace Flapjack

/-- HOL `crep_to_loop$prog_if` (`crep_to_loopScript.sml:34`) over the exact
    loopLang syntax, type-indexed word, and SPT-backed `num_set` carriers. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "prog_if_def"
  (words_as_type_indexed_bitvec)]
def progIfExact {width : Nat} [NeZero width]
    (operator : Cmp) (first second : List (HolLoopProg width))
    (left right : HolLoopExp width) (condition rightRegister : Nat)
    (live : NumSet) : List (HolLoopProg width) :=
  first ++ second ++
    [.assign condition left,
     .assign rightRegister right,
     .ite operator condition (.reg rightRegister)
       (.assign condition (.const (1 : BitVec width)))
       (.assign condition (.const (0 : BitVec width)))
       (sptListInsert [condition, rightRegister] live)]

end Flapjack
