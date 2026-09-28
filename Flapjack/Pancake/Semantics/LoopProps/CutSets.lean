import Flapjack.Pancake.Semantics.LoopProps

namespace Flapjack

/-- Exact HOL `loopProps$cut_sets_def` over the faithful `HolLoopProg` and
    `NumSet = Spt Unit` carriers. The clauses, including the nested insert
    order for long arithmetic and the identity fallback, follow
    `cakeml/pancake/semantics/loopPropsScript.sml:40-55`. The only carrier
    translation is HOL's positive word dimension to `BitVec width`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "cut_sets_def"
  (words_as_type_indexed_bitvec)]
def cutSetsHOL {width : Nat} [NeZero width] (live : NumSet) :
    HolLoopProg width → NumSet
  | .skip => live
  | .locValue destination _ => sptInsert destination () live
  | .assign destination _ => sptInsert destination () live
  | .load32 _ destination => sptInsert destination () live
  | .loadByte _ destination => sptInsert destination () live
  | .seq first second => cutSetsHOL (cutSetsHOL live first) second
  | .ite _ _ _ _ _ live' => live'
  | .arith (.longDiv left right _ _ _) =>
      sptInsert left () (sptInsert right () live)
  | .arith (.longMul left right _ _) =>
      sptInsert left () (sptInsert right () live)
  | .arith (.div destination _ _) => sptInsert destination () live
  | _ => live

end Flapjack
