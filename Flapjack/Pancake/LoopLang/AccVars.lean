import Flapjack.Pancake.LoopLang

/-!
Exact `loopLang$acc_vars_def`.  This submodule is the declaration-level
counterpart of the `acc_vars` clause group in `loopLangScript.sml`; the
production list-backed accumulator remains in `LoopLive.lean` without a HOL tag.
-/

namespace Flapjack

/-- Exact HOL `acc_vars_def` (`cakeml/pancake/loopLangScript.sml:117-158`) over
its exact width-indexed program carrier.  HOL's polymorphic `'a prog` becomes
`HolLoopProg width` (the tag records the standard type-indexed-word
translation) and `num_set = unit spt` is the reviewed exact `NumSet = Spt Unit`
carrier.  All 24 `prog` constructors are matched clause-for-clause; the nested
`Seq`/`If`/`Call` accumulator order and the `insert`/`list_insert` helpers
(`sptInsert`, `sptListInsert`) reproduce the HOL right/left nesting. -/
@[hol "cakeml/pancake/loopLangScript.sml" "acc_vars_def"
  (words_as_type_indexed_bitvec)]
def accVarsHOL {width : Nat} [NeZero width] :
    HolLoopProg width → NumSet → NumSet
  | .seq p1 p2, l => accVarsHOL p1 (accVarsHOL p2 l)
  | .break _, l => l
  | .continue _, l => l
  | .loop _ body _, l => accVarsHOL body l
  | .ite _ _ _ p1 p2 _, l => accVarsHOL p1 (accVarsHOL p2 l)
  | .arith operation, l =>
      match operation with
      | .longMul v1 v2 _ _ => sptInsert v1 () (sptInsert v2 () l)
      | .longDiv v1 v2 _ _ _ => sptInsert v1 () (sptInsert v2 () l)
      | .div v1 _ _ => sptInsert v1 () l
  | .mark p1, l => accVarsHOL p1 l
  | .tick, l => l
  | .skip, l => l
  | .fail, l => l
  | .raise _, l => l
  | .return _, l => l
  | .call none _ _ _, l => l
  | .call (some (vs, _)) _ _ none, l => sptListInsert vs l
  | .call (some (vs, _)) _ _ (some (n, p1, p2, _)), l =>
      accVarsHOL p1 (accVarsHOL p2 (sptInsert n () (sptListInsert vs l)))
  | .locValue n _, l => sptInsert n () l
  | .assign n _, l => sptInsert n () l
  | .primitive lhss _ _, l => sptListInsert lhss l
  | .shMem _ n _, l => sptInsert n () l
  | .store _ _, l => l
  | .setGlobal _ _, l => l
  | .load32 _ m, l => sptInsert m () l
  | .loadByte _ m, l => sptInsert m () l
  | .store32 _ _, l => l
  | .storeByte _ _, l => l
  | .ffi _ _ _ _ _ _, l => l

end Flapjack
