import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Pancake.WordConvs
import Flapjack.Misc.Sptree.ToAList

namespace Flapjack

/-! Production codec normalization preserves native input conventions.
The codec reconstructs unit Spt cutsets from their full key enumeration;
lookup semantics is preserved, but tree equality is not assumed. These
carrier lemmas have no separate HOL declaration. -/

private theorem allNames_toNumSet_fromNumSet (predicate : Nat → Bool) (tree : Spt Unit) :
    ((sptToAList (LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL tree))).map Prod.fst).all predicate =
      ((sptToAList tree).map Prod.fst).all predicate := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, sptMemMapFstToAList, sptDomain,
    toNumSet_fromNumSet_lookup]

end Flapjack
