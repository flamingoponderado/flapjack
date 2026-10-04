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

/-- Both cutset domains retain every stack-variable predicate through the
actual list/tree normalization. This is codec infrastructure, not a HOL port. -/
theorem everyNameHOL_normalizeCutsets (predicate : Nat → Bool) (sets : WordLangCutsetsHOL) :
    everyNameHOL predicate (wordCutsetsToHOL (wordCutsetsFromHOL sets)) =
      everyNameHOL predicate sets := by
  simp only [everyNameHOL, wordCutsetsToHOL, wordCutsetsFromHOL,
    allNames_toNumSet_fromNumSet]

/-- The codec preserves the complete native stack-cutset predicate, including
both returning Call bodies and all nested loops. -/
theorem everyStackVarHOL_normalizeCutsets {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (program : WordLangProgHOL (BitVec width)) :
    everyStackVarHOL predicate (wordLangProgNormalizeCutsets program) =
      everyStackVarHOL predicate program := by
  fun_induction wordLangProgNormalizeCutsets program <;>
    first | rfl | (try simp_all [everyStackVarHOL, everyNameHOL_normalizeCutsets])
  case case9 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [everyStackVarHOL, everyNameHOL_normalizeCutsets]


/-- Native argument ABI checks are unchanged by cutset normalization. -/
theorem callArgConventionHOL_normalizeCutsets {width : Nat}
    (program : WordLangProgHOL (BitVec width)) :
    callArgConventionHOL (wordLangProgNormalizeCutsets program) = callArgConventionHOL program := by
  fun_induction wordLangProgNormalizeCutsets program <;>
    first | rfl | (try simp_all [callArgConventionHOL])
  case case9 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [callArgConventionHOL]


/-- Full native pre-allocation conventions survive actual codec normalization;
this states predicate preservation rather than unjustified Spt tree equality. -/
theorem preAllocConventionsHOL_normalizeCutsets {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) :
    preAllocConventionsHOL (wordLangProgNormalizeCutsets program) = preAllocConventionsHOL program := by
  simp only [preAllocConventionsHOL, everyStackVarHOL_normalizeCutsets,
    callArgConventionHOL_normalizeCutsets]

/-- Flat-expression conventions are preserved for every native program,
including the complete returning Call and exception-handler subtrees. -/
theorem flatExpConventions_normalizeCutsets {width : Nat}
    (program : WordLangProgHOL (BitVec width)) :
    flatExpConventions (wordLangProgNormalizeCutsets program) = flatExpConventions program := by
  fun_induction wordLangProgNormalizeCutsets program <;>
    first | rfl | (try simp_all [flatExpConventions])
  case case9 returns target arguments handler ihReturns ihHandler =>
    rcases returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handler with _ | ⟨exception, handlerBody, h1, h2⟩ <;>
      simp_all [flatExpConventions]


end Flapjack
