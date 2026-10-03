import Flapjack.Compiler.Backend.RegAlloc.ProductionInitAlloc
import Flapjack.Compiler.Backend.RegAlloc.MovePrep

namespace Flapjack.RegAlloc
open RiscV.CakeRegAlloc Translator.Monadic.MonadBase

/-- Complete actual/native move-admission transport, including equal and
out-of-domain endpoints. Original validity supplies every guarded read. This
is Flapjack infrastructure without an independent HOL original. -/
theorem fullConsistencyOk_production (limit left right : Nat) {native : State}
    {production : CakeRaState} (related : ProductionStateRel native production)
    (good : goodRaState native) :
    fullConsistencyOk limit left right native =
      (.success (cakeFullConsistencyOk production limit left right), native) := by
  by_cases equal : left = right
  · simp [fullConsistencyOk, equal, ret, cakeFullConsistencyOk]
  · have different : (left != right) = true := bne_iff_ne.mpr equal
    by_cases outside : left ≥ native.dim ∨ right ≥ native.dim
    · simp only [fullConsistencyOk, if_neg equal, Translator.Monadic.MonadBase.bind, getDim, ret, if_pos outside]
      rcases outside with leftOutside | rightOutside
      · simp [cakeFullConsistencyOk, related.dimension, Nat.not_lt.mpr leftOutside]
      · simp [cakeFullConsistencyOk, related.dimension, Nat.not_lt.mpr rightOutside]
    · have leftBound : left < native.dim := by omega
      have rightBound : right < native.dim := by omega
      have adjacencyBound : right < native.adj_ls.length := by rwa [good.1]
      have leftTagBound : left < native.node_tag.length := by rwa [good.2.1]
      have rightTagBound : right < native.node_tag.length := by rwa [good.2.1]
      have leftTag := related.tag_read left leftTagBound
      have rightTag := related.tag_read right rightTagBound
      have adjacency := cakeAdjMem_production left right related good rightBound
      rw [holEl_eq_getElem right native.adj_ls adjacencyBound] at adjacency
      simp only [fullConsistencyOk, if_neg equal, Translator.Monadic.MonadBase.bind, getDim,
        if_neg outside, adjLsSubEqn, if_pos adjacencyBound,
        holEl_eq_getElem right native.adj_ls adjacencyBound]
      rw [← adjacency]
      cases query : cakeAdjMem production left right
      · cases ltag : native.node_tag[left] <;> cases rtag : native.node_tag[right] <;>
          simp [query, isFixedK, isAtemp, Translator.Monadic.MonadBase.bind, nodeTagSubEqn, leftTagBound, rightTagBound,
            holEl_eq_getElem left native.node_tag leftTagBound,
            holEl_eq_getElem right native.node_tag rightTagBound,
            cakeFullConsistencyOk, leftTag, rightTag, ltag, rtag, Tag.toProduction,
            different, related.dimension, leftBound, rightBound, ret]
      · simp [query, ret, cakeFullConsistencyOk]

/-- Original reversed stateful filtering matches the executed move selection.
No endpoint bounds are required: the complete admission guard handles them. -/
theorem fullConsistencyFilter_production (limit : Nat) (moves : List (Nat × (Nat × Nat)))
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (acc : List (Nat × (Nat × Nat))) :
    stExFilter (fun move => fullConsistencyOk limit move.2.1 move.2.2) moves acc native =
      (.success ((filterReversed
        (fun move => cakeFullConsistencyOk production limit move.2.1 move.2.2) moves) ++ acc), native) := by
  rw [filterReversed_production]
  induction moves generalizing acc with
  | nil => rfl
  | cons move moves ih =>
      simp only [stExFilter, Translator.Monadic.MonadBase.bind,
        fullConsistencyOk_production limit move.2.1 move.2.2 related good]
      cases selected : cakeFullConsistencyOk production limit move.2.1 move.2.2 <;>
        simp only [Bool.false_eq_true, if_false, if_true, List.filter_cons,
          selected, List.reverse_cons, List.append_assoc, List.singleton_append]
      all_goals exact ih _

end Flapjack.RegAlloc
