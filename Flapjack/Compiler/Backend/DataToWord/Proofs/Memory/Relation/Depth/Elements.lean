import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.Sorting
import Flapjack.Misc.ListEl

/-! Ancestor-chain consequences of the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

private instance : Nonempty Value := ⟨.number 0⟩

/-- A value has strictly smaller structural size than any block containing it. -/
private theorem valueBlockSize_child (v : Value) (stamp tag : Nat) (before after : List Value) :
    valueBlockSize v < valueBlockSize (.block stamp tag (before ++ [v] ++ after)) := by
  simp only [valueBlockSize, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, List.length_append, List.length_cons, List.length_nil]
  omega

/-- A nonempty ancestor chain beginning with a block consists of blocks and
    has strictly increasing structural sizes. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "elements_list_all_blocks"]
theorem elementsListAllBlocks (xs : List Value) :
    elementsList xs ∧ xs ≠ [] ∧ (∃ stamp tag values, holHd xs = Value.block stamp tag values) →
    List.Forall (fun x => ∃ stamp tag values, x = Value.block stamp tag values) xs ∧
      holSorted (fun x y => valueBlockSize x < valueBlockSize y) xs := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    rintro ⟨chain, _, first⟩
    cases rest with
    | nil =>
      simp only [holHd] at first
      exact ⟨by simpa [List.forall_cons, List.Forall] using first, by simp [holSorted]⟩
    | cons y ys =>
      simp only [elementsList] at chain
      obtain ⟨stamp, tag, before, after, yEq, tailChain⟩ := chain
      subst y
      have firstBlock : ∃ stamp tag values, x = Value.block stamp tag values := by simpa [holHd] using first
      obtain ⟨tailBlocks, tailSorted⟩ := ih ⟨tailChain, by simp, ⟨stamp, tag, before ++ [x] ++ after, rfl⟩⟩
      exact ⟨(List.forall_cons _ _ _).mpr ⟨firstBlock, tailBlocks⟩,
        ⟨valueBlockSize_child x stamp tag before after, tailSorted⟩⟩

/-- All target locations after the first in an ancestor chain are words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_elements_list_words"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_elementsListWords {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vs : List Value) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain vars ∧ elementsList vs ∧
      vs = vars.map Prod.fst ∧ goodDimindex width → vars ≠ [] →
    ((vars.map Prod.snd).tail.all wordSemIsWordLoc) = true := by
  induction vars generalizing vs with
  | nil => simp
  | cons pair rest ih =>
    rintro ⟨rel, chain, eq, good⟩ _
    subst vs
    cases pair with
    | mk v w =>
      cases rest with
      | nil => simp
      | cons second remaining =>
        cases second with
        | mk child location =>
          simp only [List.map_cons, elementsList] at chain
          obtain ⟨stamp, tag, before, after, childEq, chainTail⟩ := chain
          subst child
          have tailRel := memoryRel_tail conf be next refs space store memory domain (v, w)
            ((.block stamp tag (before ++ [v] ++ after), location) :: remaining) rel
          obtain ⟨word, loc, _⟩ := memoryRel_blockImp conf be next refs space store memory domain
            stamp tag (before ++ [v] ++ after) location remaining ⟨tailRel, good⟩
          subst location
          have restWords := ih _ ⟨tailRel, chainTail, rfl, good⟩ (by simp)
          simpa [wordSemIsWordLoc] using restWords

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
