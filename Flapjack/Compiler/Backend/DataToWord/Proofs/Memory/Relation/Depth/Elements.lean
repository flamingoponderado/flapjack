module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth.BlockPointer
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Misc.Sorting
public import Flapjack.Misc.ListEl
public import Mathlib.Data.List.Basic

@[expose] public section

/-! Ancestor-chain consequences of the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

instance elementsInst1 : Nonempty Value := ⟨.number 0⟩

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

/-- Strictly ordered related blocks occupy distinct target locations. -/
private theorem relatedBlocks_distinct {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain vars → goodDimindex width →
    List.Forall (fun x => ∃ stamp tag values, x = Value.block stamp tag values) (vars.map Prod.fst) →
    holSorted (fun x y => valueBlockSize x < valueBlockSize y) (vars.map Prod.fst) →
    (vars.map Prod.snd).Nodup := by
  induction vars with
  | nil => simp
  | cons pair rest ih =>
    intro rel good blocks sorted
    obtain ⟨v, location⟩ := pair
    simp only [List.map_cons, List.forall_cons] at blocks
    simp only [List.map_cons, List.nodup_cons]
    have trans : holTransitive (fun x y : Value => valueBlockSize x < valueBlockSize y) := by
      intro x y z h
      exact Nat.lt_trans h.1 h.2
    have ordered := (holSortedEq _ (rest.map Prod.fst) v trans).mp sorted
    constructor
    · intro member
      obtain ⟨⟨v', location'⟩, inRest, same⟩ := List.mem_map.mp member
      simp only at same
      subst location'
      have inValues : v' ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(v', location), inRest, rfl⟩
      obtain ⟨s, t, xs, hv⟩ := blocks.1
      obtain ⟨s', t', ys, hv'⟩ := (List.forall_iff_forall_mem.mp blocks.2) v' inValues
      subst v
      subst v'
      have both : memoryRel conf be next refs space store memory domain
          [(.block s t xs, location), (.block s' t' ys, location)] := by
        apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ rel
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr inRest
      have sameBlock := memoryRel_blockPtrEq conf be next refs space store memory domain
        s t s' t' xs ys location [] ⟨both, good⟩
      have smaller := ordered.2 _ inValues
      rw [sameBlock] at smaller
      exact (Nat.lt_irrefl _ smaller)
    · exact ih (memoryRel_tail conf be next refs space store memory domain (v, location) rest rel)
        good blocks.2 ordered.1

/-- Target locations in the tail of an ancestor chain are distinct. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_elements_list_distinct"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_elementsListDistinct {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (vs : List Value) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain vars ∧ elementsList vs ∧
      vs = vars.map Prod.fst ∧ goodDimindex width → (vars.tail.map Prod.snd).Nodup := by
  rintro ⟨rel, chain, eq, good⟩
  subst vs
  cases vars with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp
    | cons second remaining =>
      obtain ⟨v, location⟩ := first
      obtain ⟨child, childLocation⟩ := second
      simp only [List.map_cons, elementsList] at chain
      obtain ⟨stamp, tag, before, after, childEq, tailChain⟩ := chain
      subst child
      have tailRel := memoryRel_tail conf be next refs space store memory domain (v, location)
        ((.block stamp tag (before ++ [v] ++ after), childLocation) :: remaining) rel
      have chainInfo := elementsListAllBlocks
        (((Value.block stamp tag (before ++ [v] ++ after), childLocation) :: remaining).map Prod.fst)
        ⟨tailChain, by simp, ⟨stamp, tag, before ++ [v] ++ after, rfl⟩⟩
      exact relatedBlocks_distinct conf be next refs space store memory domain _ tailRel good chainInfo.1 chainInfo.2

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
