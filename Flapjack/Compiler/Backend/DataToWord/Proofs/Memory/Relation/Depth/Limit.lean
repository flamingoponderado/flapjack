import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth.Elements
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCardinality

/-! Constructing ancestor chains from source value depth. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- A nonempty list contains a value attaining its maximum depth. -/
private theorem maxDepth_mem (xs : List Value) (nonempty : xs ≠ []) :
    ∃ x, x ∈ xs ∧ vDepth x = vDepthMax xs := by
  induction xs with
  | nil => contradiction
  | cons x xs ih =>
    cases xs with
    | nil => exact ⟨x, by simp, by simp [vDepthMax]⟩
    | cons y ys =>
      obtain ⟨z, mem, maxEq⟩ := ih (by simp)
      by_cases h : vDepth x ≥ vDepthMax (y :: ys)
      · exact ⟨x, by simp, by rw [vDepthMax, Nat.max_eq_left h]⟩
      · exact ⟨z, by simp [mem], by rw [vDepthMax, Nat.max_eq_right (Nat.le_of_not_ge h), maxEq]⟩

/-- A child of a block has smaller source structural size. -/
theorem child_size_lt (x : Value) (stamp tag : Nat) (xs : List Value) (mem : x ∈ xs) :
    valueBlockSize x < valueBlockSize (.block stamp tag xs) := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem mem
  simp only [valueBlockSize, List.map_append, List.map_cons, List.sum_append,
    List.sum_cons, List.length_append, List.length_cons]
  omega

/-- Extend a related value to an ancestor chain realizing its depth. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_depth_limit"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_depthLimit {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v : Value) (location : WordLocW width) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((v, location) :: vars) ∧
      elementsList (v :: vars.map Prod.fst) ∧ goodDimindex width →
    ∃ ls, memoryRel conf be next refs space store memory domain (ls ++ (v, location) :: vars) ∧
      vDepth v = ls.length ∧ elementsList (ls.map Prod.fst ++ v :: vars.map Prod.fst) := by
  generalize eqSize : valueBlockSize v = n
  induction n using Nat.strong_induction_on generalizing v location vars with
  | h n ih =>
    rintro ⟨rel, chain, good⟩
    cases v with
    | number i => exact ⟨[], by simpa using rel, by simp [vDepth], by simpa using chain⟩
    | word64 w => exact ⟨[], by simpa using rel, by simp [vDepth], by simpa using chain⟩
    | codePtr c => exact ⟨[], by simpa using rel, by simp [vDepth], by simpa using chain⟩
    | refPtr b i => exact ⟨[], by simpa using rel, by simp [vDepth], by simpa using chain⟩
    | block stamp tag xs =>
      by_cases empty : xs = []
      · subst xs
        exact ⟨[], by simpa using rel, by simp [vDepth, vDepthMax], by simpa using chain⟩
      · obtain ⟨child, member, maxEq⟩ := maxDepth_mem xs empty
        have less : valueBlockSize child < n := by
          rw [← eqSize]
          exact child_size_lt child stamp tag xs member
        obtain ⟨before, after, xsEq⟩ := List.append_of_mem member
        subst xs
        have bound : before.length < (before ++ child :: after).length := by simp
        obtain ⟨w, addr, offset, _, _, _, _, extended⟩ :=
          memoryRel_blockMem conf be next refs space store memory domain stamp tag
            (before ++ child :: after) location vars before.length bound ⟨rel, good⟩
        have childRel : memoryRel conf be next refs space store memory domain
            ((child, memory (addr + offset)) :: (.block stamp tag (before ++ child :: after), location) :: vars) := by
          simpa using extended
        have childChain : elementsList (child :: .block stamp tag (before ++ child :: after) :: vars.map Prod.fst) := by
          simp only [elementsList]
          exact ⟨stamp, tag, before, after, by simp, chain⟩
        obtain ⟨ls, lsRel, depthEq, lsChain⟩ := ih (valueBlockSize child) less child (memory (addr + offset))
          ((.block stamp tag (before ++ child :: after), location) :: vars) rfl ⟨childRel, childChain, good⟩
        refine ⟨ls ++ [(child, memory (addr + offset))], ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using lsRel
        · simp only [vDepth, empty, ↓reduceIte, List.length_append, List.length_cons, List.length_nil]
          omega
        · simpa [List.map_append, List.append_assoc] using lsChain

/-- A related source value's depth is bounded by the number of machine words.
    This combines the source chain and cardinality theorems for later resource bounds. -/
theorem memoryRel_depthWordBound {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v : Value) (location : WordLocW width) (vars : List (Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((v, location) :: vars))
    (good : goodDimindex width) : vDepth v ≤ 2 ^ width := by
  have single : memoryRel conf be next refs space store memory domain [(v, location)] := by
    apply memoryRel_rearrange conf be next refs space store memory domain _ _ ?_ rel
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
    exact Or.inl hp
  obtain ⟨ls, extended, depth, chain⟩ := memoryRel_depthLimit conf be next refs space
    store memory domain v location [] ⟨single, by simp [elementsList], good⟩
  let related := ls ++ [(v, location)]
  have relation : memoryRel conf be next refs space store memory domain related := by simpa [related] using extended
  have chain' : elementsList (related.map Prod.fst) := by simpa [related] using chain
  have distinct := memoryRel_elementsListDistinct conf be next refs space store memory domain
    (related.map Prod.fst) related ⟨relation, chain', rfl, good⟩
  have nonempty : related ≠ [] := by simp [related]
  have words := memoryRel_elementsListWords conf be next refs space store memory domain
    (related.map Prod.fst) related ⟨relation, chain', rfl, good⟩ nonempty
  have bound := wordListLimit (related.tail.map Prod.snd) ⟨by simpa using words, distinct⟩
  have len : related.tail.length = ls.length := by
    cases ls with
    | nil => simp [related]
    | cons a rest => simp [related]
  rw [List.length_map, len, ← depth] at bound
  exact bound

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
