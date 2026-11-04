import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackPermute

/-! Rearrangement of values in the full data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Restricting or reordering the paired stack preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_rearrange"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_rearrange {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (xs ys : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    (∀ pair, pair ∈ ys → pair ∈ xs) → memoryRel conf bigEndian next refs space store memory domain xs →
      memoryRel conf bigEndian next refs space store memory domain ys := by
  intro subset related
  obtain ⟨heap, limit, a, sp, sp1, gens, hstore, hword, hbound, hspace⟩ := related
  exact ⟨heap, limit, a, sp, sp1, gens, hstore,
    wordMlInv_rearrange heap bigEndian a sp sp1 gens limit next conf refs xs ys subset hword,
    hbound, hspace⟩

open Classical in
/-- Updating both functions at one key preserves the relation for their
mapped key list when the replacement pair is already a related root. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_IMP_MAP_UPDATE"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_mapUpdate {width : Nat} [NeZero width] {α : Type} (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (value : Flapjack.Compiler.Backend.DataSem.Value) (word : WordLocW width)
    (source : α → Flapjack.Compiler.Backend.DataSem.Value) (target : α → WordLocW width)
    (index : α) (keys : List α) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((value, word) :: keys.map (fun key => (source key, target key)) ++ vars) →
    memoryRel conf bigEndian next refs space store memory domain
      (keys.map (fun key => (Function.update source index value key, Function.update target index word key)) ++ vars) := by
  apply memoryRel_rearrange conf bigEndian next refs space store memory domain
  intro pair member
  simp only [List.mem_append, List.mem_map, List.mem_cons] at member ⊢
  rcases member with ⟨key, inKeys, rfl⟩ | inVars
  · by_cases same : key = index
    · subst key
      simp
    · simp [Function.update, same]
      exact Or.inl (Or.inr ⟨key, inKeys, rfl, rfl⟩)
  · exact Or.inr inVars

/-- Removing the first paired value preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_tl"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_tl {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (x : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)
    (xs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain (x :: xs) →
      memoryRel conf bigEndian next refs space store memory domain xs := by
  apply memoryRel_rearrange conf bigEndian next refs space store memory domain (x :: xs) xs
  intro pair member
  exact List.mem_cons_of_mem x member

/-- The source's second tail lemma, with the same tail operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_tail"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_tail {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (x : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)
    (xs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain (x :: xs) →
      memoryRel conf bigEndian next refs space store memory domain xs :=
  memoryRel_tl conf bigEndian next refs space store memory domain x xs

/-- Removing a paired stack prefix preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_drop"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_drop {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (dropped rest : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain (dropped ++ rest) →
      memoryRel conf bigEndian next refs space store memory domain rest := by
  apply memoryRel_rearrange conf bigEndian next refs space store memory domain (dropped ++ rest) rest
  intro pair member
  exact List.mem_append_right dropped member

/-- Swapping the first two paired values preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_swap"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_swap {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (x y : Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)
    (rest : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain (x :: y :: rest) →
      memoryRel conf bigEndian next refs space store memory domain (y :: x :: rest) := by
  apply memoryRel_rearrange conf bigEndian next refs space store memory domain (x :: y :: rest) (y :: x :: rest)
  intro pair member
  rcases List.mem_cons.mp member with first | member
  · exact List.mem_cons_of_mem x (List.mem_cons.mpr (Or.inl first))
  · rcases List.mem_cons.mp member with second | tail
    · exact List.mem_cons.mpr (Or.inl second)
    · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y tail)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
