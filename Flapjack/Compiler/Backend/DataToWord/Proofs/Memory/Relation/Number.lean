import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation

/-! Consequences of the data-to-word memory relation for numeric values. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A numeric value's related abstract address projects to a word. This
Flapjack helper combines the value invariant with the address projection. -/
theorem numberValueWordAddr {width : Nat} [NeZero width] (conf : Config) (i : Int)
    (refs : Spt (BvlSem.Ref Value)) (root : HeapAddress (WordLocW width))
    (f tf : HolFiniteMapExact Nat Nat) (heap : ValueHeap width)
    (related : valueInv conf (.number i) refs (root, f, tf, heap)) :
    ∃ word : BitVec width, wordAddr conf root = .word word := by
  have hnumber := (valueInv_number conf i refs root f tf heap).mp related
  by_cases small : smallInt width i
  · simp only [small, ↓reduceIte] at hnumber
    subst root
    exact ⟨_, rfl⟩
  · simp only [small, ↓reduceIte] at hnumber
    obtain ⟨ptr, rfl, _⟩ := hnumber
    exact ⟨_, rfl⟩

/-- A numeric data value is represented by a word location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_IMP_Word"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberImpWord {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i : Int) (location : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.number i, location) :: vars) →
      ∃ word : BitVec width, location = .word word := by
  rintro ⟨heap, limit, a, sp, sp1, gens, _, hword, _, _⟩
  dsimp [wordMlInv] at hword
  rcases hword with ⟨roots, habs, haddresses⟩
  dsimp [absMlInv] at habs
  rcases habs with ⟨_, _, _, _, hstack⟩
  dsimp [bcStackRefInv] at hstack
  rcases hstack with ⟨f, tf, _, _, _, _, _, _, _, hvalues, _⟩
  cases roots with
  | nil => cases hvalues
  | cons root rest =>
      cases hvalues with
      | cons hvalue _ =>
        cases haddresses with
        | cons haddress _ =>
          obtain ⟨word, hword⟩ := numberValueWordAddr conf i refs root f tf heap hvalue
          exact ⟨word, haddress.symm.trans hword⟩

/-- Two numeric data values are each represented by a word location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_IMP_Word_2"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_numberImpWord2 {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : Int) (first second : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i, first) :: (.number j, second) :: vars) →
      ∃ w1 w2 : BitVec width, first = .word w1 ∧ second = .word w2 := by
  rintro ⟨heap, limit, a, sp, sp1, gens, _, hword, _, _⟩
  dsimp [wordMlInv] at hword
  rcases hword with ⟨roots, habs, haddresses⟩
  dsimp [absMlInv] at habs
  rcases habs with ⟨_, _, _, _, hstack⟩
  dsimp [bcStackRefInv] at hstack
  rcases hstack with ⟨f, tf, _, _, _, _, _, _, _, hvalues, _⟩
  cases roots with
  | nil => cases hvalues
  | cons root roots =>
      cases roots with
      | nil => cases hvalues with | cons _ rest => cases rest
      | cons root' rest =>
          cases hvalues with
          | cons hvalue more =>
            cases more with
            | cons hvalue' _ =>
              cases haddresses with
              | cons haddress more =>
                cases more with
                | cons haddress' _ =>
                  obtain ⟨w1, hw1⟩ := numberValueWordAddr conf i refs root f tf heap hvalue
                  obtain ⟨w2, hw2⟩ := numberValueWordAddr conf j refs root' f tf heap hvalue'
                  exact ⟨w1, w2, haddress.symm.trans hw1, haddress'.symm.trans hw2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
