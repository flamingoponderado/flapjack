module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StackOperations

@[expose] public section

/-! Code pointers and target locations in the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Every encoded heap pointer has its low marker bit set. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_addr_0"
  (words_as_type_indexed_bitvec)]
theorem getAddr_lowBit {width : Nat} [NeZero width] (conf : Config) (n : Nat) (u : WordLocW width) :
    (getAddr conf n u).getLsbD 0 = true := by
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  cases u <;> simp [getAddr, getLowerBits, pos]

/-- A target code location comes from a data location and has zero offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_addr_eq_Loc"
  (words_as_type_indexed_bitvec)]
theorem wordAddr_eqLoc {width : Nat} [NeZero width] (conf : Config)
    (address : HeapAddress (WordLocW width)) (l1 l2 : Nat) :
    wordAddr conf address = .loc l1 l2 ↔ l2 = 0 ∧ ∃ offset, address = .data (.loc l1 offset) := by
  cases address with
  | pointer index annot => simp [wordAddr]
  | data value =>
      cases value <;> simp [wordAddr, eq_comm, and_comm]

/-- Adding a code pointer does not add a nested block. This is Flapjack
invariant infrastructure. -/
theorem allValues_codeBlock (lab : Nat) (refs : Spt (BvlSem.Ref Value))
    (stack : List Value) (stamp tag : Nat) (items : List Value)
    (member : allValues refs (.codePtr lab :: stack) (.block stamp tag items)) :
    allValues refs stack (.block stamp tag items) := by
  rcases member with a | b | c | d
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (by simpa [valueListValues] using d)))

/-- Adding a code pointer preserves uniqueness of existing blocks. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_CodePtr"]
theorem blocksUnique_codePtr {α : Type} (vars : List (Value × α)) (refs : Spt (BvlSem.Ref Value))
    (next lab : Nat) :
    blocksUnique next (allValues refs (vars.map Prod.fst)) →
    blocksUnique next (allValues refs (.codePtr lab :: vars.map Prod.fst)) := by
  intro unique stamp tag1 xs1 tag2 xs2 ⟨first, nonempty1, second, nonempty2⟩
  exact unique stamp tag1 xs1 tag2 xs2
    ⟨allValues_codeBlock lab refs _ stamp tag1 xs1 first, nonempty1,
      allValues_codeBlock lab refs _ stamp tag2 xs2 second, nonempty2⟩

/-- Adding a code pointer and its abstract location preserves the abstract
invariant. This is Flapjack infrastructure for the full memory theorem. -/
theorem absMlInv_codePtr {width : Nat} [NeZero width] (conf : Config) (lab : Nat)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GenState) (limit next : Nat)
    (inv : absMlInv conf (vars.map Prod.fst) refs (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    absMlInv conf (.codePtr lab :: vars.map Prod.fst) refs
      (.data (.loc lab 0) :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  obtain ⟨rootOk, heapOk', gc, unused, stackInv⟩ := inv
  refine ⟨?_, heapOk', gc, unused, ?_⟩
  · intro ptr annotation member
    apply rootOk ptr annotation
    simpa using member
  · obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, values, cells⟩ := stackInv
    refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
    · intro stamp inDomain
      obtain ⟨value, member, timestamp⟩ := tfTimestamps stamp inDomain
      refine ⟨value, ?_, timestamp⟩
      rcases member with inRef | inStack
      · exact Or.inl inRef
      · exact Or.inr (List.mem_cons_of_mem _ inStack)
    · exact blocksUnique_codePtr vars refs next lab unique
    · exact .cons ((valueInv_codePtr conf lab refs _ f tf heap).mpr rfl) values
    · intro n ⟨reachable, inDomain⟩
      apply cells n
      refine ⟨?_, inDomain⟩
      obtain ⟨value, start, member, ref, path⟩ := reachable
      rcases List.mem_cons.mp member with same | inStack
      · subst value
        simp [getRefs] at ref
      · exact ⟨value, start, inStack, ref, path⟩

/-- A code pointer and its target location can be added to the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_CodePtr"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_codePtr {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (lab : Nat)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain vars →
    memoryRel conf bigEndian next refs space store memory domain ((.codePtr lab, .loc lab 0) :: vars) := by
  rintro ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩
  refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, bound, spaceBound⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  exact ⟨.data (.loc lab 0) :: roots,
    absMlInv_codePtr conf lab vars refs roots heap bigEndian a sp sp1 gens limit next inv,
    .cons rfl addresses⟩

/-- A related code location originates from the corresponding source code pointer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Loc"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_loc {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v : Value) (label offset : Nat) (vars : List (Value × WordLocW width)) :
    memoryRel conf be next refs space store memory domain ((v, .loc label offset) :: vars) ∧
      (∀ ptr, v ≠ .refPtr false ptr) → v = .codePtr label := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, _, wordInv, _, _⟩, notRef⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stackInv
  cases roots with
  | nil => cases values
  | cons root rest =>
    cases values with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        have value := related 0
        cases value <;> simp_all [wordAddr]

/-- A represented code pointer has the exact word-level code location. -/
theorem memoryRel_codePtr_location {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (label : Nat) (word : WordLocW width)
    (roots : List (DataSem.Value × WordLocW width))
    (rel : memoryRel conf be next refs space store memory domain ((.codePtr label, word) :: roots)) :
    word = .loc label 0 := by
  obtain ⟨heap, limit, a, sp, sp1, gens, _, hword, _, _⟩ := rel
  obtain ⟨xs, habs, addresses⟩ := hword
  obtain ⟨_, _, _, _, stack⟩ := habs
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stack
  cases xs with
  | nil => cases values
  | cons x xs =>
    cases values with
    | cons valueInv _ =>
      cases addresses with
      | cons address _ =>
        have eq := (valueInv_codePtr conf label refs x f tf heap).mp valueInv
        subst x
        simpa [wordAddr] using address.symm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
