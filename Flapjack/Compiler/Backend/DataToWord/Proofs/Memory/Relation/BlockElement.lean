import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader

/-! Concrete heap elements needed by the block-indexing simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- A contiguous word-list assertion separates at a list append. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_list_APPEND"
  (words_as_type_indexed_bitvec)]
theorem wordListAppend {width : Nat} [NeZero width] {β : Type}
    (xs ys : List β) (address : BitVec width) :
    Misc.wordList address (xs ++ ys) =
      SetSep.star (Misc.wordList address xs)
        (Misc.wordList (address + BitVec.ofNat width xs.length * StackRemove.bytesInWord width) ys) := by
  induction xs generalizing address with
  | nil => simp [Misc.wordList, StackRemove.StackHeap.starEmptyLeft]
  | cons head tail ih =>
    simp only [List.cons_append, Misc.wordList, ih, List.length_cons]
    rw [← SetSep.starAssoc]
    congr 2
    congr 1
    simp only [BitVec.ofNat_add]
    simp only [BitVec.add_mul, BitVec.one_mul]
    ac_rfl

/-- Every in-bounds item of a separated word list occurs at its modular
address. This is Flapjack infrastructure for the block-element memory proof. -/
theorem wordList_indexMember {width : Nat} [NeZero width] {β : Type}
    (xs : List β) (i : Nat) (bound : i < xs.length) (address : BitVec width)
    (whole : (BitVec width × β) → Prop) (assertion : Misc.wordList address xs whole) :
    whole (address + BitVec.ofNat width i * StackRemove.bytesInWord width, xs[i]) := by
  induction xs generalizing i address whole with
  | nil => simp at bound
  | cons x xs ih =>
    obtain ⟨left, right, split, singleton, tail⟩ := assertion
    cases i with
    | zero =>
      have member : left (address, x) := by rw [singleton]
      have result := (iff_of_eq (congrFun split.1 (address, x))).mp (Or.inl member)
      simpa using result
    | succ i =>
      have nextBound : i < xs.length := by simpa using bound
      have member := ih i nextBound (address + StackRemove.bytesInWord width) right tail
      have result := (iff_of_eq (congrFun split.1 _)).mp (Or.inr member)
      have addressEq : address + StackRemove.bytesInWord width +
          BitVec.ofNat width i * StackRemove.bytesInWord width =
          address + BitVec.ofNat width (i + 1) * StackRemove.bytesInWord width := by
        simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        ac_rfl
      simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, ← addressEq] using result

/-- Each child of a looked-up block contributes its projected word at the
corresponding payload address. This is Flapjack separation infrastructure for
`memory_rel_Block_MEM`. -/
theorem wordHeap_blockElement {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index tag : Nat) (roots : List (HeapAddress (WordLocW width)))
    (i : Nat) (bound : i < roots.length) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (blockRep tag roots))
    (heapAssertion : wordHeap curr heap conf whole) :
    whole (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
      StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
      wordAddr conf roots[i]) := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (blockRep tag roots) found
  subst heap
  subst index
  rw [wordHeapAppend] at heapAssertion
  obtain ⟨prefixHeap, restHeap, split1, _, restAssertion⟩ := heapAssertion
  change SetSep.star (wordEl _ (blockRep tag roots) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, blockRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, _⟩ := elementAssertion
  obtain ⟨singleton, tailHeap, split4, _, tailAssertion⟩ := listAssertion
  let start := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before)
  let cell := (start + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
    wordAddr conf roots[i])
  have tailMember : tailHeap cell := by
    have h := wordList_indexMember (roots.map (wordAddr conf)) i (by simpa using bound)
      (start + StackRemove.bytesInWord width) tailHeap tailAssertion
    simpa only [List.getElem_map] using h
  have listMember : listHeap cell := by
    rw [← split4.1]
    exact Or.inr tailMember
  have elementMember : elementHeap cell := by
    rw [← split3.1]
    exact Or.inl listMember
  have restMember : restHeap cell := by
    rw [← split2.1]
    exact Or.inl elementMember
  have wholeMember : whole cell := by
    rw [← split1.1]
    exact Or.inr restMember
  exact wholeMember

/-- A block child is readable from concrete memory at the decoded block
address plus its header and element offset. This is Flapjack infrastructure for
`memory_rel_Block_MEM`. -/
theorem heapInMemoryStore_blockElement {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index tag : Nat) (roots : List (HeapAddress (WordLocW width)))
    (i : Nat) (bound : i < roots.length) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (limit : Nat)
    (annot : WordLocW width) (good : goodDimindex width)
    (found : heapLookup index heap = some (blockRep tag roots))
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ addr : BitVec width,
      getRealAddr conf store (getAddr conf index annot) = some addr ∧
      memory (addr + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width) =
        wordAddr conf roots[i] ∧
      domain (addr + StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width) = true := by
  have heapBound := heapMem.1
  obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
  obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
  have activeMember := wordHeap_blockElement conf heap index tag roots i bound curr active found activeHeap
  have graph : SetSep.fun2Set (memory, fun addr => domain addr = true)
      (curr + StackRemove.bytesInWord width * BitVec.ofNat width index +
       StackRemove.bytesInWord width + BitVec.ofNat width i * StackRemove.bytesInWord width,
       wordAddr conf roots[i]) := by
    rw [← split.1]
    exact Or.inl activeMember
  have facts := (SetSep.fun2SetThm memory (fun addr => domain addr = true) _ (wordAddr conf roots[i])).mp graph
  have addr := (getRealAddr_getAddr conf store heap index (blockRep tag roots) curr annot
    ⟨heapBound, found, stored, good⟩).2
  refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width index, ?_, facts.1, facts.2⟩
  simpa only [BitVec.mul_comm] using addr

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
