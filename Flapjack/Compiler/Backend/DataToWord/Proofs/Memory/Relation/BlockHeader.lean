import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer

/-! Reading a concrete block header from the separated heap assertion. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- A member of the left part of a separated heap belongs to the whole heap.
This is Flapjack separation infrastructure. -/
private theorem split_left_member {α : Type} (whole left right : α → Prop) (entry : α)
    (split : SetSep.split whole (left, right)) (member : left entry) : whole entry := by
  have eq := congrFun split.1 entry
  exact (iff_of_eq eq).mp (Or.inl member)

/-- A member of the right part of a separated heap belongs to the whole heap.
This is Flapjack separation infrastructure. -/
private theorem split_right_member {α : Type} (whole left right : α → Prop) (entry : α)
    (split : SetSep.split whole (left, right)) (member : right entry) : whole entry := by
  have eq := congrFun split.1 entry
  exact (iff_of_eq eq).mp (Or.inr member)

/-- A block cell in a word heap contributes its header at its concrete heap
address and satisfies the original payload checks. This is Flapjack
separation infrastructure for the constructor-memory theorem. -/
theorem wordHeap_blockHeader {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index tag : Nat) (roots : List (HeapAddress (WordLocW width)))
    (curr : BitVec width) (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (blockRep tag roots))
    (heapAssertion : wordHeap curr heap conf whole) :
    ∃ header : BitVec width,
      whole (curr + StackRemove.bytesInWord width * BitVec.ofNat width index, .word header) ∧
      roots.length < 2 ^ (width - 4) ∧
      WordGcFunctions.decodeLength conf header = BitVec.ofNat width roots.length ∧
      encodeHeader conf (tag * 4) roots.length = some header := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (blockRep tag roots) found
  subst heap
  subst index
  rw [wordHeapAppend] at heapAssertion
  obtain ⟨prefixHeap, restHeap, split1, _, restAssertion⟩ := heapAssertion
  change SetSep.star (wordEl _ (blockRep tag roots) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, blockRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
  obtain ⟨singleton, tailHeap, split4, singletonAssertion, _⟩ := listAssertion
  let header : BitVec width := makeHeader conf (BitVec.ofNat width tag <<< (2 : Nat)) roots.length
  let address := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before)
  have member1 : singleton (address, .word header) := by
    change singleton = (fun entry => entry = (address, .word header)) at singletonAssertion
    rw [singletonAssertion]
  have member2 := split_left_member listHeap singleton tailHeap _ split4 member1
  have member3 := split_left_member elementHeap listHeap pureHeap _ split3 member2
  have member4 := split_left_member restHeap elementHeap suffixHeap _ split2 member3
  have member5 := split_right_member whole prefixHeap restHeap _ split1 member4
  have checks := pureAssertion.2
  refine ⟨header, member5, checks.1, checks.2.1, ?_⟩
  simpa only [decide_eq_true_eq, true_and] using checks.2.2

/-- A looked-up block contributes a valid header to the concrete memory
at the decoded pointer address. This is Flapjack infrastructure for the
constructor-memory relation. -/
theorem heapInMemoryStore_blockHeader {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index tag : Nat) (roots : List (HeapAddress (WordLocW width)))
    (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (limit : Nat)
    (annot : WordLocW width) (good : goodDimindex width)
    (found : heapLookup index heap = some (blockRep tag roots))
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ addr header : BitVec width,
      getRealAddr conf store (getAddr conf index annot) = some addr ∧
      memory addr = .word header ∧ domain addr = true ∧
      roots.length < 2 ^ (width - 4) ∧
      WordGcFunctions.decodeLength conf header = BitVec.ofNat width roots.length ∧
      encodeHeader conf (tag * 4) roots.length = some header := by
  have heapBound := heapMem.1
  obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
  obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
  obtain ⟨header, member, lengthBound, decoded, encoded⟩ :=
    wordHeap_blockHeader conf heap index tag roots curr active found activeHeap
  have graph := split_left_member (SetSep.fun2Set (memory, fun addr => domain addr = true))
    active inactive _ split member
  have facts := (SetSep.fun2SetThm memory (fun addr => domain addr = true) _ (.word header)).mp graph
  have addr := (getRealAddr_getAddr conf store heap index (blockRep tag roots) curr annot
    ⟨heapBound, found, stored, good⟩).2
  refine ⟨curr + StackRemove.bytesInWord width * BitVec.ofNat width index, header, ?_, facts.1, facts.2,
    lengthBound, decoded, encoded⟩
  simpa only [BitVec.mul_comm] using addr

/-- Valid constructor headers have both low tag bits clear. This is Flapjack
bit-vector infrastructure for the constructor-memory theorem. -/
theorem encodedBlockHeader_bits {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) (h : BitVec width)
    (good : goodDimindex width) (configBound : conf.lenSize + 7 < width)
    (encoded : encodeHeader conf (tag * 4) len = some h) :
    h.getLsbD 3 = false ∧ h.getLsbD 2 = false := by
  unfold encodeHeader at encoded
  split at encoded
  next cond =>
    have eq : h = makeHeader conf (BitVec.ofNat width (tag * 4)) len := (Option.some.inj encoded).symm
    subst h
    have h2 : ¬ (2 : Nat) ≥ width - conf.lenSize := by omega
    have h3 : ¬ (3 : Nat) ≥ width - conf.lenSize := by omega
    rcases good with hw | hw <;> subst width <;>
      simp [makeHeader, BitVec.ofNat_mul, h2, h3] <;> bv_decide
  next cond => contradiction

/-- Empty block encodings retain their value under the immediate marker mask.
This is Flapjack bit-vector infrastructure for the constructor-memory theorem. -/
theorem blockNil_mask {width : Nat} [NeZero width] (good : goodDimindex width) (tag : Nat) :
    (blockNil (width := width) tag &&& ~~~(1 : BitVec width)) =
      BitVec.ofNat width tag * 16 + 2 ∧
    (blockNil (width := width) tag &&& ~~~(1 : BitVec width)).getLsbD 0 = false := by
  rcases good with h | h <;> subst width <;> simp [blockNil] <;> bv_decide

/-- A related constructor is either an immediate empty block or a pointer to
a valid concrete block header with a bounded timestamp. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Block_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_blockImp {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (stamp tag : Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (location : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain ((.block stamp tag values, location) :: vars) ∧
      goodDimindex width →
    ∃ w : BitVec width, location = .word w ∧
      if values = [] then
        w = BitVec.ofNat width tag * 16 + 2 ∧ w.getLsbD 0 = false ∧ tag < 2 ^ width / 16 ∧ stamp = 0
      else
        ∃ a x : BitVec width,
          w.getLsbD 0 = true ∧ x.getLsbD 3 = false ∧ x.getLsbD 2 = false ∧
          getRealAddr conf store w = some a ∧ memory a = .word x ∧ domain a = true ∧
          WordGcFunctions.decodeLength conf x = BitVec.ofNat width values.length ∧
          values.length < 2 ^ (width - 4) ∧ encodeHeader conf (4 * tag) values.length = some x ∧ stamp < next := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, _, _⟩, good⟩
  obtain ⟨roots, inv, addresses⟩ := wordInv
  obtain ⟨_, _, _, _, stackInv⟩ := inv
  obtain ⟨f, tf, _, _, _, _, tfBound, _, _, valueRel, _⟩ := stackInv
  cases roots with
  | nil => cases valueRel
  | cons root rest =>
    cases valueRel with
    | cons related _ =>
      cases addresses with
      | cons projected _ =>
        by_cases empty : values = []
        · subst values
          obtain ⟨rootEq, tagBound, stampEq⟩ := (valueInv_emptyBlock conf stamp tag refs root f tf heap).mp related
          subst root
          refine ⟨(blockNil tag &&& ~~~(1 : BitVec width)), projected.symm, ?_⟩
          simp only [ite_true]
          exact ⟨(blockNil_mask good tag).1, (blockNil_mask good tag).2, tagBound, stampEq⟩
        · obtain ⟨ptr, children, pair, lookup, rootEq, cell⟩ :=
            (valueInv_nonemptyBlock conf stamp tag values refs root f tf heap empty).mp related
          subst root
          have childrenLength : values.length = children.length := pair.length_eq
          obtain ⟨addr, header, addrEq, memoryEq, domainEq, lenBound, decoded, encoded⟩ :=
            heapInMemoryStore_blockHeader conf heap ptr tag children a sp sp1 gens store memory domain limit
              (.word (ptrBits conf tag children.length)) good cell heapMem
          have bits := encodedBlockHeader_bits conf tag children.length header good heapMem.2.2.2.2.1 encoded
          refine ⟨getAddr conf ptr (.word (ptrBits conf tag children.length)), projected.symm, ?_⟩
          simp only [empty, ↓reduceIte]
          refine ⟨addr, header, getAddr_lowBit conf ptr _, bits.1, bits.2, addrEq, memoryEq, domainEq, ?_, ?_, ?_, ?_⟩
          · simpa only [childrenLength] using decoded
          · simpa only [childrenLength] using lenBound
          · simpa only [childrenLength, Nat.mul_comm] using encoded
          · exact tfBound stamp ⟨ptr, lookup⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
