import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeader
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Values.Thunk
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.ValueInv.Reference

/-! Concrete heap facts used by the source thunk memory-relation proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The evaluated-thunk tag has the original four low tag bits. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "thunk_tag_bits_lemma"
  (words_as_type_indexed_bitvec)]
theorem thunkTagBits_evaluated {width : Nat} [NeZero width] :
    ((thunkTagToBits .evaluated : BitVec width) <<< (3 : Nat)) ||| 6 = 14 := by
  have shifted : ((1 : BitVec width) <<< (3 : Nat)) = BitVec.ofNat width 8 := by
    apply BitVec.eq_of_toNat_eq
    have positive : 1 < 2 ^ width := Nat.one_lt_two_pow (NeZero.ne width)
    simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt positive]
  simp only [thunkTagToBits, shifted]
  change BitVec.ofNat width 8 ||| BitVec.ofNat width 6 = BitVec.ofNat width 14
  rw [← BitVec.ofNat_or]
  rfl

/-- References reachable through a thunk child were already reachable from
the thunk pointer. HOL uses this edge when extending the root stack. -/
theorem reachableRefs_thunkChild (refs : Spt (BvlSem.Ref Value)) (stack : List Value)
    (bit : Bool) (ptr : Nat) (mode : AstHOL.ThunkMode) (child : Value) (target : Nat)
    (found : sptLookup ptr refs = some (.thunk mode child)) :
    reachableRefs (child :: .refPtr bit ptr :: stack) refs target →
      reachableRefs (.refPtr bit ptr :: stack) refs target := by
  rintro ⟨source, start, inStack, inRefs, path⟩
  rcases List.mem_cons.mp inStack with eq | old
  · subst source
    refine ⟨.refPtr bit ptr, ptr, by simp, by simp [getRefs], ?_⟩
    have edge : refEdge refs ptr start := by
      simpa [refEdge, found, getRefs] using inRefs
    exact Relation.ReflTransGen.head edge path
  · exact ⟨source, start, old, inRefs, path⟩

/-- Exposing a thunk's child preserves the abstract heap invariant. The
original value-invariant split distinguishes an inlined evaluated child
from a separately allocated thunk cell and ensures the inlined child is not
itself a thunk. -/
theorem absMlInv_thunkChild {width : Nat} [NeZero width] (conf : Config)
    (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (bigEndian : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState) (limit next : Nat)
    (bit : Bool) (ptr : Nat) (mode : AstHOL.ThunkMode) (child : Value)
    (found : sptLookup ptr refs = some (.thunk mode child))
    (inv : absMlInv conf (.refPtr bit ptr :: stack) refs
      (roots, heap, bigEndian, a, sp, sp1, gens) limit next) :
    ∃ (parent childRoot : HeapAddress (WordLocW width)) (rest : List (HeapAddress (WordLocW width))),
      roots = parent :: rest ∧ bit = false ∧
      ((mode = .evaluated ∧ parent = childRoot ∧ destThunk child refs = .notThunk) ∨
        ∃ index, parent = .pointer index (.word 0) ∧ heapLookup index heap = some (thunkBlock mode childRoot)) ∧
      absMlInv conf (child :: .refPtr bit ptr :: stack) refs
        (childRoot :: roots, heap, bigEndian, a, sp, sp1, gens) limit next := by
  obtain ⟨rootOk, heapOk', gc, unused, stackInv⟩ := inv
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimestamps, tfBound, endian, unique, related, cells⟩ := stackInv
  cases roots with
  | nil => cases related
  | cons parent rest =>
    cases related with
    | cons parentRelated remaining =>
      have childValues : allValues refs (.refPtr bit ptr :: stack) child := by
        exact Or.inr (Or.inl ⟨ptr, mode, child, found, mem_valueListValues [child] child (by simp)⟩)
      have extended (childRoot : HeapAddress (WordLocW width))
          (childRelated : valueInv conf child refs (childRoot, f, tf, heap))
          (validRoot : ∀ index annot, childRoot = .pointer index annot → isSomeDataElement (heapLookup index heap)) :
          absMlInv conf (child :: .refPtr bit ptr :: stack) refs
            (childRoot :: parent :: rest, heap, bigEndian, a, sp, sp1, gens) limit next := by
        refine ⟨?_, heapOk', gc, unused, ?_⟩
        · intro index annot member
          rcases List.mem_cons.mp member with eq | old
          · exact validRoot index annot eq.symm
          · exact rootOk index annot old
        · refine ⟨f, tf, fInj, fDomain, tfInj, ?_, tfBound, endian, ?_, ?_, ?_⟩
          · intro ts dom
            rw [← allTimestamps_headEq child refs (.refPtr bit ptr :: stack) () childValues]
            exact tfTimestamps ts dom
          · intro ts tag1 xs1 tag2 xs2 ⟨first, ne1, second, ne2⟩
            have subset := allValues_addThunk refs ptr mode child (.refPtr bit ptr :: stack) found
            exact unique ts tag1 xs1 tag2 xs2 ⟨subset _ first, ne1, subset _ second, ne2⟩
          · exact .cons childRelated (.cons parentRelated remaining)
          · intro n ⟨reachable, dom⟩
            exact cells n ⟨reachableRefs_thunkChild refs stack bit ptr mode child n found reachable, dom⟩
      rcases (valueInv_refPtr conf bit ptr refs parent f tf heap).mp parentRelated with
        nonThunk | allocated | inlined
      · exact False.elim (nonThunk.2.1 mode child found)
      · obtain ⟨actualMode, actualChild, childRoot, lookup, safe, domain, cell, childRelated, bitEq, parentEq⟩ := allocated
        have same := Option.some.inj (found.symm.trans lookup)
        cases same
        have validRoot : ∀ index annot, childRoot = .pointer index annot → isSomeDataElement (heapLookup index heap) := by
          intro index annot eq
          apply heapOk'.2.2 [childRoot] 1 (.thunkTag mode, []) index annot
          refine ⟨?_, by simp [eq]⟩
          simpa only [thunkBlock] using heapLookup_mem heap (holFapply f ptr) (thunkBlock mode childRoot) cell
        exact ⟨parent, childRoot, rest, rfl, bitEq, Or.inr ⟨holFapply f ptr, parentEq, cell⟩,
          extended childRoot childRelated validRoot⟩
      · obtain ⟨actualChild, lookup, safe, bitEq, childRelated⟩ := inlined
        have same := Option.some.inj (found.symm.trans lookup)
        cases same
        have validRoot : ∀ index annot, parent = .pointer index annot → isSomeDataElement (heapLookup index heap) := by
          intro index annot eq
          apply rootOk index annot
          simp [eq]
        exact ⟨parent, parent, rest, rfl, bitEq, Or.inl ⟨rfl, rfl, safe⟩,
          extended parent childRelated validRoot⟩

/-- The corresponding word-level invariant can expose the child at its
projected root while keeping the original thunk pointer on the stack. -/
theorem wordMlInv_thunkChild {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (bigEndian : Bool) (a sp sp1 : Nat)
    (gens : GcCombined.GenState) (limit next : Nat)
    (refs : Spt (BvlSem.Ref Value)) (bit : Bool) (ptr : Nat)
    (mode : AstHOL.ThunkMode) (child : Value) (location : WordLocW width)
    (vars : List (Value × WordLocW width))
    (found : sptLookup ptr refs = some (.thunk mode child))
    (inv : wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs
      ((.refPtr bit ptr, location) :: vars)) :
    ∃ (parent childRoot : HeapAddress (WordLocW width)),
      bit = false ∧ location = wordAddr conf parent ∧
      ((mode = .evaluated ∧ parent = childRoot ∧ destThunk child refs = .notThunk) ∨
        ∃ index, parent = .pointer index (.word 0) ∧ heapLookup index heap = some (thunkBlock mode childRoot)) ∧
      wordMlInv (heap, bigEndian, a, sp, sp1, gens) limit next conf refs
        ((child, wordAddr conf childRoot) :: (.refPtr bit ptr, location) :: vars) := by
  obtain ⟨roots, abstract, addresses⟩ := inv
  obtain ⟨parent, childRoot, rest, rootEq, bitEq, cases, extended⟩ :=
    absMlInv_thunkChild conf (vars.map Prod.fst) refs roots heap bigEndian a sp sp1 gens limit next
      bit ptr mode child found abstract
  subst roots
  cases addresses with
  | cons parentAddr restAddresses =>
    exact ⟨parent, childRoot, bitEq, parentAddr.symm, cases,
      childRoot :: parent :: rest, extended, .cons rfl (.cons parentAddr restAddresses)⟩

/-- A thunk cell contributes both its header and its sole payload to the
separated word heap. HOL derives this by splitting `word_heap` at the cell. -/
theorem wordHeap_thunkCell {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (mode : AstHOL.ThunkMode)
    (root : HeapAddress (WordLocW width)) (curr : BitVec width)
    (whole : (BitVec width × WordLocW width) → Prop)
    (found : heapLookup index heap = some (thunkBlock mode root))
    (heapAssertion : wordHeap curr heap conf whole) :
    let address := curr + wordSemBytesInWord * BitVec.ofNat width index
    let header := makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1
    whole (address, .word header) ∧
      whole (address + wordSemBytesInWord, wordAddr conf root) ∧
      WordGcFunctions.decodeLength conf header = 1 := by
  obtain ⟨before, after, heapEq, indexEq⟩ := heapLookup_split heap index (thunkBlock mode root) found
  subst heap
  subst index
  rw [wordHeapAppend] at heapAssertion
  obtain ⟨prefixHeap, restHeap, split1, _, restAssertion⟩ := heapAssertion
  change SetSep.star (wordEl _ (thunkBlock mode root) conf) (wordHeap _ after conf) restHeap at restAssertion
  obtain ⟨elementHeap, suffixHeap, split2, elementAssertion, _⟩ := restAssertion
  simp only [wordEl, thunkBlock, wordPayload, List.map_cons, List.map_nil, List.isEmpty_nil,
    Bool.true_and, List.length_cons, List.length_nil] at elementAssertion
  obtain ⟨listHeap, pureHeap, split3, listAssertion, pureAssertion⟩ := elementAssertion
  obtain ⟨headerHeap, restListHeap, split4, headerAssertion, tailAssertion⟩ := listAssertion
  obtain ⟨valueHeap, emptyHeap, split5, valueAssertion, _⟩ := tailAssertion
  let header : BitVec width := makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1
  let address := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength before)
  have headerMem : headerHeap (address, .word header) := by
    change headerHeap = (fun entry => entry = (address, .word header)) at headerAssertion
    rw [headerAssertion]
  have valueMem : valueHeap (address + StackRemove.bytesInWord width, wordAddr conf root) := by
    change valueHeap = (fun entry => entry = (address + StackRemove.bytesInWord width, wordAddr conf root)) at valueAssertion
    rw [valueAssertion]
  have hm := split_left_member listHeap headerHeap restListHeap _ split4 headerMem
  have vm := split_right_member listHeap headerHeap restListHeap _ split4
    (split_left_member restListHeap valueHeap emptyHeap _ split5 valueMem)
  have hm := split_right_member whole prefixHeap restHeap _ split1
    (split_left_member restHeap elementHeap suffixHeap _ split2
      (split_left_member elementHeap listHeap pureHeap _ split3 hm))
  have vm := split_right_member whole prefixHeap restHeap _ split1
    (split_left_member restHeap elementHeap suffixHeap _ split2
      (split_left_member elementHeap listHeap pureHeap _ split3 vm))
  exact ⟨hm, vm, pureAssertion.2.2.1⟩

/-- A thunk in the abstract heap has a decoded concrete address containing
its header and payload, both inside the memory domain. This is the heap split
used in the allocated-thunk branch of the original HOL proof. -/
theorem heapInMemoryStore_thunkCell {width : Nat} [NeZero width] (conf : Config)
    (heap : ValueHeap width) (index : Nat) (mode : AstHOL.ThunkMode)
    (root : HeapAddress (WordLocW width)) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool) (limit : Nat)
    (annot : WordLocW width) (good : goodDimindex width)
    (found : heapLookup index heap = some (thunkBlock mode root))
    (heapMem : heapInMemoryStore heap a sp sp1 gens conf store memory domain limit) :
    ∃ address header : BitVec width,
      getRealSimpleAddr conf store (getAddr conf index annot) = some address ∧
      getRealAddr conf store (getAddr conf index annot) = some address ∧
      header = makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1 ∧
      memory address = .word header ∧ domain address = true ∧
      memory (address + wordSemBytesInWord) = wordAddr conf root ∧
      domain (address + wordSemBytesInWord) = true ∧
      WordGcFunctions.decodeLength conf header = 1 := by
  have heapBound := heapMem.1
  obtain ⟨curr, other, _, _, stored, _, _, _, _, _, _, _, heapAssertion⟩ := heapMem.2.2.2.2.2.2.2
  obtain ⟨active, inactive, split, activeHeap, _⟩ := heapAssertion
  obtain ⟨headerMem, valueMem, decoded⟩ := wordHeap_thunkCell conf heap index mode root curr active found activeHeap
  let address := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
  let header : BitVec width := makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1
  have headerGraph := split_left_member (SetSep.fun2Set (memory, fun addr => domain addr = true))
    active inactive _ split headerMem
  have valueGraph := split_left_member (SetSep.fun2Set (memory, fun addr => domain addr = true))
    active inactive _ split valueMem
  have headerFacts := (SetSep.fun2SetThm memory (fun addr => domain addr = true) address (.word header)).mp headerGraph
  have valueFacts := (SetSep.fun2SetThm memory (fun addr => domain addr = true)
    (address + wordSemBytesInWord) (wordAddr conf root)).mp valueGraph
  have addr := (getRealAddr_getAddr conf store heap index (thunkBlock mode root) curr annot
    ⟨heapBound, found, stored, good⟩).2
  have simple := getRealSimpleAddr_getAddr conf store heap index (thunkBlock mode root) curr annot
    heapBound found stored good
  refine ⟨address, header, ?_, ?_, rfl, headerFacts.1, headerFacts.2, valueFacts.1, valueFacts.2, decoded⟩
  · simpa only [address, BitVec.mul_comm] using simple
  · simpa only [address, BitVec.mul_comm] using addr

/-- The source thunk header carries its evaluation mode in bit five, with
bits three and four set and bit two clear. HOL derives these bits by
simplifying the encoded header in the allocated-thunk case. The configuration
bound is a conjunct of `heapInMemoryStore`, not an additional premise of the
source memory-relation theorem. -/
theorem thunkHeader_bits {width : Nat} [NeZero width] (conf : Config) (mode : AstHOL.ThunkMode)
    (good : goodDimindex width) (configBound : conf.lenSize + 7 < width) :
    let header : BitVec width := makeHeader conf ((thunkTagToBits mode <<< (3 : Nat)) ||| 6) 1
    header.getLsbD 3 = true ∧ header.getLsbD 2 = false ∧ header.getLsbD 4 = true ∧
      (header.getLsbD 5 = true ↔ mode = .evaluated) := by
  have h2 : ¬ (2 : Nat) ≥ width - conf.lenSize := by omega
  have h3 : ¬ (3 : Nat) ≥ width - conf.lenSize := by omega
  have h4 : ¬ (4 : Nat) ≥ width - conf.lenSize := by omega
  have h5 : ¬ (5 : Nat) ≥ width - conf.lenSize := by omega
  cases mode with
  | evaluated =>
      dsimp only
      rw [thunkTagBits_evaluated]
      rcases good with hw | hw <;> subst width <;>
        simp [makeHeader] <;> omega
  | notEvaluated =>
      rcases good with hw | hw <;> subst width <;>
        simp [makeHeader, thunkTagToBits] <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
