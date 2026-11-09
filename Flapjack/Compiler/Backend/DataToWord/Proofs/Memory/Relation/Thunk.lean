module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ThunkHeap
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.WordTest
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberHeader

@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Derive the two mask inequalities from the source bit tests. HOL performs
this propositional step inline using its two local word-test lemmas. -/
private theorem headerDiff {width : Nat} [NeZero width] (header : BitVec width)
    (good : goodDimindex width)
    (different : header.getLsbD 2 = true ∨ header.getLsbD 3 = false ∨ header.getLsbD 4 = false) :
    (header &&& 60) ≠ BitVec.ofNat width ((0 + 6) * 4) ∧
      (header &&& 60) ≠ BitVec.ofNat width ((8 + 6) * 4) := by
  constructor <;> intro eq
  · have bits := (wordTestLemma2 header good).mp (by simpa [BitVec.and_comm] using eq)
    rcases different with b | b | b <;> simp_all
  · have bits := (wordTestLemma1 header good).mp (by simpa [BitVec.and_comm] using eq)
    rcases different with b | b | b <;> simp_all

private theorem byteHeaderBit2 {width : Nat} [NeZero width] (conf : Config) (length : Nat)
    (flag : Bool) (good : goodDimindex width) :
    (makeByteHeader (width := width) conf flag length).getLsbD 2 = true := by
  rcases good with hw | hw <;> subst width <;> cases flag <;> simp [makeByteHeader]

/-- A related thunk is either an inlined evaluated value or an allocated
thunk cell, with the complete corresponding memory and domain facts. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Thunk_IMP"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_thunkImp {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (ptr : Nat) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) (mode : AstHOL.ThunkMode) (child : Value) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, location) :: vars) ∧
      sptLookup ptr refs = some (.thunk mode child) ∧ goodDimindex width →
    (bit = false ∧ mode = .evaluated ∧ ∀ w : BitVec width,
      location = .word w ∧ w.getLsbD 0 = true →
      memoryRel conf be next refs space store memory domain ((child, location) :: vars) ∧
      ∃ address header : BitVec width,
        getRealAddr conf store w = some address ∧ memory address = .word header ∧ domain address = true ∧
        (header &&& 60) ≠ BitVec.ofNat width ((0 + 6) * 4) ∧
        (header &&& 60) ≠ BitVec.ofNat width ((8 + 6) * 4)) ∨
    ∃ w address header : BitVec width,
      location = .word w ∧ w.getLsbD 0 = true ∧ header.getLsbD 3 = true ∧
      header.getLsbD 2 = false ∧ header.getLsbD 4 = true ∧
      getRealSimpleAddr conf store w = some address ∧ getRealAddr conf store w = some address ∧
      memory address = .word header ∧ domain address = true ∧ domain (address + wordSemBytesInWord) = true ∧
      WordGcFunctions.decodeLength conf header = 1 ∧
      (header.getLsbD 5 = true ↔ mode = .evaluated) ∧
      memoryRel conf be next refs space store memory domain
        ((child, memory (address + wordSemBytesInWord)) :: (.refPtr bit ptr, location) :: vars) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩, found, good⟩
  obtain ⟨parent, childRoot, bitEq, locationEq, cases, extended⟩ :=
    wordMlInv_thunkChild conf heap be a sp sp1 gens limit next refs bit ptr mode child location vars found wordInv
  rcases cases with inline | allocated
  case inl =>
    obtain ⟨modeEq, rootEq, safe⟩ := inline
    refine Or.inl ⟨bitEq, modeEq, ?_⟩
    intro w ⟨locationWord, low⟩
    have twoRel : memoryRel conf be next refs space store memory domain
        ((child, location) :: (.refPtr bit ptr, location) :: vars) := by
      refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, limitBound, spaceBound⟩
      simpa only [← rootEq, ← locationEq] using extended
    have oneRel : memoryRel conf be next refs space store memory domain ((child, location) :: vars) := by
      apply memoryRel_rearrange conf be next refs space store memory domain
        ((child, location) :: (.refPtr bit ptr, location) :: vars) ((child, location) :: vars)
      · intro pair member
        simp only [List.mem_cons] at member ⊢
        tauto
      · exact twoRel
    refine ⟨oneRel, ?_⟩
    cases child with
    | word64 value =>
      obtain ⟨index, address, header, loc, real, dom, mem, _, bit4, bit2, _⟩ :=
        memoryRel_word64Imp conf be next refs space store memory domain value location vars ⟨oneRel, good⟩
      have wordEq : getAddr conf index (.word 0) = w := WordLocW.word.inj (loc.symm.trans locationWord)
      have diff := headerDiff header good (Or.inl bit2)
      exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
    | number value =>
      obtain ⟨numberWord, numberLoc, bitIff⟩ := memoryRel_anyNumberImp conf be next refs space store
        memory domain value location vars ⟨good, oneRel⟩
      have numberWordEq : numberWord = w := WordLocW.word.inj (numberLoc.symm.trans locationWord)
      have large : ¬ smallInt width value := bitIff.mp (by rw [numberWordEq]; exact low)
      obtain ⟨word, address, frame, loc, real, mem, dom, _, _, _, bit2, _⟩ :=
        memoryRel_bignumWords conf be next refs space store memory domain value location vars ⟨oneRel, large, good⟩
      have wordEq : word = w := WordLocW.word.inj (loc.symm.trans locationWord)
      let header : BitVec width := makeHeader conf (((if value < 0 then 1 else 0) <<< 2) ||| 3)
        (Misc.Multiword.n2mw (width := width) value.natAbs).length
      have diff := headerDiff header good (Or.inl bit2)
      exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
    | codePtr label =>
      have loc := memoryRel_codePtr_location conf be next refs space store memory domain label location vars oneRel
      rw [loc] at locationWord
      cases locationWord
    | block stamp tag children =>
      obtain ⟨word, loc, layout⟩ := memoryRel_blockImp conf be next refs space store memory domain
        stamp tag children location vars ⟨oneRel, good⟩
      have wordEq : word = w := WordLocW.word.inj (loc.symm.trans locationWord)
      by_cases empty : children = []
      · simp only [empty, ↓reduceIte] at layout
        rw [wordEq] at layout
        simp [low] at layout
      · simp only [empty, ↓reduceIte] at layout
        obtain ⟨address, header, _, bit3, _, real, mem, dom, _⟩ := layout
        have diff := headerDiff header good (Or.inr (Or.inl bit3))
        exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
    | refPtr refBit refIndex =>
      obtain ⟨cell, refFound⟩ := memoryRel_refPtrExists conf be next refs space store memory domain
        refBit refIndex location vars oneRel
      cases cell with
      | thunk nestedMode nested =>
        simp [destThunk, refFound] at safe
        split at safe <;> contradiction
      | valueArray values =>
        obtain ⟨word, address, header, loc, _, _, _, bit4, _, real, mem, dom, _⟩ :=
          memoryRel_valueArrayImp conf be next refs space store memory domain refBit refIndex values location vars
            ⟨oneRel, refFound, good⟩
        have wordEq : word = w := WordLocW.word.inj (loc.symm.trans locationWord)
        have diff := headerDiff header good (Or.inr (Or.inr bit4))
        exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
      | byteArray flag bytes =>
        obtain ⟨word, address, loc, _, real, _, mem, dom, _, _⟩ :=
          memoryRel_byteArrayHeader conf be next refs space store memory domain refBit flag refIndex bytes location vars
            oneRel refFound good
        have wordEq : word = w := WordLocW.word.inj (loc.symm.trans locationWord)
        let header := makeByteHeader (width := width) conf flag bytes.length
        have diff := headerDiff header good (Or.inl (byteHeaderBit2 conf bytes.length flag good))
        exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
      | mutBlock tag finalised left val right =>
        obtain ⟨otherHeap, otherLimit, otherA, otherSp, otherSp1, otherGens,
          otherHeapMem, otherWordInv, _, _⟩ := oneRel
        obtain ⟨otherRoots, otherInv, otherAddresses⟩ := otherWordInv
        obtain ⟨_, _, _, _, otherStackInv⟩ := otherInv
        obtain ⟨f, tf, _, _, _, _, _, _, _, related, cells⟩ := otherStackInv
        cases otherRoots with
        | nil => cases related
        | cons root rest =>
          cases related with
          | cons related _ =>
            cases otherAddresses with
            | cons projected _ =>
              have noThunk : ∀ md v, sptLookup refIndex refs ≠ some (.thunk md v) := by
                intro md v eq
                rw [refFound] at eq
                cases eq
              obtain ⟨domainF, _, rootEq⟩ :=
                (valueInv_refPtr_notThunk conf refBit refIndex refs root f tf otherHeap noThunk).mp related
              obtain ⟨index, ffound⟩ := domainF
              let annot : WordLocW width := refPtrAnnot conf (some (.mutBlock tag finalised left val right))
              have rootEq' : root = .pointer index annot := by
                simpa [refFound, holFapply_of_lookup ffound, annot] using rootEq
              have reachable : reachableRefs (.refPtr refBit refIndex :: vars.map Prod.fst) refs refIndex := by
                exact ⟨.refPtr refBit refIndex, refIndex, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
              have cellInv := cells refIndex ⟨reachable, ⟨index, ffound⟩⟩
              obtain ⟨_, _, children, cell, _⟩ :
                  (∀ sizes, conf.gcKind ≠ .generational sizes) ∧
                  (finalised = false → ¬ ∃ stamp, mapDomain tf stamp ∧ holFapply tf stamp = index) ∧
                  ∃ children, heapLookup index otherHeap = some (blockRep tag children) ∧
                    List.Forall₂ (fun address value => valueInv conf value refs (address, f, tf, otherHeap))
                      children (left ++ [val] ++ right) := by
                simpa [bcRefInv, ffound, refFound] using cellInv
              obtain ⟨address, header, real, mem, dom, _, _, encoded⟩ :=
                heapInMemoryStore_blockHeader conf otherHeap index tag children otherA otherSp otherSp1
                  otherGens store memory domain otherLimit annot good cell otherHeapMem
              have loc : location = .word (getAddr conf index annot) := by
                rw [rootEq'] at projected
                simpa [wordAddr] using projected.symm
              have wordEq : getAddr conf index annot = w := WordLocW.word.inj (loc.symm.trans locationWord)
              have bits := encodedBlockHeader_bits conf tag children.length header good otherHeapMem.2.2.2.2.1 encoded
              have diff := headerDiff header good (Or.inr (Or.inl bits.1))
              exact ⟨address, header, by rw [← wordEq]; exact real, mem, dom, diff.1, diff.2⟩
  case inr =>
    obtain ⟨index, parentEq, cell⟩ := allocated
    subst parent
    obtain ⟨address, header, simpleEq, realEq, headerEq, memoryEq, inDomain, childEq, childDomain, decoded⟩ :=
      heapInMemoryStore_thunkCell conf heap index mode childRoot a sp sp1 gens store memory domain limit
        (.word 0) good cell heapMem
    have bits := thunkHeader_bits conf mode good heapMem.2.2.2.2.1
    dsimp only at bits
    rw [← headerEq] at bits
    refine Or.inr ⟨getAddr conf index (.word 0), address, header, ?_, ?_, bits.1, bits.2.1, bits.2.2.1,
      simpleEq, realEq, memoryEq, inDomain, childDomain, decoded, bits.2.2.2, ?_⟩
    · simpa [wordAddr] using locationEq
    · exact getAddr_lowBit conf index _
    · refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, limitBound, spaceBound⟩
      simpa only [childEq] using extended
/-- A thunk represented by a location or a word with clear low bit is
evaluated and can be replaced by its child in the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Thunk_inlined"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_thunkInlined {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (ptr : Nat) (location : WordLocW width)
    (vars : List (Value × WordLocW width)) (mode : AstHOL.ThunkMode) (child : Value) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, location) :: vars) ∧
      ((∃ l1 l2, location = .loc l1 l2) ∨
        ∃ word : BitVec width, location = .word word ∧ word.getLsbD 0 = false) ∧
      sptLookup ptr refs = some (.thunk mode child) ∧ goodDimindex width →
    mode = .evaluated ∧ memoryRel conf be next refs space store memory domain ((child, location) :: vars) := by
  rintro ⟨⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩, immediate, found, _⟩
  obtain ⟨parent, childRoot, _, locationEq, cases, extended⟩ :=
    wordMlInv_thunkChild conf heap be a sp sp1 gens limit next refs bit ptr mode child location vars found wordInv
  rcases cases with inlined | allocated
  · obtain ⟨modeEq, rootEq, _⟩ := inlined
    refine ⟨modeEq, ?_⟩
    have twoRel : memoryRel conf be next refs space store memory domain
        ((child, location) :: (.refPtr bit ptr, location) :: vars) := by
      refine ⟨heap, limit, a, sp, sp1, gens, heapMem, ?_, limitBound, spaceBound⟩
      simpa only [← rootEq, ← locationEq] using extended
    apply memoryRel_rearrange conf be next refs space store memory domain
      ((child, location) :: (.refPtr bit ptr, location) :: vars) ((child, location) :: vars)
    · intro pair member
      simp only [List.mem_cons] at member ⊢
      tauto
    · exact twoRel
  · obtain ⟨index, parentEq, _⟩ := allocated
    rw [parentEq] at locationEq
    simp only [wordAddr] at locationEq
    rcases immediate with ⟨l1, l2, loc⟩ | ⟨word, loc, low⟩
    · rw [loc] at locationEq
      cases locationEq
    · rw [loc] at locationEq
      have wordEq := WordLocW.word.inj locationEq
      rw [wordEq] at low
      simp [getAddr_lowBit conf index] at low

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
