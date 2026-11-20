module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteXorInvariants
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.XorWordList
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArray
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Rearrange
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteXorHeap
public import Flapjack.Compiler.Backend.GenGc.Proofs.HeapLookup

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.WordGcFunctions

/-- Factor two separated byte cells and retain their common frame for the XOR proof. -/
private theorem byteTwoHeapFrame {width : Nat} [NeZero width] (c : Config) (curr : BitVec width)
    (pre mid post : ValueHeap width) (src dst : List (BitVec 8)) (be srcFlag dstFlag : Bool)
    (outer : ((BitVec width × WordLocW width) → Prop) → Prop)
    (good : goodDimindex width) (config : c.lenSize + 7 < width)
    (srcCount : src.length / (width / 8) + 1 < 2 ^ (width - 4))
    (srcLen : src.length / (width / 8) + 1 < 2 ^ c.lenSize)
    (dstCount : dst.length / (width / 8) + 1 < 2 ^ (width - 4))
    (dstLen : dst.length / (width / 8) + 1 < 2 ^ c.lenSize) :
    let srcWords := List.replicate (src.length / (width / 8) + 1) (0 : BitVec width)
    let dstWords := List.replicate (dst.length / (width / 8) + 1) (0 : BitVec width)
    let srcBase := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
    let midBase := srcBase + StackRemove.bytesInWord width * BitVec.ofNat width (srcWords.length + 1)
    let dstBase := midBase + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength mid)
    let postBase := dstBase + StackRemove.bytesInWord width * BitVec.ofNat width (dstWords.length + 1)
    let frame := SetSep.star (SetSep.star (wordHeap curr pre c) (SetSep.one (srcBase, .word (makeByteHeader c srcFlag src.length))))
      (SetSep.star (SetSep.star (wordHeap midBase mid c) (SetSep.one (dstBase, .word (makeByteHeader c dstFlag dst.length))))
        (SetSep.star (wordHeap postBase post c) outer))
    let srcPayload := Misc.wordList (srcBase + StackRemove.bytesInWord width) ((writeBytes src srcWords be).map WordLocW.word)
    let dstPayload := Misc.wordList (dstBase + StackRemove.bytesInWord width) ((writeBytes dst dstWords be).map WordLocW.word)
    SetSep.star (wordHeap curr (pre ++ [bytesRep be srcFlag src srcWords] ++ mid ++ [bytesRep be dstFlag dst dstWords] ++ post) c) outer =
      SetSep.star (SetSep.star srcPayload dstPayload) frame := by
  dsimp only
  rw [show pre ++ [bytesRep be srcFlag src (List.replicate (src.length / (width / 8) + 1) 0)] ++ mid ++ [bytesRep be dstFlag dst (List.replicate (dst.length / (width / 8) + 1) 0)] ++ post =
      pre ++ [bytesRep be srcFlag src (List.replicate (src.length / (width / 8) + 1) 0)] ++
        (mid ++ [bytesRep be dstFlag dst (List.replicate (dst.length / (width / 8) + 1) 0)] ++ post) by simp [List.append_assoc]]
  rw [byteHeapFrame c curr pre _ src be srcFlag outer good config srcCount srcLen]
  rw [byteHeapFrame c _ mid post dst be dstFlag outer good config dstCount dstLen]
  let : Std.Associative (@SetSep.star (BitVec width × WordLocW width)) := ⟨fun a b c => (SetSep.starAssoc a b c).symm⟩
  let : Std.Commutative (@SetSep.star (BitVec width × WordLocW width)) := ⟨SetSep.starComm⟩
  ac_rfl

/-- A distinct cell lies before or after a selected heap cell. -/
private theorem heapLookup_beforeOrAfter {α β : Type} (pre post : List (HeapElement α β)) (cell other : HeapElement α β) (index : Nat)
    (found : heapLookup index (pre ++ [cell] ++ post) = some other)
    (different : index ≠ heapLength pre) :
    (index < heapLength pre ∧ heapLookup index pre = some other) ∨
    (heapLength pre + elLength cell ≤ index ∧ heapLookup (index - (heapLength pre + elLength cell)) post = some other) := by
  rw [List.append_assoc, GenGc.heapLookup_append] at found
  by_cases h : index < heapLength pre
  · simp [h] at found
    exact Or.inl ⟨h, found⟩
  · simp only [h, ↓reduceIte, List.singleton_append] at found
    have nonzero : index - heapLength pre ≠ 0 := by omega
    by_cases inside : index - heapLength pre < elLength cell
    · simp [heapLookup, nonzero, inside] at found
    · right
      refine ⟨by omega, ?_⟩
      simp only [heapLookup, nonzero, ↓reduceIte, inside] at found
      simpa [Nat.sub_sub] using found

/-- XORing related byte arrays preserves the complete data-to-word memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_xor_bytes"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRelXorBytes {width : Nat} [NeZero width] (c : Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Value)) (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (bl1 bl2 : Bool) (p1 p2 : Nat) (v1 v2 : WordLocW width) (vars : List (Value × WordLocW width))
    (fl1 fl2 : Bool) (vals1 vals2 res : List (BitVec 8))
    (rel : memoryRel c be ts refs sp st m dm ((.refPtr bl1 p1,v1) :: (.refPtr bl2 p2,v2) :: vars))
    (found1 : sptLookup p1 refs = some (.byteArray fl1 vals1))
    (found2 : sptLookup p2 refs = some (.byteArray fl2 vals2))
    (h : SemanticPrimitivesHOL.xorBytes vals1 vals2 = some res) (good : goodDimindex width) :
    ∃ w1 a1 w2 a2 x1 m1, v1 = .word w1 ∧ v2 = .word w2 ∧
      getRealAddr c st w1 = some a1 ∧ getRealAddr c st w2 = some a2 ∧
      m a1 = .word x1 ∧ dm a1 = true ∧
      wordXorBytes (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord) (decodeLength c x1) dm m = some m1 ∧
      memoryRel c be ts (sptInsert p2 (.byteArray fl2 res) refs) sp st m1 dm
        ((.refPtr bl1 p1,v1) :: (.refPtr bl2 p2,v2) :: vars) := by
  have tailRel := memoryRel_tl c be ts refs sp st m dm (.refPtr bl1 p1, v1) ((.refPtr bl2 p2,v2)::vars) rel
  obtain ⟨w1, a1, v1Eq, tag1, addr1, simple1, head1, member1, config1, len1⟩ :=
    memoryRel_byteArrayHeader c be ts refs sp st m dm bl1 fl1 p1 vals1 v1 ((.refPtr bl2 p2,v2)::vars) rel found1 good
  obtain ⟨w2, a2, v2Eq, tag2, addr2, simple2, head2, member2, config2, len2⟩ :=
    memoryRel_byteArrayHeader c be ts refs sp st m dm bl2 fl2 p2 vals2 v2 vars tailRel found2 good
  have rel1 : memoryRel c be ts refs sp st m dm ((.refPtr bl1 p1, .word w1) :: (.refPtr bl2 p2,v2) :: vars) := by
    simpa [v1Eq] using rel
  obtain ⟨header, frame1, headerMem, payloadSep, countBound, countEq⟩ :=
    memoryRel_byteArrayWordsImp c be ts refs sp st m dm bl1 fl1 p1 vals1 w1 a1
      ((.refPtr bl2 p2,v2)::vars) ⟨rel1, found1, good, addr1⟩
  have headerEq : header = makeByteHeader (width := width) c fl1 vals1.length := by
    exact WordLocW.word.inj (Option.some.inj (congrArg some (headerMem.symm.trans head1)))
  subst header
  have countNat : (decodeLength c (makeByteHeader (width := width) c fl1 vals1.length)).toNat =
      (makeZeros (width := width) vals1).length := by
    simpa [makeZeros] using countEq
  have countBound2 : (makeZeros (width := width) vals1).length < 2 ^ width := by
    simpa [countNat] using countBound
  have decoded : decodeLength c (makeByteHeader (width := width) c fl1 vals1.length) =
      BitVec.ofNat width (makeZeros (width := width) vals1).length := by
    apply BitVec.eq_of_toNat_eq
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt countBound2] using countNat
  have lenBound1 : vals1.length / (width / 8) + 1 < 2 ^ c.lenSize := by
    rcases good with hw | hw <;> subst width <;>
      simp only [Nat.pow_add] at len1 ⊢ <;> norm_num at len1 ⊢ <;> omega
  have lenBound2 : vals2.length / (width / 8) + 1 < 2 ^ c.lenSize := by
    rcases good with hw | hw <;> subst width <;>
      simp only [Nat.pow_add] at len2 ⊢ <;> norm_num at len2 ⊢ <;> omega
  have cellBound1 : vals1.length / (width / 8) + 1 < 2 ^ (width - 4) := by
    apply Nat.lt_of_lt_of_le lenBound1
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have cellBound2 : vals2.length / (width / 8) + 1 < 2 ^ (width - 4) := by
    apply Nat.lt_of_lt_of_le lenBound2
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have sameLen : vals2.length = res.length := (xorBytesLength vals1 vals2 res h).2.symm
  have swapped : memoryRel c be ts refs sp st m dm ((.refPtr bl2 p2,v2) :: (.refPtr bl1 p1,v1) :: vars) := by
    apply memoryRel_rearrange c be ts refs sp st m dm ((.refPtr bl1 p1,v1) :: (.refPtr bl2 p2,v2) :: vars)
    · intro pair member
      simp only [List.mem_cons] at member ⊢
      rcases member with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact rel
  obtain ⟨heap, limit, heapA, heapSp, heapSp1, gens, heapMem, wordInv, heapBound, spaceBound⟩ := swapped
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have abs2 : absMlInv c (.refPtr bl2 p2 :: .refPtr bl1 p1 :: vars.map Prod.fst) refs
      (roots, heap, be, heapA, heapSp, heapSp1, gens) limit ts := by
    simpa using absInv
  let zeros2 : List (BitVec width) := makeZeros vals2
  have extracted : ∃ roots2 pre post,
      roots = .pointer (heapLength pre) (.word 0) :: roots2 ∧
      heap = pre ++ [bytesRep be fl2 vals2 zeros2] ++ post := by
    obtain ⟨_, _, _, _, stackInv⟩ := abs2
    obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, values, refsInv⟩ := stackInv
    cases roots with
    | nil => cases values
    | cons root roots2 =>
      have headInv : valueInv c (.refPtr bl2 p2) refs (root, f, tf, heap) := by
        cases values with | cons head _ => exact head
      have headAddress := valueInv_byteRefAddress c bl2 p2 refs root f tf heap fl2 vals2 found2 headInv
      have domainF2 : mapDomain f p2 := by
        rcases (valueInv_refPtr c bl2 p2 refs root f tf heap).mp headInv with ordinary | thunk | inlined
        · exact ordinary.1
        · obtain ⟨_, _, _, thunkFound, _⟩ := thunk
          rw [found2] at thunkFound
          cases thunkFound
        · obtain ⟨_, thunkFound, _⟩ := inlined
          rw [found2] at thunkFound
          cases thunkFound
      have reach : reachableRefs (.refPtr bl2 p2 :: .refPtr bl1 p1 :: vars.map Prod.fst) refs p2 := by
        exact ⟨.refPtr bl2 p2, p2, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
      obtain ⟨mapped, mappedLookup⟩ := domainF2
      have refInv := refsInv p2 ⟨reach, ⟨mapped, mappedLookup⟩⟩
      have heapFound : heapLookup mapped heap = some (bytesRep be fl2 vals2 zeros2) := by
        simpa [bcRefInv, mappedLookup, found2, zeros2, makeZeros] using refInv
      obtain ⟨pre, post, heapEq, mappedEq⟩ := heapLookup_split heap mapped _ heapFound
      have rootEq : root = .pointer (heapLength pre) (.word 0) := by
        rw [headAddress, holFapply_of_lookup mappedLookup, mappedEq]
      exact ⟨roots2, pre, post, by simp [rootEq], by simpa [List.append_assoc] using heapEq⟩
  obtain ⟨roots2, pre, post, rootsEq, heapEq⟩ := extracted
  subst roots
  subst heap
  have updatedAbs : absMlInv c (.refPtr bl2 p2 :: .refPtr bl1 p1 :: vars.map Prod.fst)
      (sptInsert p2 (.byteArray fl2 res) refs)
      (.pointer (heapLength pre) (.word 0) :: roots2,
        pre ++ [bytesRep be fl2 res zeros2] ++ post, be, heapA, heapSp, heapSp1, gens) limit ts := by
    obtain ⟨rootsOkOld, heapOkOld, gcOld, unusedOld, stackOld⟩ := abs2
    have shape := byteHeap_shape be fl2 vals2 res zeros2 pre post
    refine ⟨rootsOk_shape _ shape rootsOkOld, heapOk_shape shape limit heapOkOld, ?_, ?_, ?_⟩
    · have gcShape := byteHeap_gcShape be fl2 vals2 res zeros2 pre post
      exact gcKindInv_shape gcShape c heapA heapSp heapSp1 gens gcOld
    · exact unusedSpaceInv_shape shape heapA (heapSp + heapSp1) unusedOld
    · have result := bcStackRefInv_byteUpdate c ts (.refPtr bl1 p1 :: vars.map Prod.fst) refs roots2 pre post
        be fl2 bl2 vals2 res p2 sameLen found2 stackOld
      simpa [zeros2, makeZeros] using result
  have cellLookup : heapLookup (heapLength pre) (pre ++ [bytesRep be fl2 vals2 zeros2] ++ post) =
      some (bytesRep be fl2 vals2 zeros2) := by
    rw [List.append_assoc, Flapjack.Compiler.Backend.GenGc.heapLookup_append]
    simp [heapLookup]
  obtain ⟨hm1, hm2, hm3, hm4, hm5, hm6, hm7, curr, other, ca, oa, currStore, otherStore,
    nextStore, triggerStore, endStore, lengthStore, globInv, genInv, heapSeparated⟩ := heapMem
  have destWord : w2 = getAddr c (heapLength pre) (.word 0) := by
    cases rootWords with
    | cons head tail =>
      have headEq : wordAddr c (.pointer (heapLength pre) (.word 0)) = v2 := head
      simpa [wordAddr, v2Eq] using headEq.symm
  have destAddress : a2 = curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) := by
    have addrCalc := (getRealAddr_getAddr c st (pre ++ [bytesRep be fl2 vals2 zeros2] ++ post)
      (heapLength pre) _ curr (.word 0) ⟨hm1, cellLookup, currStore, good⟩).2
    rw [destWord] at addr2
    have eq := Option.some.inj (addr2.symm.trans addrCalc)
    simpa [BitVec.mul_comm] using eq
  have destHeapFrame := byteHeapFrame c curr pre post vals2 be fl2
    (wordHeap other (heapExpand limit) c) good config2 cellBound2 lenBound2
  have destPayloadSep : SetSep.star
      (Misc.wordList (a2 + wordSemBytesInWord) ((writeBytes vals2 zeros2 be).map WordLocW.word))
      (SetSep.star (SetSep.star (wordHeap curr pre c)
        (SetSep.one (a2, .word (makeByteHeader c fl2 vals2.length))))
        (SetSep.star (wordHeap (a2 + wordSemBytesInWord * BitVec.ofNat width (zeros2.length + 1)) post c)
          (wordHeap other (heapExpand limit) c))) (SetSep.fun2Set (m, fun k => dm k = true)) := by
    have canonicalSep : SetSep.star
        (wordHeap curr (pre ++ [bytesRep be fl2 vals2 (List.replicate (vals2.length / (width / 8) + 1) (0 : BitVec width))] ++ post) c)
        (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun k => dm k = true)) := by
      simpa [zeros2, makeZeros, BitVec.ofNat] using heapSeparated
    rw [destHeapFrame] at canonicalSep
    simpa only [zeros2, makeZeros, List.length_replicate, destAddress, wordSemBytesInWord, StackRemove.bytesInWord] using canonicalSep
  have relAfterOf : ∀ memory1,
      heapInMemoryStore (pre ++ [bytesRep be fl2 res zeros2] ++ post) heapA heapSp heapSp1 gens c st memory1 dm limit →
      memoryRel c be ts (sptInsert p2 (.byteArray fl2 res) refs) sp st memory1 dm
        ((.refPtr bl1 p1,v1) :: (.refPtr bl2 p2,v2) :: vars) := by
    intro memory1 heapAfter
    have swappedAfter : memoryRel c be ts (sptInsert p2 (.byteArray fl2 res) refs) sp st memory1 dm
        ((.refPtr bl2 p2,v2) :: (.refPtr bl1 p1,v1) :: vars) := by
      refine ⟨_, limit, heapA, heapSp, heapSp1, gens, heapAfter, ?_, heapBound, spaceBound⟩
      refine ⟨_, ?_, rootWords⟩
      simpa using updatedAbs
    apply memoryRel_rearrange c be ts (sptInsert p2 (.byteArray fl2 res) refs) sp st memory1 dm
      ((.refPtr bl2 p2,v2) :: (.refPtr bl1 p1,v1) :: vars)
    · intro pair member
      simp only [List.mem_cons] at member ⊢
      rcases member with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact swappedAfter
  have remaining : ∃ m1, wordXorBytes (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
      (decodeLength c (makeByteHeader (width := width) c fl1 vals1.length)) dm m = some m1 ∧
      heapInMemoryStore (pre ++ [bytesRep be fl2 res zeros2] ++ post) heapA heapSp heapSp1 gens c st m1 dm limit := by
    by_cases same : p1 = p2
    · subst p1
      have cellEq : BvlSem.Ref.byteArray fl1 vals1 = BvlSem.Ref.byteArray fl2 vals2 := Option.some.inj (found1.symm.trans found2)
      have flagEq : fl1 = fl2 := by cases cellEq; rfl
      have valsEq : vals1 = vals2 := by cases cellEq; rfl
      subst fl1
      subst vals1
      have bothRel : memoryRel c be ts refs sp st m dm ((.refPtr bl1 p2,.word w1) :: (.refPtr bl2 p2,.word w2) :: vars) := by
        simpa [v1Eq, v2Eq] using rel
      have wordEq := memoryRel_refPtrEqImp c be ts refs sp st m dm bl1 bl2 p2 w1 w2 fl2 vals2 vars ⟨bothRel, good, found2⟩
      have addressEq : a1 = a2 := by
        rw [wordEq] at addr1
        exact Option.some.inj (addr1.symm.trans addr2)
      subst a1
      let remainingFrame := SetSep.star (SetSep.star (wordHeap curr pre c)
        (SetSep.one (a2, .word (makeByteHeader c fl2 vals2.length))))
        (SetSep.star (wordHeap (a2 + wordSemBytesInWord * BitVec.ofNat width (zeros2.length + 1)) post c)
          (wordHeap other (heapExpand limit) c))
      have inSep : SetSep.star (Misc.wordList (a2 + wordSemBytesInWord)
          ((writeBytes vals2 (makeZeros (width := width) vals2) be).map WordLocW.word)) remainingFrame
          (SetSep.fun2Set (m, fun k => dm k = true)) := by simpa [remainingFrame, zeros2] using destPayloadSep
      obtain ⟨m1, outSep, run⟩ := xorBytesWordListAlias vals2 res (a2 + wordSemBytesInWord) be remainingFrame m dm h good
        countBound2 inSep
      refine ⟨m1, ?_, ?_⟩
      · simpa [decoded] using run
      · have resLen : res.length = vals2.length := sameLen.symm
        have resCountBound : res.length / (width / 8) + 1 < 2 ^ (width - 4) := by simpa [resLen] using cellBound2
        have resLenBound : res.length / (width / 8) + 1 < 2 ^ c.lenSize := by simpa [resLen] using lenBound2
        have afterFrame := byteHeapFrame c curr pre post res be fl2 (wordHeap other (heapExpand limit) c)
          good config2 resCountBound resLenBound
        have canonicalAfter : SetSep.star
            (wordHeap curr (pre ++ [bytesRep be fl2 res (List.replicate (res.length / (width / 8) + 1) (0 : BitVec width))] ++ post) c)
            (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m1, fun k => dm k = true)) := by
          rw [afterFrame]
          simpa only [remainingFrame, zeros2, makeZeros, List.length_replicate, destAddress,
            wordSemBytesInWord, StackRemove.bytesInWord, resLen] using outSep
        have afterSep : SetSep.star (wordHeap curr (pre ++ [bytesRep be fl2 res zeros2] ++ post) c)
            (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m1, fun k => dm k = true)) := by
          simpa [zeros2, makeZeros, resLen, BitVec.ofNat] using canonicalAfter
        have lengths := heapLength_shape (byteHeap_shape be fl2 vals2 res zeros2 pre post)
        refine ⟨?_, ?_, hm3, hm4, hm5, hm6, hm7, curr, other, ca, oa, currStore, otherStore,
          nextStore, triggerStore, endStore, lengthStore, globInv, genInv, afterSep⟩
        · simpa only [← lengths] using hm1
        · simpa only [← lengths] using hm2
    · have sourceInfo : ∃ idx1, idx1 ≠ heapLength pre ∧
          heapLookup idx1 (pre ++ [bytesRep be fl2 vals2 zeros2] ++ post) = some (bytesRep be fl1 vals1 (makeZeros vals1)) ∧
          a1 = curr + StackRemove.bytesInWord width * BitVec.ofNat width idx1 := by
        obtain ⟨_, _, _, _, stackInv⟩ := abs2
        obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, values, refsInv⟩ := stackInv
        cases roots2 with
        | nil =>
          cases values with | cons _ tail => cases tail
        | cons root1 roots3 =>
          cases values with
          | cons head2 tail =>
            cases tail with
            | cons head1 more =>
              have root2Addr := valueInv_byteRefAddress c bl2 p2 refs (.pointer (heapLength pre) (.word 0)) f tf _ fl2 vals2 found2 head2
              have root1Addr := valueInv_byteRefAddress c bl1 p1 refs root1 f tf _ fl1 vals1 found1 head1
              have domain2 : mapDomain f p2 := by
                rcases (valueInv_refPtr c bl2 p2 refs _ f tf _).mp head2 with ordinary | thunk | inlined
                · exact ordinary.1
                · obtain ⟨_, _, _, found, _⟩ := thunk; rw [found2] at found; cases found
                · obtain ⟨_, found, _⟩ := inlined; rw [found2] at found; cases found
              have domain1 : mapDomain f p1 := by
                rcases (valueInv_refPtr c bl1 p1 refs root1 f tf _).mp head1 with ordinary | thunk | inlined
                · exact ordinary.1
                · obtain ⟨_, _, _, found, _⟩ := thunk; rw [found1] at found; cases found
                · obtain ⟨_, found, _⟩ := inlined; rw [found1] at found; cases found
              obtain ⟨idx1, lookup1⟩ := domain1
              obtain ⟨idx2, lookup2⟩ := domain2
              rw [holFapply_of_lookup lookup2] at root2Addr
              have idx2Eq : idx2 = heapLength pre := (HeapAddress.pointer.inj root2Addr).1.symm
              have distinct : idx1 ≠ heapLength pre := by
                intro equal
                apply same
                apply injF.2 p1 p2 ⟨⟨idx1, lookup1⟩, ⟨idx2, lookup2⟩⟩
                rw [holFapply_of_lookup lookup1, holFapply_of_lookup lookup2, equal, idx2Eq]
              have reach1 : reachableRefs (.refPtr bl2 p2 :: .refPtr bl1 p1 :: vars.map Prod.fst) refs p1 := by
                exact ⟨.refPtr bl1 p1, p1, by simp, by simp [getRefs], Relation.ReflTransGen.refl⟩
              have inv1 := refsInv p1 ⟨reach1, ⟨idx1, lookup1⟩⟩
              have cell1 : heapLookup idx1 (pre ++ [bytesRep be fl2 vals2 zeros2] ++ post) =
                  some (bytesRep be fl1 vals1 (makeZeros vals1)) := by
                simpa [bcRefInv, lookup1, found1, makeZeros] using inv1
              have projected1 : wordAddr c root1 = v1 := by
                cases rootWords with | cons _ tail => cases tail with | cons head _ => exact head
              have sourceWord : w1 = getAddr c idx1 (.word 0) := by
                rw [root1Addr, holFapply_of_lookup lookup1, v1Eq] at projected1
                simpa [wordAddr] using (WordLocW.word.inj projected1).symm
              have addrCalc1 := (getRealAddr_getAddr c st (pre ++ [bytesRep be fl2 vals2 zeros2] ++ post)
                idx1 _ curr (.word 0) ⟨hm1, cell1, currStore, good⟩).2
              rw [sourceWord] at addr1
              have sourceAddr : a1 = curr + StackRemove.bytesInWord width * BitVec.ofNat width idx1 := by
                have eq := Option.some.inj (addr1.symm.trans addrCalc1)
                simpa [BitVec.mul_comm] using eq
              exact ⟨idx1, distinct, cell1, sourceAddr⟩
      obtain ⟨idx1, distinct, cell1, sourceAddr⟩ := sourceInfo
      rcases heapLookup_beforeOrAfter pre post (bytesRep be fl2 vals2 zeros2)
        (bytesRep be fl1 vals1 (makeZeros vals1)) idx1 cell1 distinct with before | after
      · obtain ⟨preA, mid, preEq, idxEq⟩ := heapLookup_split pre idx1 _ before.2
        have addrBefore1 : a1 = curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength preA) := by
          simpa [idxEq] using sourceAddr
        have addrBefore2 : a2 = (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength preA) +
              StackRemove.bytesInWord width * BitVec.ofNat width ((makeZeros (width := width) vals1).length + 1)) +
              StackRemove.bytesInWord width * BitVec.ofNat width (heapLength mid) := by
          rw [destAddress, preEq]
          simp [heapLength, elLengthBytes, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
        let srcBase := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength preA)
        let midBase := srcBase + StackRemove.bytesInWord width * BitVec.ofNat width ((makeZeros (width := width) vals1).length + 1)
        let dstBase := midBase + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength mid)
        let postBase := dstBase + StackRemove.bytesInWord width * BitVec.ofNat width ((makeZeros (width := width) vals2).length + 1)
        let frame := SetSep.star (SetSep.star (wordHeap curr preA c) (SetSep.one (srcBase, .word (makeByteHeader c fl1 vals1.length))))
          (SetSep.star (SetSep.star (wordHeap midBase mid c) (SetSep.one (dstBase, .word (makeByteHeader c fl2 vals2.length))))
            (SetSep.star (wordHeap postBase post c) (wordHeap other (heapExpand limit) c)))
        have inSep : SetSep.star (SetSep.star
            (Misc.wordList (a1 + wordSemBytesInWord) ((writeBytes vals1 (makeZeros vals1) be).map WordLocW.word))
            (Misc.wordList (a2 + wordSemBytesInWord) ((writeBytes vals2 (makeZeros vals2) be).map WordLocW.word))) frame
            (SetSep.fun2Set (m, fun k => dm k = true)) := by
          have sep := heapSeparated
          rw [preEq] at sep
          simp only [List.cons_append, List.nil_append, List.append_assoc] at sep
          have frameEq := byteTwoHeapFrame c curr preA mid post vals1 vals2 be fl1 fl2 (wordHeap other (heapExpand limit) c) good config2 cellBound1 lenBound1 cellBound2 lenBound2
          simp only [List.cons_append, List.nil_append, List.append_assoc] at frameEq
          simp only [zeros2, makeZeros] at sep
          rw [frameEq] at sep
          rw [addrBefore1, addrBefore2]
          simpa only [frame, postBase, dstBase, midBase, srcBase, zeros2, makeZeros, wordSemBytesInWord, StackRemove.bytesInWord] using sep
        obtain ⟨m1, outSep, run⟩ := xorBytesWordList vals1 vals2 res (a1 + wordSemBytesInWord)
          (a2 + wordSemBytesInWord) be frame m dm h good countBound2 inSep
        refine ⟨m1, ?_, ?_⟩
        · simpa [decoded] using run
        · have resLen : res.length = vals2.length := sameLen.symm
          have resCount : res.length / (width / 8) + 1 < 2 ^ (width - 4) := by simpa [resLen] using cellBound2
          have resBound : res.length / (width / 8) + 1 < 2 ^ c.lenSize := by simpa [resLen] using lenBound2
          have frameAfter := byteTwoHeapFrame c curr preA mid post vals1 res be fl1 fl2
            (wordHeap other (heapExpand limit) c) good config2 cellBound1 lenBound1 resCount resBound
          have afterSep : SetSep.star (wordHeap curr (pre ++ [bytesRep be fl2 res zeros2] ++ post) c)
              (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m1, fun k => dm k = true)) := by
            rw [preEq]
            simp only [List.cons_append, List.nil_append, List.append_assoc, zeros2, makeZeros]
            simp only [List.cons_append, List.nil_append, List.append_assoc, resLen] at frameAfter
            rw [frameAfter]
            rw [addrBefore1, addrBefore2] at outSep
            simpa only [frame, postBase, dstBase, midBase, srcBase, zeros2, makeZeros,
              wordSemBytesInWord, StackRemove.bytesInWord, resLen] using outSep
          have lengths := heapLength_shape (byteHeap_shape be fl2 vals2 res zeros2 pre post)
          refine ⟨?_, ?_, hm3, hm4, hm5, hm6, hm7, curr, other, ca, oa, currStore, otherStore,
            nextStore, triggerStore, endStore, lengthStore, globInv, genInv, afterSep⟩
          · simpa only [← lengths] using hm1
          · simpa only [← lengths] using hm2
      · obtain ⟨mid, postA, postEq, idxEq⟩ := heapLookup_split post _ _ after.2
        have idx1Eq : idx1 = heapLength pre + (zeros2.length + 1) + heapLength mid := by
          have hel := elLengthBytes be fl2 vals2 zeros2
          omega
        have addrAfter1 : a1 = (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
              StackRemove.bytesInWord width * BitVec.ofNat width (zeros2.length + 1)) +
              StackRemove.bytesInWord width * BitVec.ofNat width (heapLength mid) := by
          rw [sourceAddr, idx1Eq]
          simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
        let dstBase := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
        let midBase := dstBase + StackRemove.bytesInWord width * BitVec.ofNat width ((makeZeros (width := width) vals2).length + 1)
        let srcBase := midBase + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength mid)
        let postBase := srcBase + StackRemove.bytesInWord width * BitVec.ofNat width ((makeZeros (width := width) vals1).length + 1)
        let frame := SetSep.star (SetSep.star (wordHeap curr pre c) (SetSep.one (dstBase, .word (makeByteHeader c fl2 vals2.length))))
          (SetSep.star (SetSep.star (wordHeap midBase mid c) (SetSep.one (srcBase, .word (makeByteHeader c fl1 vals1.length))))
            (SetSep.star (wordHeap postBase postA c) (wordHeap other (heapExpand limit) c)))
        have inSep : SetSep.star (SetSep.star
            (Misc.wordList (a1 + wordSemBytesInWord) ((writeBytes vals1 (makeZeros vals1) be).map WordLocW.word))
            (Misc.wordList (a2 + wordSemBytesInWord) ((writeBytes vals2 (makeZeros vals2) be).map WordLocW.word))) frame
            (SetSep.fun2Set (m, fun k => dm k = true)) := by
          have sep := heapSeparated
          rw [postEq] at sep
          simp only [List.cons_append, List.nil_append, List.append_assoc, zeros2, makeZeros] at sep
          have frameEq := byteTwoHeapFrame c curr pre mid postA vals2 vals1 be fl2 fl1 (wordHeap other (heapExpand limit) c) good config2 cellBound2 lenBound2 cellBound1 lenBound1
          simp only [List.cons_append, List.nil_append, List.append_assoc] at frameEq
          rw [frameEq] at sep
          rw [destAddress, addrAfter1]
          rw [SetSep.starComm (Misc.wordList _ _) (Misc.wordList _ _)]
          simpa only [frame, postBase, srcBase, midBase, dstBase, zeros2, makeZeros, wordSemBytesInWord, StackRemove.bytesInWord] using sep
        obtain ⟨m1, outSep, run⟩ := xorBytesWordList vals1 vals2 res (a1 + wordSemBytesInWord)
          (a2 + wordSemBytesInWord) be frame m dm h good countBound2 inSep
        refine ⟨m1, ?_, ?_⟩
        · simpa [decoded] using run
        · have resLen : res.length = vals2.length := sameLen.symm
          have resCount : res.length / (width / 8) + 1 < 2 ^ (width - 4) := by simpa [resLen] using cellBound2
          have resBound : res.length / (width / 8) + 1 < 2 ^ c.lenSize := by simpa [resLen] using lenBound2
          have frameAfter := byteTwoHeapFrame c curr pre mid postA res vals1 be fl2 fl1
            (wordHeap other (heapExpand limit) c) good config2 resCount resBound cellBound1 lenBound1
          have afterSep : SetSep.star (wordHeap curr (pre ++ [bytesRep be fl2 res zeros2] ++ post) c)
              (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m1, fun k => dm k = true)) := by
            rw [postEq]
            simp only [List.cons_append, List.nil_append, List.append_assoc, zeros2, makeZeros]
            simp only [List.cons_append, List.nil_append, List.append_assoc, resLen] at frameAfter
            rw [frameAfter]
            rw [destAddress, addrAfter1] at outSep
            rw [SetSep.starComm (Misc.wordList _ _) (Misc.wordList _ _)] at outSep
            simpa only [frame, postBase, srcBase, midBase, dstBase, zeros2, makeZeros,
              wordSemBytesInWord, StackRemove.bytesInWord, resLen] using outSep
          have lengths := heapLength_shape (byteHeap_shape be fl2 vals2 res zeros2 pre post)
          refine ⟨?_, ?_, hm3, hm4, hm5, hm6, hm7, curr, other, ca, oa, currStore, otherStore,
            nextStore, triggerStore, endStore, lengthStore, globInv, genInv, afterSep⟩
          · simpa only [← lengths] using hm1
          · simpa only [← lengths] using hm2
  obtain ⟨m1, run, heapAfter⟩ := remaining
  have post := relAfterOf m1 heapAfter
  exact ⟨w1, a1, w2, a2, makeByteHeader (width := width) c fl1 vals1.length, m1, v1Eq, v2Eq, addr1, addr2, head1, member1, run, post⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
