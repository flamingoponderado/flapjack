import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Bitmap
import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyLoop
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemorySubset
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreConsts
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
/-- Flapjack-only native macro-prefix equation. The reads and load are local
facts to be derived from the original full source relation. -/
theorem prepareBitmap {width : Nat} [NeZero width] {C F : Type}
    (bitmap pointer : Nat) (base bitmapWord index : BitVec width)
    (target : StackSemStateFiniteExact width C F)
    (baseRead : target.regs.lookup (pointer + 1) = some (.word base))
    (indexRead : target.regs.lookup 1 = some (.word index))
    (different : bitmap ≠ 1)
    (firstRead : memLoad (base + storeOffset .bitmapBase) target = some (.word bitmapWord))
    (good : goodDimindex width) :
    evaluate (listSeqHOL [.inst (.mem .load bitmap
      (.addr (pointer + 1) (storeOffset .bitmapBase))),
      addInst bitmap 1, leftShiftInst bitmap (wordShiftAmount width)], target) =
      (none, setVar bitmap (.word ((bitmapWord + index) <<< wordShiftAmount width)) target) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have maps (first second : WordLocW width) :
      (target.regs.updateEq (bitmap, first)).updateEq (bitmap, second) =
      target.regs.updateEq (bitmap, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = bitmap <;>
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  have firstFacts : target.mdomain (base + storeOffset .bitmapBase) = true ∧
      target.memory (base + storeOffset .bitmapBase) = .word bitmapWord := by
    by_cases domain : target.mdomain (base + storeOffset .bitmapBase) = true
    · exact ⟨domain, Option.some.inj (by simpa [memLoad, domain] using firstRead)⟩
    · simp [memLoad, domain] at firstRead
  simp [listSeqHOL, evaluate_seq, addInst, leftShiftInst,
    evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, baseRead, indexRead,
    setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm different,
    wordOpHOL, wordOp, wordShiftHOL, StackSemControl.fixClock,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound, Nat.not_le_of_gt shiftWidth,
    maps, memLoad, firstFacts.1, firstFacts.2]
/-- The untouched bitmap-buffer/store/stack frame in the original StoreConsts
case. This local factoring is not an independent HOL definition. -/
def copyFrame {width : Nat} [NeZero width] {C F : Type}
    (base bitmapBase : BitVec width) (source : StackSemStateFiniteExact width C F) :
    ((BitVec width × WordLocW width) → Prop) → Prop :=
  SetSep.star
    (SetSep.star
      (SetSep.star
        (Misc.wordList (bitmapBase + bytesInWord width * BitVec.ofNat width source.bitmaps.length)
          (source.dataBuffer.buffer.map WordLocW.word))
        (Misc.wordListExists
          (bitmapBase + bytesInWord width * BitVec.ofNat width
            (source.bitmaps ++ source.dataBuffer.buffer).length) source.dataBuffer.spaceLeft))
      (wordStoreHOL base source.store))
    (Misc.wordList base source.stack)

/-- Exact separation rearrangement used on both sides of the original copy
transition. Local infrastructure; no independent HOL declaration is claimed. -/
theorem copyHeapShape {width : Nat} [NeZero width] {C F : Type}
    (base bitmapBase : BitVec width) (source : StackSemStateFiniteExact width C F)
    (memory : BitVec width → WordLocW width) :
    SetSep.star
      (SetSep.star
        (SetSep.star
          (SetSep.star (memoryHOL memory (fun key => source.mdomain key = true))
            (Misc.wordList bitmapBase
              ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)))
          (Misc.wordListExists
            (bitmapBase + bytesInWord width * BitVec.ofNat width
              (source.bitmaps ++ source.dataBuffer.buffer).length) source.dataBuffer.spaceLeft))
        (wordStoreHOL base source.store))
      (Misc.wordList base source.stack) =
    SetSep.star (SetSep.star
      (Misc.wordList bitmapBase (source.bitmaps.map WordLocW.word))
      (copyFrame base bitmapBase source))
      (memoryHOL memory (fun key => source.mdomain key = true)) := by
  simp only [copyFrame, List.map_append, StackHeap.wordListAppend, List.length_map,
    ← SetSep.starAssoc]
  rw [SetSep.starComm (memoryHOL memory (fun key => source.mdomain key = true))]
  simp only [← SetSep.starAssoc]

/-- Local full-relation memory transition. Its separated post-heap is derived
by CopyLoop in the constructor proof; no independent HOL declaration is claimed. -/
theorem stateRelCopiedMemory {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (base : BitVec width)
    (sourceMemory targetMemory : BitVec width → WordLocW width)
    (relation : stateRelHOL jump bounds pointer source target)
    (baseRead : target.regs.lookup (pointer + 1) = some (.word base))
    (newHeap : SetSep.star (SetSep.star
      (Misc.wordList
        (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
        (source.bitmaps.map WordLocW.word))
      (copyFrame base
        (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width) source))
      (memoryHOL sourceMemory (fun key => source.mdomain key = true))
      (SetSep.fun2Set (targetMemory, fun key => target.mdomain key = true))) :
    stateRelHOL jump bounds pointer {source with memory := sourceMemory}
      {target with memory := targetMemory} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,?_⟩
  simp only [baseRead] at h25 ⊢
  refine ⟨h25.1, h25.2.1, h25.2.2.1, h25.2.2.2.1, ?_⟩
  rw [copyHeapShape]
  exact newHeap

/-- Local native sequencing of the original macro prefix and suffix. The
prefix execution is derived by prepareBitmap in the full constructor proof. -/
theorem macroAfterPrepare {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer temporary bitmap : Nat)
    (stub : Option Nat) (target prepared : StackSemStateFiniteExact width C F)
    (prefixRun : evaluate (listSeqHOL [.inst (.mem .load bitmap
      (.addr (pointer + 1) (storeOffset .bitmapBase))),
      addInst bitmap 1, leftShiftInst bitmap (wordShiftAmount width)], target) =
      (none, prepared)) :
    evaluate (comp jump bounds pointer (.storeConsts temporary bitmap stub), target) =
      evaluate (listSeqHOL [copyLoop temporary bitmap, moveInst temporary 1,
        moveInst bitmap 1], prepared) := by
  simp only [comp, listSeqHOL]
  rw [CopyLoopProof.sequenceAssoc, CopyLoopProof.sequenceAssoc,
    evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rw [← CopyLoopProof.sequenceAssoc]
  change evaluate (.seq (.inst (.mem .load bitmap
    (.addr (pointer + 1) (storeOffset .bitmapBase))))
    (.seq (addInst bitmap 1) (leftShiftInst bitmap (wordShiftAmount width))), target) =
    (none, prepared) at prefixRun
  rw [prefixRun]

/-- Local native final moves, derived from the CopyLoop register-one result. -/
theorem finishMoves {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (target : StackSemStateFiniteExact width C F)
    (distinct : temporary ≠ 1) (read : getVar 1 target = some (.word 1)) :
    evaluate (listSeqHOL [moveInst temporary 1, moveInst bitmap 1], target) =
      (none, setVar bitmap (.word 1) (setVar temporary (.word 1) target)) := by
  change target.regs.lookup 1 = _ at read
  simp [listSeqHOL, moveInst, moveHOL, evaluate_seq, evaluate_inst,
    StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm distinct,
    read, StackSemControl.fixClock]


/-- Canonical codec of the actual imported evaluator state. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

set_option linter.unusedSimpArgs false in
/-- Full original StoreConsts constructor case (1504–1575), with the original
four premises and arbitrary temporary/bitmap registers and optional stub.
Source success excludes allocation/error branches and supplies the distinct
registers and actual copy result. The target bitmap load, full CopyLoop run,
clock allowance, final moves and entire framed post-relation are derived.
The evaluator closure inherits the reviewed reals_as_rational_cuts FP carrier
(SOUNDNESS item 8); this constructor executes no FP instruction. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "comp_correct"
  (fmap_as_finite_support_relation := [StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem compCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (stub : Option Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.storeConsts temporary bitmap stub, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.storeConsts temporary bitmap stub : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.storeConsts temporary bitmap stub),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change 3 < pointer ∧ temporary < pointer ∧ bitmap < pointer at bound
  have notAlloc : source.useAlloc = false := relation.2.2.2.2.2.1
  rw [evaluate_storeConsts] at sourceRun
  rw [if_neg (by simp [relation.2.1])] at sourceRun
  cases stub with
  | some label =>
    simp only [notAlloc, Bool.false_eq_true, not_false_eq_true,
      Option.isSome_some, and_self, if_true] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, and_false, if_false,
      StackSemStoreConstsGuard.checkStoreConstsOpt, not_true_eq_false] at sourceRun
    unfold StackSemStoreConsts.storeConstSem at sourceRun
    split at sourceRun
    next invalid => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    next distinct =>
      have distinct : [0, 1, 2, 3, temporary, bitmap].Nodup := by simpa only [not_not] using distinct
      split at sourceRun
      next _ _ _ index address offset read1 read2 read3 =>
        cases copySource : StackSemStoreConsts.copyWordsExact index.toNat address offset
            source.bitmaps (fun key => source.mdomain key = true) source.memory with
        | none =>
          simp only [copySource] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | some output =>
          rcases output with ⟨finalAddress, finalMemory⟩
          simp only [copySource] at sourceRun
          rw [if_neg (by simp [notAlloc])] at sourceRun
          simp only [id_eq] at sourceRun
          have loopDistinct : [1, 2, 3, temporary, bitmap].Nodup :=
            (List.nodup_cons.mp distinct).2
          have bOne : bitmap ≠ 1 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have bTwo : bitmap ≠ 2 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have bThree : bitmap ≠ 3 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tOne : temporary ≠ 1 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tTwo : temporary ≠ 2 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tb : temporary ≠ bitmap := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, _⟩ := Bitmap.bitmapReads jump bounds pointer source target relation
          obtain ⟨base, baseRead, _reserve, _upper, _pointerRead, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup 1 = some (.word index) := by
            change getVar 1 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 1 source target ⟨relation, by omega⟩]
            exact read1
          have targetAddress : target.regs.lookup 2 = some (.word address) := by
            change getVar 2 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 2 source target ⟨relation, by omega⟩]
            exact read2
          have targetOffset : target.regs.lookup 3 = some (.word offset) := by
            change getVar 3 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 3 source target ⟨relation, by omega⟩]
            exact read3
          let bitmapBase := bitmapWord <<< wordShiftAmount width
          let prepared := setVar bitmap (.word ((bitmapWord + index) <<< wordShiftAmount width)) target
          have addressEq : (bitmapWord + index) <<< wordShiftAmount width =
              bitmapBase + bytesInWord width * BitVec.ofNat width index.toNat := by
            simp only [bitmapBase, BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift index good, BitVec.mul_comm index]
          have preparedReads : getVar 2 prepared = some (.word address) ∧
              getVar 3 prepared = some (.word offset) ∧
              getVar bitmap prepared = some (.word
                (bitmapBase + bytesInWord width * BitVec.ofNat width index.toNat)) := by
            simp [prepared, getVar, setVar, HolFiniteMapExact.lookup_updateEq,
              FUPDATE_HOL, Ne.symm bTwo, Ne.symm bThree, targetAddress, targetOffset, addressEq]
          rw [copyHeapShape] at heap
          have copyHeap : SetSep.star
              (SetSep.star (Misc.wordList bitmapBase (source.bitmaps.map WordLocW.word))
                (copyFrame base bitmapBase source))
              (memoryHOL source.memory (fun key => source.mdomain key = true))
              (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true)) := by
            simpa only [bitmapLookup, Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBase] using heap
          have subset := memoryFun2SetSubset source.memory target.memory
            (fun key => source.mdomain key = true) (fun key => target.mdomain key = true)
            (SetSep.star (Misc.wordList bitmapBase (source.bitmaps.map WordLocW.word))
              (copyFrame base bitmapBase source))
            (by rw [SetSep.starComm]; exact copyHeap)
          obtain ⟨allowance, unchanged, value, nextBitmap, targetMemory, copyRun, finalHeap⟩ :=
            CopyLoopProof.copyLoopThm temporary bitmap index.toNat 0 address offset finalAddress bitmapBase
              source.bitmaps (fun key => source.mdomain key = true)
              (fun key => target.mdomain key = true) source.memory finalMemory
              (copyFrame base bitmapBase source) prepared
              ⟨copySource, loopDistinct, rfl, good, subset,
                preparedReads.1, preparedReads.2.1, preparedReads.2.2, copyHeap⟩
          let copied : StackSemStateFiniteExact width C F :=
            {prepared with memory := targetMemory, regs := (((if unchanged then prepared.regs else prepared.regs.updateEq (temporary, .word value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word nextBitmap)}
          change evaluate (copyLoop temporary bitmap,
            {prepared with clock := prepared.clock + allowance}) = (none, copied) at copyRun
          have memoryRel := stateRelCopiedMemory jump bounds pointer source target base
            finalMemory targetMemory relation baseRead
            (by simpa only [bitmapLookup, Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBase] using finalHeap)
          have prefixRun := prepareBitmap bitmap pointer base bitmapWord index
            {target with clock := allowance + target.clock} baseRead targetIndex bOne firstRead good
          have prefixState : setVar bitmap (.word ((bitmapWord + index) <<< wordShiftAmount width))
              {target with clock := allowance + target.clock} =
              {prepared with clock := prepared.clock + allowance} := by
            simp only [prepared, setVar, Nat.add_comm]
          rw [prefixState] at prefixRun
          have copiedRead : getVar 1 copied = some (.word 1) := by
            simp [copied, getVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm bOne]
          let postTarget := setVar temporary (.word 1) (setVar bitmap (.word 1)
            (setVar 1 (.word 1) (setVar 2 (.word finalAddress) {target with memory := targetMemory})))
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          refine ⟨allowance, postTarget, ?_, ?_⟩
          · rw [macroAfterPrepare jump bounds pointer temporary bitmap none
              {target with clock := allowance + target.clock}
              {prepared with clock := prepared.clock + allowance} prefixRun]
            change evaluate (.seq (copyLoop temporary bitmap)
              (listSeqHOL [moveInst temporary 1, moveInst bitmap 1]), _) = _
            rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
            simp only [copyRun]
            rw [finishMoves temporary bitmap copied tOne copiedRead]
            dsimp only [postTarget, copied, prepared, setVar]
            congr 2
            apply HolFiniteMapExact.ext_lookup
            intro query
            cases unchanged <;>
              by_cases qBitmap : query = bitmap <;>
              by_cases qOne : query = 1 <;>
              by_cases qTwo : query = 2 <;>
              by_cases qTemporary : query = temporary <;>
              simp [qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb, bOne, bTwo,
                Ne.symm tOne, Ne.symm tTwo, Ne.symm tb, Ne.symm bOne, Ne.symm bTwo,
                HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · exact StateUpdates.stateRelSetVar jump bounds pointer temporary (.word 1) _ _
              ⟨StateUpdates.stateRelSetVar jump bounds pointer bitmap (.word 1) _ _
                ⟨StateUpdates.stateRelSetVar jump bounds pointer 1 (.word 1) _ _
                  ⟨StateUpdates.stateRelSetVar jump bounds pointer 2 (.word finalAddress) _ _
                    ⟨memoryRel, by omega⟩, by omega⟩, bound.2.2⟩, bound.2.1⟩
      next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)

end Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreConsts
