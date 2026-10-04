import Mathlib.Tactic.NormNum
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StackMemoryAny
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreTransfers
namespace Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local extraction of bounded bitmap reads from the original full
separated heap. No target load or domain fact is supplied as a premise. -/
theorem bitmapReads {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ bitmapWord : BitVec width,
      source.store.lookup .bitmapBase = some (.word bitmapWord) ∧
      ∀ (index : Nat) (bound : index < source.bitmaps.length),
        StackSemStateOps.memLoad ((bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width index) target =
          some (.word source.bitmaps[index]) := by
  have validWord := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heaps⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  cases lookup : source.store.lookup .bitmapBase with
  | none => simp [lookup, isSomeWord] at validWord
  | some value =>
    cases value with
    | loc first second => simp [lookup, isSomeWord, wordLocWToGeneric] at validWord
    | word bitmapWord =>
      refine ⟨bitmapWord, rfl, ?_⟩
      intro index bound
      rcases heaps with ⟨heap4, heapStack, part4, assertion4, stack⟩
      rcases assertion4 with ⟨heap3, heapStore, part3, assertion3, store⟩
      rcases assertion3 with ⟨heap2, heapBuffer, part2, assertion2, buffer⟩
      rcases assertion2 with ⟨heapMemory, heapBitmap, part1, memory, bitmap⟩
      simp only [lookup, Option.map_some, wordLocWToGeneric, theSomeWord] at bitmap
      have combinedBound : index < ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word).length := by
        simp only [List.length_map, List.length_append]
        omega
      have member := StackHeap.wordListNth (bitmapWord <<< wordShiftAmount width)
        ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word) heapBitmap index combinedBound bitmap
      have entry : ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)[index] = .word source.bitmaps[index] := by
        simp only [List.getElem_map, List.getElem_append_left bound]
      rw [entry] at member
      have targetMember : SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)
          ((bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width index, .word source.bitmaps[index]) := by
        rw [← part4.1, ← part3.1, ← part2.1, ← part1.1]
        exact Or.inl (Or.inl (Or.inl (Or.inr member)))
      have facts := (SetSep.fun2SetThm target.memory (fun address => target.mdomain address = true)
        _ (.word source.bitmaps[index])).mp targetMember
      simp only [StackSemStateOps.memLoad, facts.1, facts.2, ite_true]

/-- Factoring of the original native BitmapLoad instruction sequence;
the full constructor derives all target lookup/read premises. -/
theorem runBitmap {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (base bitmapWord word entry : BitVec width)
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (indexLookup : state.regs.lookup index = some (.word word))
    (different : index ≠ register)
    (firstRead : StackSemStateOps.memLoad (base + storeOffset .bitmapBase) state = some (.word bitmapWord))
    (finalRead : StackSemStateOps.memLoad ((bitmapWord + word) <<< wordShiftAmount width) state = some (.word entry))
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.bitmapLoad register index), state) =
      (none, StackSemStateOps.setVar register (.word entry) state) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have maps (first second : WordLocW width) :
      (state.regs.updateEq (register, first)).updateEq (register, second) = state.regs.updateEq (register, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  have firstFacts : state.mdomain (base + storeOffset .bitmapBase) = true ∧
      state.memory (base + storeOffset .bitmapBase) = .word bitmapWord := by
    by_cases domain : state.mdomain (base + storeOffset .bitmapBase) = true
    · exact ⟨domain, Option.some.inj (by simpa [StackSemStateOps.memLoad, domain] using firstRead)⟩
    · simp [StackSemStateOps.memLoad, domain] at firstRead
  have finalReadNormalized : StackSemStateOps.memLoad
      ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) state = some (.word entry) := by
    simpa using finalRead
  have finalFacts : state.mdomain ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = true ∧
      state.memory ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = .word entry := by
    by_cases domain : state.mdomain ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = true
    · exact ⟨domain, Option.some.inj (by simpa [StackSemStateOps.memLoad, domain] using finalReadNormalized)⟩
    · simp [StackSemStateOps.memLoad, domain] at finalReadNormalized
  simp [comp, listSeqHOL, StackSemEvaluate.evaluate_seq, addInst, leftShiftInst,
    StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, baseLookup, indexLookup,
    StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    different, wordOpHOL, wordOp, wordShiftHOL,
    StackSemControl.fixClock, BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound,
    Nat.not_le_of_gt shiftWidth, maps, StackSemStateOps.memLoad, firstFacts.1, firstFacts.2, finalFacts.1, finalFacts.2]

/-- Full original BitmapLoad constructor, retaining all original guards and
four premises. Target reads are derived from the full separated source heap. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBitmapLoad {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.bitmapLoad register index : HolProg width) pointer) :
    ∃ clock postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.bitmapLoad register index),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_bitmapLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_or] at sourceRun
  by_cases same : register = index
  · simp only [same, beq_self_eq_true, if_true] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] at sourceRun
    cases lookup : StackSemStateOps.getVar index source with
    | none =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      cases value with
      | loc first second =>
        rw [lookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [lookup] at sourceRun
        simp only [] at sourceRun
        by_cases outsideBounds : source.bitmaps.length ≤ word.toNat
        · rw [dif_pos outsideBounds] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        · rw [dif_neg outsideBounds] at sourceRun
          have resultEq := (Prod.mk.inj sourceRun).1.symm
          have sourceEq := (Prod.mk.inj sourceRun).2.symm
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, reads⟩ := bitmapReads jump bounds pointer source target relation
          obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact lookup
          have addressEq : (bitmapWord + word) <<< wordShiftAmount width =
              (bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width word.toNat := by
            simp only [BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm word]
          have bound : word.toNat < source.bitmaps.length := by omega
          have read := reads word.toNat bound
          rw [← addressEq] at read
          refine ⟨0, StackSemStateOps.setVar register (.word source.bitmaps[word.toNat]) target, ?_, ?_⟩
          · simp only [Nat.zero_add]
            have execution := runBitmap target register index pointer base bitmapWord word source.bitmaps[word.toNat]
              baseLookup targetIndex (Ne.symm same) firstRead read good
            simpa only [comp] using execution
          · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
              (.word source.bitmaps[word.toNat]) source target ⟨relation, lower.1⟩
end Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap
