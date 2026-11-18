module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemCopy
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StateRelation
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Correctness of the generated word-copy routine. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- The source memory-copy routine evaluates to the copied memory, preserving
the original return value and bounding its maximum stack use. The word
evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MemCopy_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memCopy_correct {width : Nat} [NeZero width] {C F : Type}
    (retVal : WordLocW width) (l1 l2 k : Nat) (a1 a2 : BitVec width)
    (state : WordSemStateFiniteExact width C F)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (result : BitVec width → WordLocW width)
    (premises : memcopy k a1 a2 memory domain = some result ∧
      state.memory = memory ∧ state.mdomain = domain ∧
      sptLookup memCopyLocation state.code = some (5, memCopyCode) ∧
      k ≤ state.clock ∧ 4 * k < 2 ^ width ∧
      WordSemStateFiniteExact.getVar 0 state = some (.loc l1 l2) ∧
      WordSemStateFiniteExact.getVar 2 state = some (.word (BitVec.ofNat width (4 * k))) ∧
      WordSemStateFiniteExact.getVar 4 state = some (.word a1) ∧
      WordSemStateFiniteExact.getVar 6 state = some (.word a2) ∧
      WordSemStateFiniteExact.getVar 8 state = some retVal) :
    ∃ stackMax,
      WordSemStateFiniteExact.evaluate memCopyCode state =
        (some (.result (.loc l1 l2) [retVal]),
          {state with clock := state.clock - k, memory := result, locals := .ln, localsSize := some 0, stackMax := stackMax}) ∧
      optionLe stackMax (Option.map₂ max state.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize state.stack) (sptLookup memCopyLocation state.stackSize))) := by
  induction k generalizing a1 a2 state memory domain result with
  | zero =>
    obtain ⟨copy, hmem, hdomain, hcode, hclock, hbound, h0, h2, h4, h6, h8⟩ := premises
    simp [memcopy] at copy
    subst result
    have zeroTest : Compiler.Encoders.Asm.wordCmpHOL .test (BitVec.ofNat width 0) (BitVec.ofNat width 0) = true := by
      change ((0 : BitVec width) &&& 0 == 0) = true
      simp
    refine ⟨state.stackMax, ?_, ?_⟩
    · simp [memCopyCode, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        wordSemWordCmp, zeroTest,
        WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.flushState, h0, h2, h8, hmem]
    · exact (optionLe_max_right _ _ _).mpr (Or.inl (optionLe_refl _))
  | succ k ih =>
    obtain ⟨copy, hmem, hdomain, hcode, hclock, hbound, h0, h2, h4, h6, h8⟩ := premises
    change sptLookup 0 state.locals = some (.loc l1 l2) at h0
    change sptLookup 2 state.locals = some (.word (BitVec.ofNat width (4 * (k + 1)))) at h2
    change sptLookup 4 state.locals = some (.word a1) at h4
    change sptLookup 6 state.locals = some (.word a2) at h6
    change sptLookup 8 state.locals = some retVal at h8
    have srcDomain : domain a1 = true := by
      cases h : domain a1 <;> simp [memcopy, h] at copy ⊢
    have destDomain : domain a2 = true := by
      cases h : domain a2 <;> simp [memcopy, h] at copy ⊢
    have copyTail : memcopy k (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        (fun key => if key = a2 then memory a1 else memory key) domain = some result := by
      simpa [memcopy, srcDomain, destDomain] using copy
    have countNonzero : (BitVec.ofNat width (4 * (k + 1))) ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound] at h
    have clockPositive : state.clock ≠ 0 := by omega
    have bitAndSelf (x : BitVec width) : x &&& x = x := by simp
    have testFalse : Compiler.Encoders.Asm.wordCmpHOL .test
        (BitVec.ofNat width (4 * (k + 1))) (BitVec.ofNat width (4 * (k + 1))) = false := by
      change ((BitVec.ofNat width (4 * (k + 1)) &&& BitVec.ofNat width (4 * (k + 1))) == 0) = false
      rw [bitAndSelf]
      have nz : BitVec.ofNat width (4 * (k + 1)) ≠ BitVec.ofNat width 0 := by
        intro eq
        apply countNonzero
        simpa using eq
      simp [nz]
    let size := sptLookup memCopyLocation state.stackSize
    let updatedMemory := fun key => if key = a2 then memory a1 else memory key
    let next := WordSemStateFiniteExact.callEnv
      [.loc l1 l2, .word (BitVec.ofNat width (4 * k)), .word (a1 + wordSemBytesInWord),
        .word (a2 + wordSemBytesInWord), retVal] size
      {state with clock := state.clock - 1, memory := updatedMemory}
    have nextPremises : memcopy k (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord)
        updatedMemory domain = some result ∧
        next.memory = updatedMemory ∧ next.mdomain = domain ∧
        sptLookup memCopyLocation next.code = some (5, memCopyCode) ∧
        k ≤ next.clock ∧ 4 * k < 2 ^ width ∧
        WordSemStateFiniteExact.getVar 0 next = some (.loc l1 l2) ∧
        WordSemStateFiniteExact.getVar 2 next = some (.word (BitVec.ofNat width (4 * k))) ∧
        WordSemStateFiniteExact.getVar 4 next = some (.word (a1 + wordSemBytesInWord)) ∧
        WordSemStateFiniteExact.getVar 6 next = some (.word (a2 + wordSemBytesInWord)) ∧
        WordSemStateFiniteExact.getVar 8 next = some retVal := by
      refine ⟨copyTail, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [next, WordSemStateFiniteExact.callEnv] using hdomain
      · simpa [next, WordSemStateFiniteExact.callEnv] using hcode
      · simp only [next, WordSemStateFiniteExact.callEnv]; omega
      · omega
      all_goals simp [next, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.getVar,
        sptFromList2, sptInsert, sptLookup]
    obtain ⟨smx, nextRun, stackBound⟩ :=
      ih (a1 + wordSemBytesInWord) (a2 + wordSemBytesInWord) next updatedMemory domain result nextPremises
    have resultEq : WordSemStateFiniteExact.evaluate memCopyCode next =
        (some (.result (.loc l1 l2) [retVal]),
          {state with clock := state.clock - (k + 1), memory := result, locals := .ln, localsSize := some 0, stackMax := smx}) := by
      simpa [next, WordSemStateFiniteExact.callEnv, Nat.sub_sub, Nat.add_comm] using nextRun
    have countSub : BitVec.ofNat width (4 * (k + 1)) - 4 = BitVec.ofNat width (4 * k) := by
      simp [Nat.mul_add, BitVec.ofNat_add]
    have countSub' : BitVec.ofNat width (4 * (k + 1)) - BitVec.ofNat width 4 = BitVec.ofNat width (4 * k) := by
      simpa using countSub
    refine ⟨smx, ?_, ?_⟩
    · simp only [memCopyCode, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm,
        WordSemStateFiniteExact.getVar, wordSemWordCmp, h2, testFalse]
      change WordSemStateFiniteExact.evaluate
        (.seq (.assign 1 (.load (.var 4)))
          (.seq (.assign 2 (.op .sub [.var 2, .const 4]))
            (.seq (.assign 4 (.op .add [.var 4, .const wordSemBytesInWord]))
              (.seq (.store (.var 6) 1)
                (.seq (.assign 6 (.op .add [.var 6, .const wordSemBytesInWord]))
                  (.call none (some memCopyLocation) [0, 2, 4, 6, 8] none)))))) state = _
      simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.memStore,
        WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, h2, h4, h6, hmem, hdomain, srcDomain, destDomain,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, theWords, wordOpHOL, wordOp]
      simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, h0, h8,
        wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode, hcode, clockPositive,
        WordSemStateFiniteExact.decClock, WordSemStateFiniteExact.callEnv,
        wordSemBadFunReturn, ← hmem]
      simp only [countSub']
      simp only [next, WordSemStateFiniteExact.callEnv, size, updatedMemory, ← hmem, hdomain] at resultEq
      rw [resultEq]
      rfl
    · change optionLe smx (Option.map₂ max state.stackMax
        (Option.map₂ (· + ·) (wordSemStackSize state.stack) size))
      simp only [next, WordSemStateFiniteExact.callEnv, size] at stackBound ⊢
      cases hstack : state.stackMax <;> cases hsize : wordSemStackSize state.stack <;>
        cases hframe : sptLookup memCopyLocation state.stackSize <;>
        simp [wordSemOptionMax, wordSemOptionAdd, hstack, hsize, hframe] at stackBound ⊢ <;>
        exact stackBound

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
