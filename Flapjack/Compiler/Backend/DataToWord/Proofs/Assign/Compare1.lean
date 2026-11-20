module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.RealAddrInsert
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CompareLoop
public import Flapjack.Compiler.Backend.DataToWord.Stubs
@[expose] public section

/-! Correctness of the word-comparison runtime loop. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Compare1Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end Compare1Witness

/-- The comparison stub evaluates a successful word comparison within its clock and stack bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "Compare1_code_thm"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem compare1Code_correct {width : Nat} [NeZero width] {C F : Type}
    (len a1 a2 : BitVec width) (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width)
    (res : BitVec width) (t : WordSemStateFiniteExact width C F) (l1 l2 : Nat)
    (loop : wordCmpLoop len a1 a2 domain memory = some res)
    (dom : domain = t.mdomain) (mem : memory = t.memory)
    (code : sptLookup compare1Location t.code = some (4, compare1Code))
    (size : sptLookup compare1Location t.stackSize = t.localsSize)
    (r0 : t.getVar 0 = some (.loc l1 l2)) (r2 : t.getVar 2 = some (.word len))
    (r4 : t.getVar 4 = some (.word a1)) (r6 : t.getVar 6 = some (.word a2))
    (clock : len.toNat ≤ t.clock) :
    ∃ ck smx, WordSemStateFiniteExact.evaluate compare1Code t =
      (some (.result (.loc l1 l2) [.word res]), {t with clock := ck, locals := .ln, localsSize := some 0, stackMax := smx}) ∧
      optionLe smx (Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize)) ∧
      t.clock ≤ len.toNat + ck := by
  induction hn : len.toNat using Nat.strong_induction_on generalizing len a1 a2 t res with
  | h n ih =>
    by_cases zero : len = 0
    · subst len
      simp [wordCmpLoop] at loop
      subst res
      refine ⟨t.clock, t.stackMax, ?_, ?_, by simp⟩
      · simp only [WordSemStateFiniteExact.getVar] at r0 r2
        simp [compare1Code, wordListSeq, WordSemStateFiniteExact.evaluate,
          WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
          WordSemStateFiniteExact.flushState, WordSemStateFiniteExact.fixClock,
          WordSemStateFiniteExact.getVars, wordSemWordCmp, Encoders.Asm.wordCmpHOL,
          sptLookup_sptInsert_same, sptLookup_sptInsert_ne, r0, r2]
      · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
    · rw [wordCmpLoop] at loop
      simp only [zero, ↓reduceIte] at loop
      by_cases inDomain : domain a1 = true ∧ domain a2 = true
      · simp only [inDomain] at loop
        cases ha : memory a1 with
        | loc x y => simp [ha] at loop
        | word x =>
          cases hb : memory a2 with
          | loc x y => simp [ha, hb] at loop
          | word y =>
            simp only [ha, hb] at loop
            by_cases equal : x = y
            · subst y
              simp only [and_self, ↓reduceIte] at loop
              have d1 : t.mdomain a1 = true := by simpa [dom] using inDomain.1
              have d2 : t.mdomain a2 = true := by simpa [dom] using inDomain.2
              have m1 : t.memory a1 = .word x := by simpa [mem] using ha
              have m2 : t.memory a2 = .word x := by simpa [mem] using hb
              have zbeq : (len == BitVec.ofNat width 0) = false := by
                apply beq_eq_false_iff_ne.mpr
                simpa using zero
              have ltcount : (len - 1).toNat < len.toNat := WordGcFunctions.bitVec_toNat_sub_one_lt zero
              have positive : 0 < t.clock := by omega
              let entry : WordSemStateFiniteExact width C F :=
                { t with
                  locals := sptFromList2 [.loc l1 l2, .word (len - 1),
                    .word (a1 - StackRemove.bytesInWord width), .word (a2 - StackRemove.bytesInWord width)]
                  clock := t.clock - 1
                  stackMax := wordSemOptionMax t.stackMax (wordSemOptionAdd (wordSemStackSize t.stack) t.localsSize) }
              have bound : (len - 1).toNat ≤ entry.clock := by
                change (len - 1).toNat ≤ t.clock - 1
                omega
              have read0 : entry.getVar 0 = some (.loc l1 l2) := by
                simp [entry, WordSemStateFiniteExact.getVar, sptFromList2, sptLookup_sptInsert_ne, sptLookup]
              have read2 : entry.getVar 2 = some (.word (len - 1)) := by
                simp [entry, WordSemStateFiniteExact.getVar, sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
              have read4 : entry.getVar 4 = some (.word (a1 - StackRemove.bytesInWord width)) := by
                simp [entry, WordSemStateFiniteExact.getVar, sptFromList2, sptLookup_sptInsert_ne, sptLookup_sptInsert_same]
              have read6 : entry.getVar 6 = some (.word (a2 - StackRemove.bytesInWord width)) := by
                simp [entry, WordSemStateFiniteExact.getVar, sptFromList2, sptLookup_sptInsert_same]
              obtain ⟨ck, smx, eval, stackBound, clockBound⟩ :=
                ih (len - 1).toNat (by omega) (len - 1) (a1 - StackRemove.bytesInWord width)
                  (a2 - StackRemove.bytesInWord width) res entry loop (by simpa [entry] using dom)
                  (by simpa [entry] using mem) (by simpa [entry] using code) (by simpa [entry] using size)
                  read0 read2 read4 read6 bound rfl
              refine ⟨ck, smx, ?_, ?_, ?_⟩
              · simp only [WordSemStateFiniteExact.getVar] at r0 r2 r4 r6
                simp only [entry, StackRemove.bytesInWord] at eval
                have oneEq : (BitVec.ofNat width 1) = (1 : BitVec width) := by rfl
                rw [← oneEq] at eval
                rw [compare1Code, wordListSeq]
                simp [wordListSeq, WordSemStateFiniteExact.evaluate,
                  WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
                  WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.setVar,
                  WordSemStateFiniteExact.getVar,
                  WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVars,
                  wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_same,
                  wordOpHOL, wordOp, theWords, wordSemBadDestArgs, wordSemAddRetLoc, wordSemFindCode,
                  WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock, size,
                  sptLookup_sptInsert_ne, r0, r2, r4, r6, zbeq, d1, d2, m1, m2, code,
                  show t.clock ≠ 0 by omega, eval, wordSemBadFunReturn]
              · change optionLe smx (Option.map₂ max
                  (wordSemOptionMax t.stackMax (wordSemOptionAdd (wordSemStackSize t.stack) t.localsSize))
                  (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize)) at stackBound
                have opt : Option.map₂ max
                    (wordSemOptionMax t.stackMax (wordSemOptionAdd (wordSemStackSize t.stack) t.localsSize))
                    (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize) =
                    Option.map₂ max t.stackMax (Option.map₂ (· + ·) (wordSemStackSize t.stack) t.localsSize) := by
                  cases t.stackMax <;> cases wordSemStackSize t.stack <;> cases t.localsSize <;>
                    simp [wordSemOptionMax, wordSemOptionAdd]
                simpa [opt] using stackBound
              · change t.clock - 1 ≤ (len - 1).toNat + ck at clockBound
                omega
            · simp only [equal, ↓reduceIte] at loop
              have d1 : t.mdomain a1 = true := by simpa [dom] using inDomain.1
              have d2 : t.mdomain a2 = true := by simpa [dom] using inDomain.2
              have m1 : t.memory a1 = .word x := by simpa [mem] using ha
              have m2 : t.memory a2 = .word y := by simpa [mem] using hb
              have zbeq : (len == 0) = false := beq_eq_false_iff_ne.mpr zero
              have zbeq2 : (len == BitVec.ofNat width 0) = false := by
                apply beq_eq_false_iff_ne.mpr
                simpa using zero
              have xbeq : (x == y) = false := beq_eq_false_iff_ne.mpr equal
              by_cases lt : x < y
              · simp [lt] at loop
                subst res
                refine ⟨t.clock, t.stackMax, ?_, ?_, by omega⟩
                · simp only [WordSemStateFiniteExact.getVar] at r0 r2 r4 r6
                  simp [compare1Code, wordListSeq, WordSemStateFiniteExact.evaluate,
                    WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.setVar,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.flushState,
                    WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVars,
                    wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_same,
                    sptLookup_sptInsert_ne, r0, r2, r4, r6, zbeq2, xbeq, d1, d2, m1, m2, lt]
                · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
              · simp [lt] at loop
                subst res
                refine ⟨t.clock, t.stackMax, ?_, ?_, by omega⟩
                · simp only [WordSemStateFiniteExact.getVar] at r0 r2 r4 r6
                  simp [compare1Code, wordListSeq, WordSemStateFiniteExact.evaluate,
                    WordSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.wordExp,
                    WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.setVar,
                    WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.flushState,
                    WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVars,
                    wordSemWordCmp, Encoders.Asm.wordCmpHOL, sptLookup_sptInsert_same,
                    sptLookup_sptInsert_ne, r0, r2, r4, r6, zbeq2, xbeq, d1, d2, m1, m2, lt]
                · exact (optionLe_max_right _ _ _).2 (Or.inl (optionLe_refl _))
      · simp [inDomain] at loop
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
