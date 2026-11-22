module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.MemoryLemmas
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumImp

@[expose] public section

/-! Loading the header and first payload word of a bignum in the data-to-word assignment proof. -/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace LoadBignumWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end LoadBignumWitness

/-- `LoadBignum` reads the header and the first payload word of a related bignum.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_LoadBignum"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_loadBignum {width : Nat} [NeZero width] {C F : Type} (c : Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (t : WordSemStateFiniteExact width C F) (i : Int) (v : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (src header w1 : Nat)
    (h : memoryRel c be ts refs sp t.store t.memory t.mdomain ((.number i, v) :: vars) ∧
      ¬ smallInt width i ∧ goodDimindex width ∧ shiftLength c < width ∧
      WordSemStateFiniteExact.getVar src t = some v ∧ header ≠ w1) :
    ∃ (hd : BitVec width) (junk : WordLocW width),
      WordSemStateFiniteExact.evaluate (loadBignum c header w1 src) t =
        (none, WordSemStateFiniteExact.setVars [w1, header, w1]
          [.word (BitVec.ofNat width i.natAbs), .word hd, junk] t) ∧
      ((16 &&& hd) = 0 ↔ 0 ≤ i) := by
  obtain ⟨rel, notSmall, good, shift, hv, hne⟩ := h
  obtain ⟨w, x, a, hloc, -, haddr, hdom, hmem, -, hdom1, hmem1, sign⟩ :=
    memoryRel_number_bignumImp c be ts refs sp t.store t.memory t.mdomain i v vars
      ⟨rel, notSmall, good⟩
  subst hloc
  have hreal := Bignum.getRealAddr_lemma c src t w a ⟨shift, good, hv, haddr⟩
  have hbytes : (wordSemBytesInWord : BitVec width) = StackRemove.bytesInWord width := rfl
  rw [hbytes] at hdom1 hmem1
  refine ⟨x, .word a, ?_, ?_⟩
  · have read1 : sptLookup w1 (sptInsert header (WordLocW.word x)
        (sptInsert w1 (WordLocW.word a) t.locals)) = some (.word a) := by
      rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hne), sptLookup_sptInsert_same]
    simp only [loadBignum]
    generalize (realAddr c src : WordLangExpHOL (BitVec width)) = e at hreal ⊢
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp, hreal,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.setVars, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.memLoad, theWords, wordOpHOL, wordOp, hbytes, hdom, hmem, hdom1, hmem1,
      WordSemStateFiniteExact.fixClock, sptLookup_sptInsert_same, read1,
      LoopSemStateFiniteExact.sptAlistInsert]
  · simpa [BitVec.and_comm] using sign
