module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.Equal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordMemoryEquality

@[expose] public section

/-! Word-memory comparison code used by constant equality. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace MemEqListWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MemEqListWitness

/-- Sequence a successful assignment. Private infrastructure for the HOL proof, with no separate HOL declaration. -/
private theorem seqAssign {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (k : Nat) (e : WordLangExpHOL (BitVec width))
    (v : WordLocW width) (p : WordLangProgHOL (BitVec width))
    (read : t.wordExp e = some v) :
    WordSemStateFiniteExact.evaluate (.seq (.assign k e) p) t =
      WordSemStateFiniteExact.evaluate p (t.setVar k v) := by
  simp [WordSemStateFiniteExact.evaluate, read, WordSemStateFiniteExact.fixClock,
    WordSemStateFiniteExact.setVar]

/-- Compare at an arbitrary offset, the induction used by HOL before specialization. Private infrastructure, not a separate tagged declaration. -/
private theorem memEqGeneral {width : Nat} [NeZero width] {C F : Type}
    (xs : List (BitVec width)) (offset : BitVec width)
    (t : WordSemStateFiniteExact width C F) (b : Bool) (a : BitVec width)
    (comparison : wordMemEq (a + offset) xs t.mdomain t.memory = some b)
    (base : t.getVar 3 = some (.word a)) :
    ∃ x : WordLocW width, WordSemStateFiniteExact.evaluate (memEqList offset xs) t =
      (none, {t with locals := (if b then sptInsert 1 (.word 18) else id) ((if xs ≠ [] then sptInsert 5 x else id) t.locals)}) := by
  induction xs generalizing offset t b with
  | nil =>
    simp [wordMemEq] at comparison
    subst b
    refine ⟨.word 0, ?_⟩
    simp [memEqList, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.setVar]
  | cons w ws ih =>
    cases dm : t.mdomain (a + offset) with
    | false => simp [wordMemEq, dm] at comparison
    | true =>
      cases mm : t.memory (a + offset) with
      | loc x y => simp [wordMemEq, dm, mm] at comparison
      | word value =>
        have load : t.wordExp (.load (.op .add [.var 3, .const offset])) = some (.word value) := by
          simp [WordSemStateFiniteExact.wordExp, base, theWords, wordOpHOL, wordOp,
            WordSemStateFiniteExact.memLoad, dm, mm]
        simp only [memEqList]
        rw [seqAssign t 5 _ (.word value) _ load]
        let next := t.setVar 5 (.word value)
        change ∃ x : WordLocW width, WordSemStateFiniteExact.evaluate (.ite .equal 5 (.imm w) _ _) next = _
        have found : next.getVar 5 = some (.word value) := by
          simp [next, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar, sptLookup_sptInsert_same]
        by_cases eq : value = w
        · subst value
          have cmp : wordMemEq (a + (offset + wordSemBytesInWord)) ws next.mdomain next.memory = some b := by
            simpa [wordMemEq, dm, mm, next, WordSemStateFiniteExact.setVar,
              wordSemBytesInWord, StackRemove.bytesInWord, BitVec.add_assoc] using comparison
          have baseNext : next.getVar 3 = some (.word a) := by
            simpa [next, WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.getVar,
              sptLookup_sptInsert_ne] using base
          obtain ⟨last, run⟩ := ih (offset + wordSemBytesInWord) next b cmp baseNext
          rw [WordSemStateFiniteExact.evaluate]
          simp only [found, WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
            Compiler.Encoders.Asm.wordCmpHOL, beq_self_eq_true]
          cases ws with
          | nil =>
            refine ⟨.word w, ?_⟩
            simpa [next, WordSemStateFiniteExact.setVar] using run
          | cons h tail =>
            refine ⟨last, ?_⟩
            simpa [next, WordSemStateFiniteExact.setVar, sptInsert_insert_shadow] using run
        · have falseB : b = false := by simpa [wordMemEq, dm, mm, eq] using comparison.symm
          subst b
          refine ⟨.word value, ?_⟩
          have neq : (value == w) = false := beq_eq_false_iff_ne.mpr eq
          rw [WordSemStateFiniteExact.evaluate, found]
          simp [WordSemStateFiniteExact.getVarImm, wordSemWordCmp,
            Compiler.Encoders.Asm.wordCmpHOL, neq, next, WordSemStateFiniteExact.evaluate,
            WordSemStateFiniteExact.setVar]

/-- Generated comparison code implements the complete word-memory comparison.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MemEqList_thm" 12206
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem memEqList_correct {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (xs : List (BitVec width)) (b : Bool) (a : BitVec width)
    (h : wordMemEq a xs t.mdomain t.memory = some b ∧ t.getVar 3 = some (.word a)) :
    ∃ x : WordLocW width, WordSemStateFiniteExact.evaluate (memEqList 0 xs) t =
      (none, {t with locals := (if b then sptInsert 1 (.word 18) else id) ((if xs ≠ [] then sptInsert 5 x else id) t.locals)}) := by
  apply memEqGeneral xs 0 t b a
  · simpa using h.1
  · exact h.2
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
