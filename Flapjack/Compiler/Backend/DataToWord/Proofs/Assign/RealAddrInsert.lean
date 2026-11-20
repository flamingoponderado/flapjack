module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.EqualStack
@[expose] public section

/-! Real-address expression preservation for comparison-code correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
set_option maxRecDepth 8192
namespace RealAddrInsertWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end RealAddrInsertWitness

/-- Real-address expressions are unaffected by insertions at unrelated registers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_insert"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExp_realAddr_insert {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (t : WordSemStateFiniteExact width C F) (m n n1 : Nat) (w w1 : WordLocW width) :
    (m ≠ n → WordSemStateFiniteExact.wordExp {t with locals := sptInsert n w t.locals} (realAddr conf m) =
      WordSemStateFiniteExact.wordExp t (realAddr conf m)) ∧
    (m ∉ ({n, n1} : Finset Nat) →
      WordSemStateFiniteExact.wordExp {t with locals := sptInsert n w (sptInsert n1 w1 t.locals)} (realAddr conf m) =
        WordSemStateFiniteExact.wordExp t (realAddr conf m)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  constructor <;> intro h <;>
    simp only [realAddr] <;> split_ifs <;>
    simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.getStore, sptLookup_sptInsert_ne, *]
/-- Disjunction is equivalent to the corresponding implication. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP"]
theorem orIffNotImp (b1 b2 : Prop) : (b1 ∨ b2) ↔ (¬b1 → b2) := by
  classical
  tauto

/-- A real-address expression evaluates when the heap base and input are words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_real_addr_some_value"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpRealAddrSomeValue {width : Nat} [NeZero width] {C F : Type} (conf : Config)
    (s : WordSemStateFiniteExact width C F) (a : Nat) (curr ww : BitVec width)
    (heap : s.store.lookup .currHeap = some (.word curr))
    (read : s.getVar a = some (.word ww)) (good : goodDimindex width)
    (bound : shiftLength conf < width) : ∃ wx,
      s.wordExp (realAddr conf a) = some (.word wx) := by
  cases h : getRealAddr conf s.store ww with
  | none =>
    simp only [getRealAddr, heap] at h
    split at h <;> simp_all
    split at h <;> simp_all
  | some address =>
    exact ⟨address, getRealAddr_lemma conf a s ww address ⟨bound, good, read, h⟩⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
