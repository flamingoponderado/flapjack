module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace AssignRealAddressWitness
/-- Canonical finite-map witness for the word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AssignRealAddressWitness

/-- The real-address expression survives writing the first scratch register. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_real_addr"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpRealAddr {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (t : WordSemStateFiniteExact width C F) (ptr a : BitVec width) (a1 : Nat)
    (premises : getRealAddr c t.store ptr = some a ∧ shiftLength c < width ∧ goodDimindex width ∧
      sptLookup (adjustVar a1) t.locals = some (.word ptr)) :
    ∀ w : BitVec width,
      WordSemStateFiniteExact.wordExp {t with locals := sptInsert 1 (.word w) t.locals}
        (realAddr c (adjustVar a1)) = some (.word a) := by
  obtain ⟨addr, shift, good, found⟩ := premises
  intro w
  apply getRealAddr_lemma c (adjustVar a1) _ ptr a
  refine ⟨shift, good, ?_, ?_⟩
  · simpa [WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, adjustVar] using found
  · simpa using addr

/-- The real-address expression survives writing both scratch registers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_real_addr_2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpRealAddr2 {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (t : WordSemStateFiniteExact width C F) (ptr a : BitVec width) (a1 : Nat)
    (premises : getRealAddr c t.store ptr = some a ∧ shiftLength c < width ∧ goodDimindex width ∧
      sptLookup (adjustVar a1) t.locals = some (.word ptr)) :
    ∀ w1 w2 : BitVec width,
      WordSemStateFiniteExact.wordExp {t with locals := sptInsert 3 (.word w1) (sptInsert 1 (.word w2) t.locals)}
        (realAddr c (adjustVar a1)) = some (.word a) := by
  obtain ⟨addr, shift, good, found⟩ := premises
  intro w1 w2
  apply getRealAddr_lemma c (adjustVar a1) _ ptr a
  refine ⟨shift, good, ?_, ?_⟩
  · have ne1 : adjustVar a1 ≠ 1 := by simp [adjustVar]
    have ne3 : adjustVar a1 ≠ 3 := by simp only [adjustVar]; omega
    simpa [WordSemStateFiniteExact.getVar, sptLookup_sptInsert_ne, ne1, ne3] using found
  · simpa using addr

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
