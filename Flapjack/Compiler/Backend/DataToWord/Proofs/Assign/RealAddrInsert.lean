module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.EqualStack
@[expose] public section

/-! Real-address expression preservation for comparison-code correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
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
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
