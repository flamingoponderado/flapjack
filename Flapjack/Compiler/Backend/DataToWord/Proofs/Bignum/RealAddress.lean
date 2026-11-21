module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Address
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

@[expose] public section

/-! Evaluation of the generated address expression. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Evaluating the compiled real-address expression gives the address
computed from the same pointer and word store. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "get_real_addr_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getRealAddr_lemma {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (v : Nat) (state : WordSemStateFiniteExact width C F)
    (ptr address : BitVec width)
    (premises : shiftLength conf < width ∧ goodDimindex width ∧
      WordSemStateFiniteExact.getVar v state = some (.word ptr) ∧
      getRealAddr conf state.store ptr = some address) :
    WordSemStateFiniteExact.wordExp state (realAddr conf v) = some (.word address) := by
  obtain ⟨shiftBound, good, read, addr⟩ := premises
  cases currEq : state.store.lookup .currHeap with
  | none => simp [getRealAddr, currEq] at addr
  | some curr =>
    cases curr with
    | loc a b => simp [getRealAddr, currEq] at addr
    | word curr =>
      have kBound : wordShiftAmount width < width := by
        rcases good with h | h <;> subst width <;> simp [wordShiftAmount]
      have widthPow : width < 2 ^ width := by
        rcases good with h | h <;> subst width <;> decide +revert
      have shiftMod : shiftLength conf % 2 ^ width = shiftLength conf :=
        Nat.mod_eq_of_lt (Nat.lt_trans shiftBound widthPow)
      have kMod : wordShiftAmount width % 2 ^ width = wordShiftAmount width :=
        Nat.mod_eq_of_lt (Nat.lt_trans kBound widthPow)
      have diffBound : shiftLength conf - wordShiftAmount width < width := by omega
      have diffMod : (shiftLength conf - wordShiftAmount width) % 2 ^ width =
          shiftLength conf - wordShiftAmount width := Nat.mod_eq_of_lt (Nat.lt_trans diffBound widthPow)
      simp [getRealAddr, currEq] at addr
      by_cases direct : wordShiftAmount width = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0
      · simp [direct] at addr
        simp [realAddr, direct, WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getStore, theWords, wordOpHOL, wordOp, read, currEq]
        simpa [BitVec.sub_eq_add_neg, BitVec.add_assoc] using addr
      · by_cases short : wordShiftAmount width ≤ conf.padBits + 1
        · simp [direct, short] at addr
          simp [realAddr, direct, short, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore, theWords, wordOpHOL, wordOp, wordShiftHOL, read, currEq,
            diffMod, Nat.not_le_of_gt diffBound, addr]
        · simp [direct, short] at addr
          simp [realAddr, direct, short, WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore, theWords, wordOpHOL, wordOp, wordShiftHOL, read, currEq,
            shiftMod, kMod, Nat.not_le_of_gt shiftBound, Nat.not_le_of_gt kBound, addr]

/-- An index below the word width is unchanged modulo the word modulus. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "lt_dimindex_MOD_dimword"
  (word_dimension_as_width := width)]
theorem lt_dimindex_MOD_dimword (width : Nat) [NeZero width] {n : Nat} :
    n < width → n % 2 ^ width = n :=
  fun h => Nat.mod_eq_of_lt (Nat.lt_trans h Nat.lt_two_pow_self)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
