module

public import Flapjack.Compiler.Backend.DataToWord.Control
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Mathlib.Tactic

@[expose] public section

/-! Agreement of the source-shaped pointer-field code with the former executable. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- Flapjack-specific executable equivalence: the former arithmetic mask and
HOL slice produce identical target programs at every positive word width. -/
theorem maxoutBitsCode_eq_inlined {width : Nat} [NeZero width] (bits shift dest src : Nat) :
    maxoutBitsCode (width := width) bits shift dest src =
      .ite .lower src (.imm (BitVec.ofNat width (2 ^ bits - 1)))
        (.assign dest (.op .or [.var dest, shiftN .lsl (.var src) shift]))
        (.assign dest (.op .or [.var dest, .const (BitVec.ofNat width ((2 ^ bits - 1) * 2 ^ shift))])) := by
  simp [maxoutBitsCode, allOnes_eq_inlined]

namespace MaxoutBitsWitnesses
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end MaxoutBitsWitnesses

/-- Evaluation saturates the requested field exactly as the source specifies.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_Maxout_bits_code"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateMaxoutBitsCode {width : Nat} [NeZero width] {C F : Type}
    (bits shift dest src n : Nat) (target : WordSemStateFiniteExact width C F) (w : BitVec width)
    (different : src ≠ dest) (nBound : n < 2 ^ width) (bitsBound : bits < width) (shiftBound : shift < width)
    (read : sptLookup src target.locals = some (.word (BitVec.ofNat width n))) :
    WordSemStateFiniteExact.evaluate (maxoutBitsCode bits shift dest src) (target.setVar dest (.word w)) =
      (none, target.setVar dest (.word (w ||| maxoutBits n bits shift))) := by
  have powLe : 2 ^ bits ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt bitsBound)
  have powPos : 0 < 2 ^ bits := Nat.two_pow_pos _
  have maxBound : 2 ^ bits - 1 < 2 ^ width := by omega
  have shiftPow : shift < 2 ^ width := Nat.lt_trans shiftBound Nat.lt_two_pow_self
  have srcRead : (target.setVar dest (.word w)).getVar src = some (.word (BitVec.ofNat width n)) := by
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
      sptLookup_sptInsert_ne, different, read]
  have destRead : (target.setVar dest (.word w)).getVar dest = some (.word w) := by
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same]
  simp only [maxoutBitsCode, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getVarImm, srcRead]
  have compare : wordSemWordCmp .lower (.word (BitVec.ofNat width n))
      (.word (BitVec.ofNat width (2 ^ bits - 1))) = some (decide (n < 2 ^ bits - 1)) := by
    simp [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, BitVec.lt_def,
      Nat.mod_eq_of_lt nBound, Nat.mod_eq_of_lt maxBound]
  rw [compare]
  by_cases h : n < 2 ^ bits - 1
  · simp only [h, decide_true, maxoutBits]
    simp [WordSemStateFiniteExact.wordExp, shiftN, srcRead, destRead,
      wordShiftHOL, Nat.mod_eq_of_lt shiftPow, Nat.not_le_of_gt shiftBound, wordOpHOL, wordOp, theWords]
    simp only [WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
    congr 3
    change (w ||| ((BitVec.ofNat width n <<< shift) ||| 0)) = _
    simp
  · simp only [h, decide_false, maxoutBits]
    simp [WordSemStateFiniteExact.wordExp, destRead, wordOpHOL, wordOp, theWords]
    simp only [WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
    congr 3
    change (w ||| (allOnes (shift + bits) shift ||| 0)) = _
    simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
