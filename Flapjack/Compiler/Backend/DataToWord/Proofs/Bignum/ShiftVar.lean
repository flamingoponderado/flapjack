module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate
public import Flapjack.SemanticPrimitivesProps.Shift
public import Mathlib.Tactic
@[expose] public section

/-! Correctness of the generated variable-shift expression. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.SemanticPrimitivesProps

namespace ShiftVarWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ShiftVarWitness

private theorem asrSaturate {width : Nat} [NeZero width] (w : BitVec width)
    (n : Nat) (hn : width ≤ n) : w.sshiftRight (width - 1) = w.sshiftRight n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_sshiftRight]
  have hpos : 0 < width := NeZero.pos width
  by_cases hz : i = 0
  · subst i
    simp [show ¬ n < width by omega, show width - 1 < width by omega,
      BitVec.msb_eq_getLsbD_last]
  · simp [show ¬ n + i < width by omega, show ¬ width - 1 + i < width by omega]

private theorem rotateZero {width : Nat} [NeZero width] (w : BitVec width) :
    w.rotateRight 0 = w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

/-- Evaluating a generated shift follows the lookup-based HOL equation;
non-word lookups retain HOL's identity-valued `FAIL` branch. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "word_exp_set_var_ShiftVar_lemma" (fmap_as_finite_support := [fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem wordExpShiftVar {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (sh : Shift) (v n : Nat) :
    t.wordExp (shiftVar sh v n) =
      match sptLookup v t.locals with
      | some (.word w) => some (.word (shiftLookup sh w n))
      | _ => t.wordExp (shiftVar sh v n) := by
  cases h : sptLookup v t.locals with
  | none => simp
  | some value =>
    cases value with
    | loc a b => simp
    | word w =>
      simp only
      have hpos : 0 < width := NeZero.pos width
      have powBound (k : Nat) (hk : k < width) : k % (2 ^ width) = k :=
        Nat.mod_eq_of_lt (Nat.lt_trans hk Nat.lt_two_pow_self)
      cases sh <;> simp only [shiftVar, shiftLookup] <;> split_ifs <;>
        simp_all [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
          shiftN, wordShiftHOL, BitVec.shiftLeft_eq_zero,
          BitVec.ushiftRight_eq_zero]
      all_goals try solve
        | exact asrSaturate w n (by assumption)
        | exact (rotateZero w).symm
        | rw [← BitVec.rotateRight_mod_eq_rotateRight]; simp_all [rotateZero]
      all_goals
        have hnmod : n % width < width := Nat.mod_lt _ hpos
        simp [powBound _ hnmod, BitVec.rotateRight_mod_eq_rotateRight, hnmod]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
