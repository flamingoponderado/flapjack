module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.GiveUp
public import Flapjack.Compiler.Backend.StackAlloc.Proofs.WordLemmas
@[expose] public section

/-! Evaluation of the generated bignum guard. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps

namespace BignumHaltWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end BignumHaltWitness

/-- The bignum guard preserves the original conditional result and stack bound.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_BignumHalt2"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateBignumHalt2 {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (reg : Nat) (w : BitVec width)
    (related : stateRel conf l1 l2 source target none locs)
    (read : target.getVar reg = some (.word w)) :
    ∃ r, WordSemStateFiniteExact.evaluate (bignumHalt reg) target =
      (if w.getLsbD 0 then (some .notEnoughSpace, r) else (none, target)) ∧
      r.ffi = source.ffi ∧ target.ffi = source.ffi ∧ optionLe r.stackMax target.stackMax := by
  have ffi : target.ffi = source.ffi := related.1
  have bitMask := StackAlloc.word_and_one_eq_0_iff w
  cases bit : w.getLsbD 0 with
  | false =>
    have mask : w &&& 1 = 0 := bitMask.mpr (by simp [bit])
    refine ⟨target, ?_, ffi, ffi, optionLe_refl _⟩
    have test : wordSemWordCmp .test (.word w) (.word (1 : BitVec width)) = some true := by
      simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
      change (w &&& (1 : BitVec width) == 0) = true
      exact beq_iff_eq.mpr mask
    simp [bignumHalt, WordSemStateFiniteExact.evaluate, read,
      WordSemStateFiniteExact.getVarImm, - BitVec.ofNat_eq_ofNat, test]
  | true =>
    have mask : w &&& 1 ≠ 0 := fun h => (bitMask.mp h) bit
    obtain ⟨out, run, outFfi, targetFfi, max⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
    refine ⟨out, ?_, outFfi, targetFfi, max⟩
    have test : wordSemWordCmp .test (.word w) (.word (1 : BitVec width)) = some false := by
      simp only [wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL, Option.some.injEq]
      change (w &&& (1 : BitVec width) == 0) = false
      exact beq_eq_false_iff_ne.mpr mask
    simp [bignumHalt, WordSemStateFiniteExact.evaluate, read,
      WordSemStateFiniteExact.getVarImm, - BitVec.ofNat_eq_ofNat, test, run]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
