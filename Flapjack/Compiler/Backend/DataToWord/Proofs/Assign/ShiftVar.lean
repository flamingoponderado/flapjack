module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
@[expose] public section

/-! Variable-shift evaluation used by the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.SemanticPrimitivesProps Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

namespace ShiftAssignWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ShiftAssignWitness

/-- The shift expression reads the word just written to its input register. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_exp_set_var_ShiftVar"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordExpSetVarShiftVar {width : Nat} [NeZero width] {C F : Type}
    (t : WordSemStateFiniteExact width C F) (sh : Shift) (v n : Nat) (w : BitVec width) :
    (t.setVar v (.word w)).wordExp (shiftVar sh v n) =
      Option.map WordLocW.word (match sh with
        | .lsl => some (w <<< n)
        | .lsr => some (w >>> n)
        | .asr => some (w.sshiftRight n)
        | .ror => some (w.rotateRight n)) := by
  rw [wordExpShiftVar]
  cases sh <;> simp [WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, shiftLookup]
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
