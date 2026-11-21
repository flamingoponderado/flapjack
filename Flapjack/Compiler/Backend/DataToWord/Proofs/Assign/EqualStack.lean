module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordOp8
@[expose] public section

/-! Stack bounds for the equality runtime helpers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps

namespace EqualStackWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end EqualStackWitness

/-- The current local-space bound is one of the two equality stub bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "sane_locals_size_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
def saneLocalsSize {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) : Prop :=
  state.localsSize = sptLookup equalLocation state.stackSize ∨
    state.localsSize = sptLookup equal1Location state.stackSize

/-- Equality-helper stack bounds are monotone in the comparison depth. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "eq_code_stack_max_le_mono"]
theorem eqCodeStackMax_le_mono (a b : Nat) (sizes : Spt Nat) (h : a ≤ b) :
    optionLe (DataSem.eqCodeStackMax a sizes) (DataSem.eqCodeStackMax b sizes) := by
  unfold DataSem.eqCodeStackMax
  cases hsize : Option.map₂ max (sptLookup equalLocation sizes)
    (Option.map₂ max (sptLookup equal1Location sizes) (sptLookup compare1Location sizes)) with
  | none => simp [optionLe]
  | some size => simp only [Option.map_some, optionLe]; exact Nat.mul_le_mul_right size h

/-- Unroll a nonzero equality-helper stack bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "eq_code_stack_max_sub1"]
theorem eqCodeStackMax_sub1 (l : Nat) (sizes : Spt Nat) (h : l ≠ 0) :
    DataSem.eqCodeStackMax l sizes =
      Option.map₂ (· + ·)
        (Option.map₂ max (sptLookup equalLocation sizes)
          (Option.map₂ max (sptLookup equal1Location sizes) (sptLookup compare1Location sizes)))
        (DataSem.eqCodeStackMax (l - 1) sizes) := by
  unfold DataSem.eqCodeStackMax
  cases hsize : Option.map₂ max (sptLookup equalLocation sizes)
    (Option.map₂ max (sptLookup equal1Location sizes) (sptLookup compare1Location sizes)) with
  | none => simp
  | some size =>
    simp only [Option.map_some, Option.map₂_some_some]
    cases l with
    | zero => contradiction
    | succ l => simp [Nat.succ_mul, Nat.add_comm]

/-- Distribute successor multiplication over an optional natural number. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "option_map_mult_suc"]
theorem optionMap_mul_succ (n : Nat) (m : Option Nat) :
    m.map ((n+1) * ·) = Option.map₂ (· + ·) m (m.map (n * ·)) := by
  cases m <;> simp [Nat.succ_mul, Nat.add_comm]
/-- Subtraction distributes over the minimum of natural numbers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "MIN_SUB"]
theorem minSub (a b c : Nat) : min a b - c = min (a - c) (b - c) := by
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
