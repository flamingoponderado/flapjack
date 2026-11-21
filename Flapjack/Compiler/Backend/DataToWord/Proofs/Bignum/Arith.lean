module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StubLookup
public import Flapjack.HolArb

@[expose] public section

/-! Arithmetic stub locations and source integer operations in the bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

namespace ArithWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end ArithWitnesses

/-- The source integer operation selected by an arithmetic stub index. HOL's
integer `/` and `%` are floor division and its remainder. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "int_op_def"]
def intOp (opIndex : Nat) (i j : Int) : Option Int :=
  if opIndex = 0 then some (i + j) else
  if opIndex = 1 then some (i - j) else
  if opIndex = 4 then some (i * j) else
  if opIndex = 5 ∧ j ≠ 0 then some (Int.fdiv i j) else
  if opIndex = 6 ∧ j ≠ 0 then some (Int.fmod i j) else none

/-- The code location of the arithmetic stub for an operation index. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "Arith_location_def"]
noncomputable def arithLocation (index : Nat) : Nat :=
  if index = 0 then addLocation else
  if index = 1 then subLocation else
  if index = 4 then mulLocation else
  if index = 5 then divLocation else
  if index = 6 then modLocation else holArb Nat

/-- The arithmetic stub body: record the operation and call the general stub. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "Arith_code_def"
  (words_as_type_indexed_bitvec)]
def arithCode {width : Nat} [NeZero width] (index : Nat) : WordLangProgHOL (BitVec width) :=
  .seq (.assign 6 (.const (BitVec.ofNat width (4 * index))))
    (.call none (some anyArithLocation) [0, 2, 4, 6] none)

/-- Every defined arithmetic operation has its stub installed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "lookup_Arith_location"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem lookup_arithLocation {width : Nat} [NeZero width] {C F : Type}
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (x : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (index : Nat) (i1 i2 r : Int) :
    stateRel c l1 l2 x t none locs ∧ intOp index i1 i2 = some r →
      sptLookup (arithLocation index) t.code = some (3, arithCode index) := by
  rintro ⟨related, op⟩
  obtain ⟨_, _, _, _, _, add, sub, mul, div, mod⟩ := lookupRefByteLocation c l1 l2 x t locs related
  unfold intOp at op
  by_cases h0 : index = 0
  · subst h0; simpa [arithLocation, arithCode, addCode, arithWrapperCode] using add
  by_cases h1 : index = 1
  · subst h1; simpa [arithLocation, arithCode, subCode, arithWrapperCode] using sub
  by_cases h4 : index = 4
  · subst h4; simpa [arithLocation, arithCode, mulCode, arithWrapperCode] using mul
  by_cases h5 : index = 5
  · subst h5; simpa [arithLocation, arithCode, divCode, arithWrapperCode] using div
  by_cases h6 : index = 6
  · subst h6; simpa [arithLocation, arithCode, modCode, arithWrapperCode] using mod
  simp [h0, h1, h4, h5, h6] at op
end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
