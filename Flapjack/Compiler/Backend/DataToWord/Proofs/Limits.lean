import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Limits
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Misc.FiniteMapApply

/-! Limit extraction for the data-to-word observational correctness theorem. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack

local instance {width : Nat} [NeZero width] : Nonempty (WordLocW width) := ⟨.word 0⟩

/-- Canonical finite-map roundtrip for the word state's store field. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Extract data-language limits from the source configuration and target word
state. Out-of-domain finite-map application and `theWord` on a location retain
HOL's unspecified values. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "get_limits_def"
  (fmap_as_finite_support := [store]) (words_as_type_indexed_bitvec)]
noncomputable def getLimits {width : Nat} [NeZero width] {C F : Type}
    (config : Config) (state : WordSemStateFiniteExact width C F) : DataSem.Limits :=
  { stackLimit := state.stackLimit
    heapLimit := (wordSemTheWord (holFapply state.store .heapLength)).toNat / (width / 8)
    lengthLimit := config.lenSize
    arch64Bit := decide (width = 64)
    hasFpOps := config.hasFpOps
    hasFpTops := config.hasFpTern }

/-- When the heap-length store entry is a word, extraction uses that exact
word's byte count. -/
theorem getLimits_heap_of_lookup {width : Nat} [NeZero width] {C F : Type}
    (config : Config) (state : WordSemStateFiniteExact width C F) (bytes : BitVec width)
    (lookup : state.store.lookup .heapLength = some (.word bytes)) :
    (getLimits config state).heapLimit = bytes.toNat / (width / 8) := by
  simp [getLimits, holFapply_of_lookup lookup]

/-- The fields independent of heap-word decoding agree with the existing
data-to-word limit invariant. -/
theorem getLimits_fields_of_limitsInv {width : Nat} [NeZero width] {C F : Type}
    (config : Config) (state : WordSemStateFiniteExact width C F) (limits : DataSem.Limits)
    (inv : Gc.limitsInv limits (state.store.lookup .heapLength) state.stackLimit config.lenSize
      config.hasFpOps config.hasFpTern) :
    (getLimits config state).stackLimit = limits.stackLimit ∧
    (getLimits config state).lengthLimit = limits.lengthLimit ∧
    (getLimits config state).arch64Bit = limits.arch64Bit ∧
    (getLimits config state).hasFpOps = limits.hasFpOps ∧
    (getLimits config state).hasFpTops = limits.hasFpTops := by
  rcases inv with ⟨stack, length, arch, _, _, fpOps, fpTops⟩
  exact ⟨stack.symm, length.symm, arch.symm, fpOps.symm, fpTops.symm⟩

/-- On the RISC-V 64-bit word model, the non-overflowing heap-length invariant
also recovers the data heap limit, so every extracted limit agrees. -/
theorem getLimits_eq_of_limitsInv64 {C F : Type} (config : Config)
    (state : WordSemStateFiniteExact 64 C F) (limits : DataSem.Limits)
    (inv : Gc.limitsInv limits (state.store.lookup .heapLength) state.stackLimit config.lenSize
      config.hasFpOps config.hasFpTern) : getLimits config state = limits := by
  have fields := getLimits_fields_of_limitsInv config state limits inv
  rcases inv with ⟨_, _, _, heap, range, _, _⟩
  have bound : limits.heapLimit * 8 < 2 ^ 64 := by simpa using range
  have sizeBound : limits.heapLimit < 2 ^ 64 := by omega
  have decoded : ((BitVec.ofNat 64 8) * BitVec.ofNat 64 limits.heapLimit).toNat / 8 = limits.heapLimit := by
    simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
    simp [Nat.mod_eq_of_lt sizeBound, Nat.mod_eq_of_lt (by omega : 8 * limits.heapLimit < 2 ^ 64)]
  have heapEq : (getLimits config state).heapLimit = limits.heapLimit := by
    rw [getLimits_heap_of_lookup config state _ heap]
    exact decoded
  cases limits
  cases h : getLimits config state
  simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs
