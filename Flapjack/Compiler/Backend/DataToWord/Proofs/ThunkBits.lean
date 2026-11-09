import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Thunk
import Flapjack.Compiler.Backend.DataToWord.Proofs.WordTest

/-! Concrete thunk-header tests used by data-to-word correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataSem
open Memory

/-- A related thunk either represents an inlined value with a non-thunk
header or has the header bits for its evaluation mode. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "memory_rel_Thunk_bits"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_thunkBits {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (bit : Bool) (ptr : Nat) (word : BitVec width) (vars : List (Value × WordLocW width))
    (mode : AstHOL.ThunkMode) (child : Value) (address header : BitVec width) :
    memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, .word word) :: vars) ∧
      sptLookup ptr refs = some (.thunk mode child) ∧ goodDimindex width ∧
      getRealAddr conf store word = some address ∧ memory address = .word header ∧ word.getLsbD 0 = true →
    (bit = false ∧ mode = .evaluated ∧
      (60 &&& header) ≠ BitVec.ofNat width ((0 + 6) * 4) ∧
      (60 &&& header) ≠ BitVec.ofNat width ((8 + 6) * 4)) ∨
    match mode with
    | .notEvaluated => (60 &&& header) = BitVec.ofNat width ((0 + 6) * 4)
    | .evaluated => (60 &&& header) = BitVec.ofNat width ((8 + 6) * 4) := by
  rintro ⟨rel, found, good, addressEq, memoryEq, low⟩
  rcases memoryRel_thunkImp conf be next refs space store memory domain bit ptr (.word word) vars mode child
      ⟨rel, found, good⟩ with inlined | allocated
  · obtain ⟨bitEq, modeEq, contents⟩ := inlined
    obtain ⟨_, foundAddress, foundHeader, real, mem, _, notUnevaluated, notEvaluated⟩ :=
      contents word ⟨rfl, low⟩
    have sameAddress : foundAddress = address := Option.some.inj (real.symm.trans addressEq)
    subst foundAddress
    have sameHeader : foundHeader = header := WordLocW.word.inj (mem.symm.trans memoryEq)
    subst foundHeader
    exact Or.inl ⟨bitEq, modeEq, by simpa only [BitVec.and_comm] using notUnevaluated,
      by simpa only [BitVec.and_comm] using notEvaluated⟩
  · obtain ⟨foundWord, foundAddress, foundHeader, loc, _, bit3, bit2, bit4,
      _, real, mem, _, _, _, bit5, _⟩ := allocated
    have sameWord : word = foundWord := WordLocW.word.inj loc
    subst foundWord
    have sameAddress : foundAddress = address := Option.some.inj (real.symm.trans addressEq)
    subst foundAddress
    have sameHeader : foundHeader = header := WordLocW.word.inj (mem.symm.trans memoryEq)
    subst foundHeader
    apply Or.inr
    cases mode with
    | notEvaluated =>
        have last : header.getLsbD 5 = false := by
          cases h : header.getLsbD 5 <;> simp_all
        exact (wordTestLemma2 header good).mpr ⟨bit2, bit3, bit4, last⟩
    | evaluated =>
        have last : header.getLsbD 5 = true := bit5.mpr rfl
        exact (wordTestLemma1 header good).mpr ⟨bit2, bit3, bit4, last⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
