import Flapjack.Misc.GoodDimindex
import Mathlib.Tactic.IntervalCases

/-! Bit-mask facts used by the data-to-word thunk proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack

/-- A thunk header with tag fourteen has bits 3, 4 and 5 set and bit 2 clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "word_test_lemma1"
  (words_as_type_indexed_bitvec)]
theorem wordTestLemma1 {width : Nat} [NeZero width] (x : BitVec width)
    (good : goodDimindex width) :
    ((60 : BitVec width) &&& x = BitVec.ofNat width ((8 + 6) * 4)) ↔
      (x.getLsbD 2 = false ∧ x.getLsbD 3 = true ∧
       x.getLsbD 4 = true ∧ x.getLsbD 5 = true) := by
  rcases good with h | h <;> subst width
  all_goals
    constructor
    · intro h
      have h2 := congrArg (fun v : BitVec _ => v.getLsbD 2) h
      have h3 := congrArg (fun v : BitVec _ => v.getLsbD 3) h
      have h4 := congrArg (fun v : BitVec _ => v.getLsbD 4) h
      have h5 := congrArg (fun v : BitVec _ => v.getLsbD 5) h
      simpa [BitVec.getLsbD_and] using And.intro h2 (And.intro h3 (And.intro h4 h5))
    · rintro ⟨h2, h3, h4, h5⟩
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      interval_cases i <;> simp_all

/-- A thunk header with tag six has bits 3 and 4 set and bits 2 and 5 clear. -/
@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "word_test_lemma2"
  (words_as_type_indexed_bitvec)]
theorem wordTestLemma2 {width : Nat} [NeZero width] (x : BitVec width)
    (good : goodDimindex width) :
    ((60 : BitVec width) &&& x = BitVec.ofNat width ((0 + 6) * 4)) ↔
      (x.getLsbD 2 = false ∧ x.getLsbD 3 = true ∧
       x.getLsbD 4 = true ∧ x.getLsbD 5 = false) := by
  rcases good with h | h <;> subst width
  all_goals
    constructor
    · intro h
      have h2 := congrArg (fun v : BitVec _ => v.getLsbD 2) h
      have h3 := congrArg (fun v : BitVec _ => v.getLsbD 3) h
      have h4 := congrArg (fun v : BitVec _ => v.getLsbD 4) h
      have h5 := congrArg (fun v : BitVec _ => v.getLsbD 5) h
      simpa [BitVec.getLsbD_and] using And.intro h2 (And.intro h3 (And.intro h4 h5))
    · rintro ⟨h2, h3, h4, h5⟩
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      interval_cases i <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs
