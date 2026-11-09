module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Depth.ResourceLimit
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality.Complete

@[expose] public section

/-! Terminating word equality for related values. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataSem
open Classical
noncomputable section

/-- Related source values compare correctly within the target termination limit. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_eq_thm"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem wordEqThm {width : Nat} [NeZero width] (conf : DataToWord.Config) (be : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (v1 v2 : Value) (w1 w2 : BitVec width) (vars : List (Value × WordLocW width)) (b : Bool) :
    memoryRel conf be next refs space store memory domain ((v1, .word w1) :: (v2, .word w2) :: vars) ∧
      doEq refs v1 v2 = .val b ∧ goodDimindex width →
    ∃ result remaining remainingClock,
      wordEq conf store domain memory (wordSemMustTerminateLimit width - 1)
        (min (valueDepth v1) (valueDepth v2)) w1 w2 = some (result, remaining, remainingClock) ∧
      (b = true ↔ result = 1) := by
  rintro ⟨rel, eq, good⟩
  obtain ⟨n, sized⟩ := doEq_imp_vbEqSize refs v1 v2 b eq
  have bound := memoryRel_limit conf be next refs space store memory domain v1 v2
    (.word w1) (.word w2) vars n b () () ⟨rel, sized, good⟩
  have wordPositive : 0 < 2 ^ width := Nat.two_pow_pos width
  have limitBound : n * 2 ^ width < wordSemMustTerminateLimit width - 1 := by omega
  obtain ⟨result, remaining, remainingClock, eqResult, resultCorrect, _⟩ :=
    (wordEqThm0 (β := Unit) (γ := Unit) conf be next space store memory domain vars).1
      refs v1 v2 (wordSemMustTerminateLimit width - 1) (min (valueDepth v1) (valueDepth v2))
      b w1 w2 n ⟨rel, sized, rfl, limitBound, good⟩
  exact ⟨result, remaining, remainingClock, eqResult, resultCorrect⟩

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
