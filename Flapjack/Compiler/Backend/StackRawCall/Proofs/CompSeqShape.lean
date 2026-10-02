import Flapjack.Compiler.Backend.StackRawCall

namespace Flapjack.Compiler.Backend.StackRawCall
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Original non-fallback shape implication. No assumption about frame lookup
success or the transformed program is added beyond the source inequality. -/
@[hol "cakeml/compiler/backend/proofs/stack_rawcallProofScript.sml" "comp_seq_neq_IMP"
  (words_as_type_indexed_bitvec)]
theorem compSeqNeqImp {width : Nat} [NeZero width]
    (first second fallback : HolProg width) (info : Spt Nat)
    (h : compSeq first second info fallback ≠ fallback) :
    ∃ k dest, first = .stackFree k ∧ second = .call none (.inl dest) none := by
  have hd : destCase first second ≠ none := by
    intro he
    simp [compSeq, he] at h
  unfold destCase at hd
  split at hd <;> simp_all

end Flapjack.Compiler.Backend.StackRawCall
