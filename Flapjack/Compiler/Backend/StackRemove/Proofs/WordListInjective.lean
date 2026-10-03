import Flapjack.Misc.WordList

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.WordListInjective

/-- Complete original uniqueness of the heap satisfying a forward word list.
Both heaps are arbitrary predicates; address and payload carriers remain
independent. No finiteness, no-wrap or distinct-address premise is added. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_inj"
  (words_as_type_indexed_bitvec)]
theorem wordListInj {width : Nat} [NeZero width] {β : Type}
    (values : List β) (base : BitVec width)
    (heap heap' : (BitVec width × β) → Prop)
    (assertions : Misc.wordList base values heap ∧ Misc.wordList base values heap') :
    heap = heap' := by
  induction values generalizing base heap heap' with
  | nil => exact assertions.1.trans assertions.2.symm
  | cons value values ih =>
    rcases assertions.1 with ⟨first,rest,partition,singleton,tail⟩
    rcases assertions.2 with ⟨first',rest',partition',singleton',tail'⟩
    have restEq := ih (base + Compiler.Backend.StackRemove.bytesInWord width) rest rest' ⟨tail,tail'⟩
    have firstEq : first = first' := singleton.trans singleton'.symm
    rw [← partition.1,← partition'.1,firstEq,restEq]

end Flapjack.Compiler.Backend.StackRemove.Proofs.WordListInjective
