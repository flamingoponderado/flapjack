import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListRev
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Mathlib.Data.List.Induction

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.WordListReverse

/-- Complete original forward/reverse heap-list equality. Addresses use the
same modular positive-width word carrier; payloads remain independent and
arbitrary. No distinct-address, no-wrap or heap-success premise is added. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_EQ_rev"
  (words_as_type_indexed_bitvec)]
theorem wordListEqRev {width : Nat} [NeZero width] {β : Type}
    (values : List β) (base : BitVec width) :
    Misc.wordList base values =
      wordListRev (base + BitVec.ofNat width values.length * bytesInWord width) values.reverse := by
  induction values using List.reverseRecOn generalizing base with
  | nil => simp [Misc.wordList,wordListRev]
  | append_singleton values value ih =>
    have addressEq : base + BitVec.ofNat width (values.length + 1) * bytesInWord width -
        bytesInWord width = base + bytesInWord width * BitVec.ofNat width values.length := by
      simp only [BitVec.ofNat_add,BitVec.add_mul,BitVec.one_mul]
      rw [← BitVec.add_assoc,BitVec.add_sub_cancel,BitVec.mul_comm]
    rw [StackHeap.wordListAppend]
    simp only [List.length_append,List.length_singleton,List.reverse_append,
      List.reverse_singleton,List.singleton_append,wordListRev,addressEq]
    have reversed := ih base
    rw [BitVec.mul_comm] at reversed
    rw [← reversed]
    simp only [Misc.wordList,SetSep.starComm _ SetSep.emp,StackHeap.starEmptyLeft]
    exact SetSep.starComm _ _

end Flapjack.Compiler.Backend.StackRemove.Proofs.WordListReverse
