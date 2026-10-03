import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap

namespace Flapjack.Compiler.Backend.StackRemove.Proofs.InitReadMemory
open Flapjack

/-- Complete original framed word-list memory-read theorem. The list, base,
frame, memory and domain remain arbitrary. The separation assertion derives
every read; no no-wrap, good-dimension or desired-output premise is added. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_IMP_read_mem"
  (words_as_type_indexed_bitvec)]
theorem wordListImpReadMem {width : Nat} [NeZero width] {β : Type}
    (memory : BitVec width → β) (domain : BitVec width → Prop) :
    ∀ (values : List β) (base : BitVec width)
      (frame : ((BitVec width × β) → Prop) → Prop),
      SetSep.star frame (Misc.wordList base values) (SetSep.fun2Set (memory, domain)) →
      readMem base memory values.length = values := by
  intro values
  induction values with
  | nil => intros; rfl
  | cons head tail ih =>
      intro base frame assertion
      have headValue : memory base = head := by
        rcases assertion with ⟨first, second, partition, _frame, listAssertion⟩
        have member := StackHeap.wordListNth base (head :: tail) second 0
          (by simp) listAssertion
        have listMember : second (base, head) := by simpa using member
        have graphMember : SetSep.fun2Set (memory, domain) (base, head) := by
          rw [← partition.1]
          exact Or.inr listMember
        exact ((SetSep.fun2SetThm memory domain base head).mp graphMember).1
      have tailRead := ih (base + bytesInWord width)
        (SetSep.star frame (SetSep.one (base, head)))
        (by simpa only [Misc.wordList, SetSep.starAssoc] using assertion)
      simp only [List.length_cons, readMem, headValue, tailRead]

end Flapjack.Compiler.Backend.StackRemove.Proofs.InitReadMemory
