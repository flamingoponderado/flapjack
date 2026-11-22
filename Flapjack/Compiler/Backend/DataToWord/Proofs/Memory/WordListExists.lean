module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.FromList

@[expose] public section

/-!
# Existential word lists in the data-to-word memory proof

Counterparts of `word_list_exists_thm`, `word_list_exists_ADD` and
`word_list_AND_word_list_exists_IMP` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. The first
two restate the identical, already reviewed `stack_removeProof` theorems of the
same names.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

/-- Exact HOL `word_list_exists_thm` of the memory proof. The typed capture
quantifies the payload type independently in each conjunct (β for the zero
equation, γ for the successor equation); both are kept. Proved from the
identical `stack_removeProof` theorem at each payload type. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_list_exists_thm"
  (words_as_type_indexed_bitvec)]
theorem memory_wordListExistsThm {width : Nat} [NeZero width] {β γ : Type}
    (a : BitVec width) (n : Nat) :
    Misc.wordListExists (β := β) a 0 = SetSep.emp ∧
    Misc.wordListExists (β := γ) a (n + 1) =
      SetSep.sepExists (fun w : γ =>
        SetSep.star (SetSep.one (a, w))
          (Misc.wordListExists (a + StackRemove.bytesInWord width) n)) :=
  ⟨(StackRemove.WordListExists.wordListExistsThm (β := β) a n).1,
    (StackRemove.WordListExists.wordListExistsThm (β := γ) a n).2⟩

/-- Exact HOL `word_list_exists_ADD` of the memory proof (same statement as the
`stack_removeProof` theorem it is proved from). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_list_exists_ADD"
  (words_as_type_indexed_bitvec)]
theorem memory_wordListExistsAdd {width : Nat} [NeZero width] {β : Type} :
    ∀ (m n : Nat) (a : BitVec width),
      Misc.wordListExists (β := β) a (m + n) =
        SetSep.star (Misc.wordListExists a m)
          (Misc.wordListExists (a + StackRemove.bytesInWord width * BitVec.ofNat width m) n) :=
  StackRemove.Proofs.WordListMemory.wordListExistsAdd

/-- Two lists at the same addresses inside one function graph carry the same
values. Flapjack infrastructure for `word_list_AND_word_list_exists_IMP`. -/
theorem wordList_graph_unique {width : Nat} [NeZero width] {β : Type}
    (m : BitVec width → β) (dm : BitVec width → Prop) (aa : BitVec width) (ws ys : List β)
    (left right : (BitVec width × β) → Prop)
    (hl : Misc.wordList aa ws left) (hr : Misc.wordList aa ys right)
    (sl : ∀ e, left e → SetSep.fun2Set (m, dm) e) (sr : ∀ e, right e → SetSep.fun2Set (m, dm) e)
    (len : ws.length = ys.length) : ws = ys := by
  apply List.ext_getElem len
  intro i h1 h2
  have a := ((SetSep.fun2SetThm m dm _ _).mp (sl _ (wordList_indexMember ws i h1 aa left hl))).1
  have b := ((SetSep.fun2SetThm m dm _ _).mp (sr _ (wordList_indexMember ys i h2 aa right hr))).1
  exact a.symm.trans b

/-- Exact HOL `word_list_AND_word_list_exists_IMP`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_list_AND_word_list_exists_IMP"
  (words_as_type_indexed_bitvec)]
theorem wordList_and_wordListExists_imp {width : Nat} [NeZero width] {β : Type}
    (m : BitVec width → β) (dm : BitVec width → Prop) :
    ∀ (ws : List β) (aa : BitVec width) (frame : ((BitVec width × β) → Prop) → Prop) (n : Nat),
      SetSep.star (Misc.wordList aa ws) SetSep.sepT (SetSep.fun2Set (m, dm)) ∧
      SetSep.star (Misc.wordListExists aa n) frame (SetSep.fun2Set (m, dm)) ∧
      ws.length ≤ n →
      SetSep.star (SetSep.star (Misc.wordList aa ws)
        (Misc.wordListExists (aa + StackRemove.bytesInWord width * BitVec.ofNat width ws.length) (n - ws.length)))
        frame (SetSep.fun2Set (m, dm)) := by
  rintro ws aa frame n ⟨⟨l1, _, p1, hws, _⟩, sep, len⟩
  rw [show n = ws.length + (n - ws.length) by omega, StackRemove.Proofs.WordListMemory.wordListExistsAdd] at sep
  obtain ⟨l2, r2, p2, ⟨l3, r3, p3, ⟨ys, hys⟩, rest⟩, frameR⟩ := sep
  obtain ⟨ysList, ysLen⟩ := (StackRemove.WordListExists.starCond _ _ _).mp hys
  have sub1 : ∀ e, l1 e → SetSep.fun2Set (m, dm) e := fun e h => by rw [← p1.1]; exact Or.inl h
  have sub3 : ∀ e, l3 e → SetSep.fun2Set (m, dm) e := fun e h => by
    rw [← p2.1]; left; rw [← p3.1]; exact Or.inl h
  have same := wordList_graph_unique m dm aa ws ys l1 l3 hws ysList sub1 sub3 ysLen.symm
  subst same
  exact ⟨l2, r2, p2, ⟨l3, r3, p3, ysList, rest⟩, frameR⟩
