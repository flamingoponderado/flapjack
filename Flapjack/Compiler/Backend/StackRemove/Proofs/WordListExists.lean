import Flapjack.Misc.WordList
namespace Flapjack.Compiler.Backend.StackRemove.WordListExists
open Flapjack

/-- Local proof infrastructure for eliminating the pure empty-heap length
assertion. No independent HOL declaration is claimed. -/
theorem starCond {α : Type} (p : (α → Prop) → Prop) (q : Prop) (heap : α → Prop) :
    SetSep.star p (SetSep.cond q) heap ↔ p heap ∧ q := by
  constructor
  · rintro ⟨left, right, partition, hp, empty, hq⟩
    rw [empty] at partition
    have same : left = heap := by
      funext entry
      simpa using congrFun partition.1 entry
    exact ⟨same ▸ hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact ⟨heap, (fun _ => False), ⟨by funext entry; simp, by simp⟩, hp, rfl, hq⟩

/-- Full original conjunction of zero and successor equations. The successor
exposes an arbitrary payload existential while preserving the whole separated
heap, not merely a domain membership or a supplied concrete list. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_exists_thm"
  (words_as_type_indexed_bitvec)]
theorem wordListExistsThm {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (count : Nat) :
    Misc.wordListExists (β := β) address 0 = SetSep.emp ∧
    Misc.wordListExists (β := β) address (count + 1) =
      SetSep.sepExists (fun value : β =>
        SetSep.star (SetSep.one (address, value))
          (Misc.wordListExists (address + bytesInWord width) count)) := by
  constructor
  · funext heap
    apply propext
    simp only [Misc.wordListExists, SetSep.sepExists, starCond]
    constructor
    · rintro ⟨values, assertion, length⟩
      have empty : values = [] := List.length_eq_zero_iff.mp length
      subst values
      exact assertion
    · intro empty
      exact ⟨[], empty, rfl⟩
  · funext heap
    apply propext
    constructor
    · intro assertion
      obtain ⟨values, listHeap, length⟩ :=
        (show ∃ values : List β, Misc.wordList address values heap ∧ values.length = count + 1 by
          simpa only [Misc.wordListExists, SetSep.sepExists, starCond] using assertion)
      cases values with
      | nil => simp at length
      | cons value values =>
        have tailLength : values.length = count := by simpa using length
        rcases listHeap with ⟨left, right, partition, head, tail⟩
        refine ⟨value, left, right, partition, head, ?_⟩
        change ∃ values : List β,
          SetSep.star (Misc.wordList (address + bytesInWord width) values)
            (SetSep.cond (values.length = count)) right
        exact ⟨values, (starCond _ _ _).mpr ⟨tail, tailLength⟩⟩
    · rintro ⟨value, left, right, partition, head, tail⟩
      obtain ⟨values, tailHeap, length⟩ :=
        (show ∃ values : List β, Misc.wordList (address + bytesInWord width) values right ∧
            values.length = count by
          simpa only [Misc.wordListExists, SetSep.sepExists, starCond] using tail)
      change ∃ values : List β, SetSep.star (Misc.wordList address values)
        (SetSep.cond (values.length = count + 1)) heap
      refine ⟨value :: values, (starCond _ _ _).mpr ⟨?_, by simp [length]⟩⟩
      exact ⟨left, right, partition, head, tailHeap⟩

end Flapjack.Compiler.Backend.StackRemove.WordListExists
