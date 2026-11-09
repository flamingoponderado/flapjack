import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordEquality
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockElement

/-! Word-memory comparison used for byte arrays and bignums. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend
open Classical
noncomputable section

/-- Compare expected words with consecutive memory cells, preserving failures. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_mem_eq_def"
  (words_as_type_indexed_bitvec)]
def wordMemEq {aw : Nat} {vw : Nat} [NeZero aw] [NeZero vw] (address : BitVec aw) :
    List (BitVec vw) → (BitVec aw → Bool) → (BitVec aw → WordLocW vw) → Option Bool
  | [], _, _ => some true
  | x :: xs, domain, memory =>
      if domain address then
        match memory address with
        | .word w => if w = x then wordMemEq (address + StackRemove.bytesInWord aw) xs domain memory else some false
        | .loc .. => none
      else none

/-- Separated word-list memory is compared exactly by the word-memory worker. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_mem_eq_thm"
  (words_as_type_indexed_bitvec)]
theorem wordMemEqThm {aw : Nat} {vw : Nat} [NeZero aw] [NeZero vw] (xs ys : List (BitVec vw))
    (address : BitVec aw) (frame : ((BitVec aw × WordLocW vw) → Prop) → Prop)
    (memory : BitVec aw → WordLocW vw) (domain : BitVec aw → Bool) :
    SetSep.star (Misc.wordList address (xs.map WordLocW.word)) frame
      (SetSep.fun2Set (memory, fun a => domain a = true)) ∧ xs.length = ys.length →
    wordMemEq address ys domain memory = some (decide (xs = ys)) := by
  induction xs generalizing ys address frame with
  | nil =>
    intro ⟨_, len⟩
    cases ys <;> simp_all [wordMemEq]
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      rintro ⟨assertion, len⟩
      have first : SetSep.star (SetSep.one (address, WordLocW.word x))
          (SetSep.star (Misc.wordList (address + StackRemove.bytesInWord aw) (xs.map WordLocW.word)) frame)
          (SetSep.fun2Set (memory, fun a => domain a = true)) := by
        simpa only [List.map_cons, Misc.wordList, ← SetSep.starAssoc] using assertion
      have firstFacts := first
      obtain ⟨h1, h2, split, singleton, _⟩ := firstFacts
      have member : h1 (address, WordLocW.word x) := by rw [singleton]
      have whole : SetSep.fun2Set (memory, fun a => domain a = true) (address, WordLocW.word x) := by
        rw [← split.1]
        exact Or.inl member
      obtain ⟨contents, inDomain⟩ := (SetSep.fun2SetThm memory (fun a => domain a = true) address (.word x)).mp whole
      have tail : SetSep.star (Misc.wordList (address + StackRemove.bytesInWord aw) (xs.map WordLocW.word))
          (SetSep.star frame (SetSep.one (address, WordLocW.word x)))
          (SetSep.fun2Set (memory, fun a => domain a = true)) := by
        rw [SetSep.starComm (SetSep.one (address, WordLocW.word x)) _, ← SetSep.starAssoc] at first
        exact first
      have recursive := ih ys (address + StackRemove.bytesInWord aw) _ ⟨tail, by simpa using len⟩
      by_cases eq : x = y
      · subst y
        simp [wordMemEq, inDomain, contents, recursive]
      · simp [wordMemEq, inDomain, contents, eq]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
