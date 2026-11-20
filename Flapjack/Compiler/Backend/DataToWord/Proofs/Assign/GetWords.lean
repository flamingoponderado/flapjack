module

public import Flapjack.Compiler.Backend.DataToWord.Build

@[expose] public section

/-! Leading word extraction for constant construction. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack

/-- The accumulator is reversed before the leading word prefix. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "getWords_acc"
  (words_as_type_indexed_bitvec)]
theorem getWords_acc {α : Type} {width : Nat} [NeZero width]
    (values : List (α × WordLocW width)) (acc : List (α × BitVec width)) :
    Build.getWords values acc =
      let (words, rest) := Build.getWords values []
      (acc.reverse ++ words, rest) := by
  induction values generalizing acc with
  | nil => simp [Build.getWords]
  | cons value rest ih =>
    obtain ⟨flag, value⟩ := value
    cases value with
    | loc block offset => simp [Build.getWords]
    | word word =>
      simp only [Build.getWords]
      rw [ih ((flag, word) :: acc), ih [(flag, word)]]
      cases Build.getWords rest []
      simp [List.reverse_cons, List.append_assoc]

/-- The extracted words followed by the remainder reconstruct the input. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "getWords_thm"
  (words_as_type_indexed_bitvec)]
theorem getWords_thm {α : Type} {width : Nat} [NeZero width]
    (values : List (α × WordLocW width)) (words : List (α × BitVec width))
    (rest : List (α × WordLocW width))
    (run : Build.getWords values [] = (words, rest)) :
    values = words.map (fun (flag, word) => (flag, .word word)) ++ rest := by
  induction values generalizing words rest with
  | nil => simp [Build.getWords] at run; simp_all
  | cons value tail ih =>
    obtain ⟨flag, value⟩ := value
    cases value with
    | loc block offset => simp [Build.getWords] at run; simp_all
    | word word =>
      rw [Build.getWords, getWords_acc] at run
      cases h : Build.getWords tail [] with
      | mk tailWords tailRest =>
        simp only [h, List.reverse_singleton, List.singleton_append] at run
        cases run
        simp only [List.map_cons, List.cons_append]
        congr 1
        exact ih _ _ h

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
