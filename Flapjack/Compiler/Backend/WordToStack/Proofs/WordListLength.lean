import Flapjack.Compiler.Backend.WordToStack
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Full original division increment identity with exactly the positive-divisor guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DIV_ADD_1"]
theorem divAddOne (m d : Nat) (hd : 0 < d) : m / d + 1 = (m + d) / d :=
  (Nat.add_div_right m hd).symm

/-- Full original native word-list length at an arbitrary positive chunk size.
No relationship between the chunk size and the word width is required. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_word_list_lemma"
  (words_as_type_indexed_bitvec)]
theorem lengthWordListPositive {width : Nat} [NeZero width] (xs : List Bool)
    (d : Nat) (hd : 0 < d) :
    (wordListW xs d : List (BitVec width)).length = (xs.length - 1) / d + 1 := by
  generalize hn : xs.length = n
  induction n using Nat.strongRecOn generalizing xs with
  | ind n ih =>
    rw [wordListW, ← hn]
    by_cases hshort : xs.length ≤ d
    · rw [if_pos (Or.inl hshort)]
      have hsmall : xs.length - 1 < d := by omega
      simp [Nat.div_eq_of_lt hsmall]
    · rw [if_neg (by omega), List.length_cons]
      have hdrop : (xs.drop d).length < n := by
        simp only [List.length_drop]
        omega
      rw [ih _ hdrop (xs.drop d) rfl, List.length_drop]
      have heq : xs.length - 1 = (xs.length - d - 1) + d := by omega
      rw [heq, Nat.add_div_right _ hd]

/-- Full original native word-list length, including the zero-chunk branch
which always produces one word even for an empty input. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LENGTH_word_list"
  (words_as_type_indexed_bitvec)]
theorem lengthWordList {width : Nat} [NeZero width] (xs : List Bool) (d : Nat) :
    (wordListW xs d : List (BitVec width)).length =
      if d = 0 then 1 else (xs.length - 1) / d + 1 := by
  by_cases hd : d = 0
  · subst d
    rw [wordListW]
    simp
  · rw [if_neg hd]
    exact lengthWordListPositive xs d (by omega)

end Flapjack.Compiler.Backend.WordToStack
