module

public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

@[expose] public section

/-!
# Constant-write lemmas of HOL `word_elimProof`

Counterpart of `cakeml/compiler/backend/proofs/word_elimProofScript.sml:902-908`:
`const_writes_eq_Loc`.  HOL's `const_writes` is the tagged `wordSemConstWrites`
(`WordSem.CallHelpers`).
-/

namespace Flapjack.Compiler.Backend.WordElim

/-- Exact HOL `const_writes_eq_Loc` (`word_elimProofScript.sml:902-908`): a
    cell that still holds a `Loc` after the constant writes was already that
    `Loc` in the original memory.  HOL's `const_writes` is `wordSemConstWrites`;
    the binder order follows the typed capture (words, a, c, m, k, l1, l2). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "const_writes_eq_Loc"
  (words_as_type_indexed_bitvec)]
theorem wordSemConstWrites_eq_Loc {width : Nat} [NeZero width]
    (words : List (Bool × BitVec width)) (a c : BitVec width)
    (m : BitVec width → WordLocW width) (k : BitVec width) (l1 l2 : Nat) :
    wordSemConstWrites a c words m k = .loc l1 l2 → m k = .loc l1 l2 := by
  induction words generalizing a m with
  | nil =>
      intro h
      exact h
  | cons head tail ih =>
      intro h
      obtain ⟨b, x⟩ := head
      simp only [wordSemConstWrites] at h
      have hk := ih (a + wordSemBytesInWord)
        (fun addr => if addr = a then .word (if b then x + c else x) else m addr) h
      by_cases hka : k = a
      · rw [if_pos hka] at hk
        simp at hk
      · rw [if_neg hka] at hk
        exact hk

end Flapjack.Compiler.Backend.WordElim
