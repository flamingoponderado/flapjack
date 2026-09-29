import Flapjack.Compiler.Backend.Semantics.WordSem.Env

/-!
# Exact Loop-to-Word `LASTN_ADD_CONS`

Ports `loop_to_wordProof$LASTN_ADD_CONS` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:447-450`:

```
Theorem LASTN_ADD_CONS[local]:
  ~(LENGTH xs <= n) ⇒ LASTN (n + 1) (x::xs) = LASTN (n + 1) xs
```

This is an exact statement about the HOL standard-library `rich_list$LASTN`
(`LASTN n xs = REVERSE (TAKE n (REVERSE xs))`, outside `cakeml/`), rendered by
the untagged `Flapjack.wordSemLastN`.  The statement mentions no word or
finite-map carrier, so the port is tagged unqualified.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `loop_to_wordProof$LASTN_ADD_CONS`: prepending an element does
    not change the last `n + 1` elements once the tail is longer than `n`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "LASTN_ADD_CONS"]
theorem wordSemLastN_add_cons {α : Type} (x : α) (xs : List α) (n : Nat)
    (h : ¬ xs.length ≤ n) :
    wordSemLastN (n + 1) (x :: xs) = wordSemLastN (n + 1) xs := by
  unfold wordSemLastN
  rw [List.reverse_cons]
  have hlen : n + 1 ≤ xs.reverse.length := by
    simp only [List.length_reverse]
    omega
  rw [List.take_append_of_le_length hlen]

end Flapjack.LoopToWord
