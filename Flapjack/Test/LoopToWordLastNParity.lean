import Flapjack.Pancake.Proofs.LoopToWord.LastNAddCons

/-!
# Regression for the exact Loop-to-Word `LASTN_ADD_CONS` port

Kernel-checks the ported statement on concrete lists and confirms the
hypothesis is needed.  `LASTN` is the HOL standard-library
`rich_list$LASTN`, rendered by `Flapjack.wordSemLastN`.
-/

namespace Flapjack.Test.LoopToWordLastNParity

open Flapjack
open Flapjack.LoopToWord

/-- Concrete lastn: `LASTN (1 + 1) [3, 1, 2] = [1, 2]`. -/
example : wordSemLastN 2 ([3, 1, 2] : List Nat) = [1, 2] := rfl

/-- The ported `LASTN_ADD_CONS` on a concrete list whose tail is longer than `n`. -/
example : wordSemLastN (1 + 1) (0 :: [3, 1, 2] : List Nat) =
    wordSemLastN (1 + 1) ([3, 1, 2] : List Nat) :=
  wordSemLastN_add_cons 0 [3, 1, 2] 1 (by decide)

/-- A second concrete instance, with a longer tail and `n = 0`. -/
example : wordSemLastN (0 + 1) (9 :: [5, 6, 7] : List Nat) =
    wordSemLastN (0 + 1) ([5, 6, 7] : List Nat) :=
  wordSemLastN_add_cons 9 [5, 6, 7] 0 (by decide)

/-- The hypothesis is load bearing: with a short tail the two sides differ. -/
example : wordSemLastN (1 + 1) (0 :: ([3] : List Nat)) ≠
    wordSemLastN (1 + 1) ([3] : List Nat) := by decide

def runChecks : IO Bool := do
  IO.println "PASS loop_to_word LASTN_ADD_CONS exact port (kernel examples)"
  return true

end Flapjack.Test.LoopToWordLastNParity
