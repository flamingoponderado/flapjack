import Flapjack.Compiler.Backend.WordCse.Proofs.InsertEquality
namespace Flapjack.Test.WordCseInsertEqualityParity
open Flapjack Flapjack.Compiler.Backend.WordCse
-- ie_0_7
example : sptInsert 0 7 (.ln : Spt Nat) = sptInsert 0 7 .ln := by rfl

-- ie_0_8
example : ¬ (sptInsert 0 7 (.ln : Spt Nat) = sptInsert 0 8 .ln) := by
  simp only [insertEq]
  decide

-- ie_1_7
example : sptInsert 7 7 ((.ls 99) : Spt Nat) = sptInsert 7 7 (.ls 99) := by rfl

-- ie_1_8
example : ¬ (sptInsert 7 7 ((.ls 99) : Spt Nat) = sptInsert 7 8 (.ls 99)) := by
  simp only [insertEq]
  decide

-- ie_2_7
example : sptInsert 0 7 ((.bn .ln .ln) : Spt Nat) = sptInsert 0 7 (.bn .ln .ln) := by rfl

-- ie_2_8
example : ¬ (sptInsert 0 7 ((.bn .ln .ln) : Spt Nat) = sptInsert 0 8 (.bn .ln .ln)) := by
  simp only [insertEq]
  decide

-- ie_3_7
example : sptInsert 2 7 ((.bs .ln 11 .ln) : Spt Nat) = sptInsert 2 7 (.bs .ln 11 .ln) := by rfl

-- ie_3_8
example : ¬ (sptInsert 2 7 ((.bs .ln 11 .ln) : Spt Nat) = sptInsert 2 8 (.bs .ln 11 .ln)) := by
  simp only [insertEq]
  decide

-- ie_4_7
example : sptInsert 1 7 ((.bn (.ls 8) (.ls 9)) : Spt Nat) = sptInsert 1 7 (.bn (.ls 8) (.ls 9)) := by rfl

-- ie_4_8
example : ¬ (sptInsert 1 7 ((.bn (.ls 8) (.ls 9)) : Spt Nat) = sptInsert 1 8 (.bn (.ls 8) (.ls 9))) := by
  simp only [insertEq]
  decide

example {α : Type} (k : Nat) (a b : α) (tree : Spt α)
    (h : sptInsert k a tree = sptInsert k b tree) : a = b :=
  (insertEq k a b tree).mp h
example (a b : BitVec 80) (tree : Spt (BitVec 80))
    (h : sptInsert 18446744073709551616 a tree = sptInsert 18446744073709551616 b tree) : a = b :=
  (insertEq _ a b tree).mp h
end Flapjack.Test.WordCseInsertEqualityParity
