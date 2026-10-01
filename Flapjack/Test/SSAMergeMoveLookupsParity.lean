import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveLookups

namespace Flapjack.Test.SSAMergeMoveLookupsParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- Each regression applies the full theorem, rather than replacing it with a
-- concrete evaluator equality. The common changed-key guard is deliberately false.
example (key : Nat) :
    sptLookup key (mergeMoves [] Spt.ln Spt.ln 8).2.2.2.1 = none ∧
    sptLookup key (mergeMoves [] Spt.ln Spt.ln 8).2.2.2.2 = none := by
  exact mergeMovesFrame3 [] 8 Spt.ln Spt.ln key (Or.inl (by simp))

example :
    sptLookup 2 (mergeMoves [0,0] (Spt.ls 1) (Spt.ls 3) 8).2.2.2.1 =
      sptLookup 2 (Spt.ls 1) ∧
    sptLookup 2 (mergeMoves [0,0] (Spt.ls 1) (Spt.ls 3) 8).2.2.2.2 =
      sptLookup 2 (Spt.ls 3) := by
  exact mergeMovesFrame3 [0,0] 8 (Spt.ls 1) (Spt.ls 3) 2 (Or.inl (by simp))

example :
    sptLookup 0 (mergeMoves [0] Spt.ln (Spt.ls 3) 8).2.2.2.1 =
      sptLookup 0 (Spt.ln : Spt Nat) ∧
    sptLookup 0 (mergeMoves [0] Spt.ln (Spt.ls 3) 8).2.2.2.2 =
      sptLookup 0 (Spt.ls 3) := by
  apply mergeMovesFrame3 [0] 8 Spt.ln (Spt.ls 3) 0
  exact Or.inr (by simp [sptDomain, sptInter])

example : ¬ (0 ∉ ([0] : List Nat) ∨
    ¬ sptDomain (sptInter (Spt.ls 1) (Spt.ls 3)) 0) := by
  simp [sptDomain, sptInter, sptLookup]

example : mergeMoves [0,0] (Spt.ls 1) (Spt.ls 3) 8 =
    ([(8,1)], [(8,3)], 12, Spt.ls 8, Spt.ls 8) := by
  simp [mergeMoves, sptLookup, sptInsert]
example : mergeMoves [0] Spt.ln (Spt.ls 3) 8 =
    ([], [], 8, Spt.ln, Spt.ls 3) := by decide

end Flapjack.Test.SSAMergeMoveLookupsParity
