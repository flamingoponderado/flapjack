import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel

/-! Boundary checks for the data-to-word stack-frame relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

example : stackRel (.env none .ln) (.stackFrame none [] [] none : WordSemStackFrame 64) := by
  simp [stackRel, stackEnvRel, sptLookup, sptFromAList]

example : ¬ stackRel (.env none .ln)
    (.stackFrame none [] [] (some (3, 4, 5)) : WordSemStackFrame 64) := by
  simp [stackRel]

example : ¬ stackRel (.exc none .ln 3)
    (.stackFrame none [] [] (some (4, 0, 0)) : WordSemStackFrame 64) := by
  simp [stackRel]

example : containsLoc (.stackFrame none [(0, .loc 1 2), (0, .loc 3 4)] [] none : WordSemStackFrame 64)
    (1, 2) := by
  simp [containsLoc, sptAListLookup]

example : ¬ containsLoc (.stackFrame none [(0, .loc 1 2), (0, .loc 3 4)] [] none : WordSemStackFrame 64)
    (3, 4) := by
  simp [containsLoc, sptAListLookup]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
