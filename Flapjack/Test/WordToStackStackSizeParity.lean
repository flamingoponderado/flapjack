import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSize

/-! Original HOL rows in word_to_stack_stack_size_rel_probe.out, regenerated
from prebuilt word_to_stackProofTheory; these check the exact tagged predicate. -/
namespace Flapjack.Test.WordToStackStackSizeParity
open WordToStackProofs

private def emptySource : List (WordSemStackFrame 8) := []
private def oneTarget : List (WordLocW 8) := [.word 0]

-- ss_none=T
example : stackSizeRel 0 none 0 none emptySource ([] : List Unit) 0 0 := by
  simp [stackSizeRel, emptySource]
-- ss_some=T
example : stackSizeRel 0 (some 0) 1 (some 1) emptySource oneTarget 0 0 := by
  simp [stackSizeRel, emptySource, oneTarget, wordSemStackSize]
-- ss_bad_max=F
example : ¬ stackSizeRel 0 (some 0) 1 (some 0) emptySource oneTarget 0 0 := by
  simp [stackSizeRel, emptySource, oneTarget, wordSemStackSize]
-- ss_missing_loc=F
example : ¬ stackSizeRel 0 none 1 (some 1) emptySource oneTarget 0 0 := by
  simp [stackSizeRel, emptySource, oneTarget, wordSemStackSize]
-- ss_missing_frame=F
example : ¬ stackSizeRel 0 (some 0) 1 (some 1)
    ([.stackFrame none [] [] none] : List (WordSemStackFrame 8)) oneTarget 0 0 := by
  simp [stackSizeRel, oneTarget, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd]
-- ss_frame_guard=F
example : ¬ stackSizeRel 2 (some 1) 1 none emptySource oneTarget 0 0 := by
  simp [stackSizeRel, emptySource, oneTarget]

-- Independent target payloads: source word width does not constrain this list.
example : stackSizeRel 0 (some 0) 1 (some 1) emptySource [true] 0 0 := by
  simp [stackSizeRel, emptySource, wordSemStackSize]
example : stackSizeRel 0 (some 0) 1 (some 1) emptySource [37] 0 0 := by
  simp [stackSizeRel, emptySource, wordSemStackSize]
example (target : List String) :
    stackSizeRel 0 none target.length none emptySource target 0 0 := by
  simp [stackSizeRel]

def runChecks : IO Bool := do
  IO.println "PASS exact Word-to-Stack stack_size_rel matches all 6 original HOL rows"
  pure true
end Flapjack.Test.WordToStackStackSizeParity
