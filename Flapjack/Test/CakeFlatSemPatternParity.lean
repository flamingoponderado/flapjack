import Flapjack.Compiler.Backend.Semantics.FlatSem.PatternMatch

/-! Matched original HOL observations from `cake_flat_sem_pattern_probe.out`. -/
namespace Flapjack.Test.CakeFlatSemPatternParity
open Flapjack.Compiler.Backend.FlatSem

example : PmatchStampsOk (α := Bool) (β := String) none none true true := .tuple _ _ rfl
example {C F : Type} (s : State C F) :
    pmatchRows [(.pany, true)] s (.litv (.intLit 1)) = .match ([], .pany, true) := by
  simp [pmatchRows, pmatch]

example {C F : Type} (s : State C F) : pmatch s .pany (.litv (.intLit 1)) [] = .match [] := by simp [pmatch]
example {C F : Type} (s : State C F) : pmatch s (.plit (.intLit 1)) (.litv (.intLit 1)) [] = .match [] := by simp [pmatch]
example {C F : Type} (s : State C F) : pmatch s (.plit (.intLit 1)) (.litv (.intLit 2)) [] = .noMatch := by simp [pmatch, Flapjack.SemanticPrimitivesHOL.litSameType]
example {C F : Type} (s : State C F) : pmatch s (.plit (.intLit 1)) (.litv (.char 97)) [] = .typeError := by simp [pmatch, Flapjack.SemanticPrimitivesHOL.litSameType]
example {C F : Type} (s : State C F) : pmatch s (.pcon none []) (.conv none [.litv (.intLit 1)]) [] = .typeError := by
  have h : ¬ PmatchStampsOk (α := Nat) (β := Nat) none none 0 1 := by intro h; cases h; contradiction
  simp [pmatch, h]
example {C F : Type} (s : State C F) :
    pmatch s (.pcon (some (0, some (1, [(0, 0), (1, 0)]))) [])
      (.conv (some (1, some 1)) []) [] = .noMatch := by
  simp [pmatch, ← pmatchStampsOk_iff, pmatchStampsOk]
example {C F : Type} (s : State C F) :
    pmatch s (.pcon (some (0, some (1, [(0, 0)]))) [])
      (.conv (some (0, some 2)) []) [] = .typeError := by
  simp [pmatch, ← pmatchStampsOk_iff, pmatchStampsOk]
example {C F : Type} (s : State C F) :
    pmatchList s [.plit (.intLit 1), .plit (.intLit 0)] [.litv (.intLit 2), .litv (.char 97)] [] = .typeError := by simp [pmatch, pmatchList, Flapjack.SemanticPrimitivesHOL.litSameType]
end Flapjack.Test.CakeFlatSemPatternParity
