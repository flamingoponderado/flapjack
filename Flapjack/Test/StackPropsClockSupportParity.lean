import Flapjack.Compiler.Backend.StackProps.ClockSupport

/-! Kernel replay of the ten original clock_neutral observations. This tests
accepted/rejected constructors and recursive conjunctions, not evaluation. -/
namespace Flapjack.Test.StackPropsClockSupportParity
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Backend.StackLang
example : clockNeutralHOL (.skip : HolProg 64) := by simp [clockNeutralHOL]
example : clockNeutralHOL (.inst (.fp (.fpSqrt 0 1)) : HolProg 1) := by
  simp [clockNeutralHOL]
example : clockNeutralHOL (.halt 2 : HolProg 16) := by simp [clockNeutralHOL]
example : clockNeutralHOL (.locValue 0 1 2 : HolProg 1) := by simp [clockNeutralHOL]
example : clockNeutralHOL (.seq .skip (.halt 2) : HolProg 64) := by simp [clockNeutralHOL]
example : ¬ clockNeutralHOL (.seq (.locValue 0 1 2) .tick : HolProg 16) := by
  simp [clockNeutralHOL]
example : clockNeutralHOL (.ite .equal 0 (.reg 1) .skip (.halt 2) : HolProg 1) := by
  simp [clockNeutralHOL]
example : ¬ clockNeutralHOL (.ite .equal 0 (.reg 1) .skip .tick : HolProg 64) := by
  simp [clockNeutralHOL]
example : ¬ clockNeutralHOL (.loop .skip : HolProg 64) := by simp [clockNeutralHOL]
example : ¬ clockNeutralHOL (.call (some (.skip,0,1,2)) (.inl 3) none : HolProg 1) := by
  simp [clockNeutralHOL]
end Flapjack.Test.StackPropsClockSupportParity
