import Flapjack.Compiler.Backend.WordAlloc.MergeStackSets

namespace Flapjack.Test.WordAllocMergeStackSetsParity
open Flapjack Flapjack.WordAlloc
-- mss_empty=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ln,0) (.ln,.ln) (.ln,.ln) = (.ln,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_retained_right=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ls true,0) (.ls 10,.ln) (.ls 20,.ln) = (.ls 20,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_new_left_bias=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ln,0) (.ls 10,.ln) (.ls 20,.ln) = (.ls 10,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_new_right=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ln,0) (.ln,.ln) (.ls 20,.ln) = (.ls 20,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_removed=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ls true,0) (.ls 10,.ln) (.ln,.ln) = (.ln,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_fixed_left_bias=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ln,0) (.ln,.ls 3) (.ln,.ls 4) = (.ln,.ls 3) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_raw=T
example : mergeStackSets (α := Nat) (β := Nat) (γ := Bool) (δ := Nat) (.ln,0) (.bn .ln .ln,.ln) (.ln,.ln) = (.bn .ln .ln,.ln) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
-- mss_generic=T
example : mergeStackSets (α := Nat) (β := Bool) (γ := Bool) (δ := Bool) (.ls true,false) (.ls 10,.ls true) (.ls 20,.ls false) = (.ls 20,.ls true) := by simp [mergeStackSets, sptUnion, sptInter, sptDifference]
