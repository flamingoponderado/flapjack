import Mathlib.Data.Set.Insert
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage

/-! Kernel replays of direct original asmProps stride PC observations. -/
namespace Flapjack.Test.AsmPropsPcCoverageParity
open Flapjack.Compiler.Encoders.AsmProps

-- Original row pcs_empty.
example : ¬ (254 : BitVec 8) ∈ allPcs 0 (254 : BitVec 8) 0 ∧
    ¬ (255 : BitVec 8) ∈ allPcs 0 (254 : BitVec 8) 0 ∧
    ¬ (0 : BitVec 8) ∈ allPcs 0 (254 : BitVec 8) 0 := by
  simp +decide [allPcs]

-- Original row pcs_byte_wrap.
example : ¬ (253 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 ∧
    (254 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 ∧
    (255 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 ∧
    (0 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 ∧
    (1 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 ∧
    ¬ (2 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 0 := by
  simp +decide [allPcs]

-- Original row pcs_stride_short.
example : (254 : BitVec 8) ∈ allPcs 3 (254 : BitVec 8) 2 ∧
    ¬ (2 : BitVec 8) ∈ allPcs 3 (254 : BitVec 8) 2 ∧
    ¬ (6 : BitVec 8) ∈ allPcs 3 (254 : BitVec 8) 2 := by
  simp +decide [allPcs]

-- Original row pcs_stride_exact.
example : (254 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 2 ∧
    ¬ (2 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 2 ∧
    ¬ (6 : BitVec 8) ∈ allPcs 4 (254 : BitVec 8) 2 := by
  simp +decide [allPcs]

-- Original row pcs_stride_tail.
example : (254 : BitVec 8) ∈ allPcs 5 (254 : BitVec 8) 2 ∧
    (2 : BitVec 8) ∈ allPcs 5 (254 : BitVec 8) 2 ∧
    ¬ (6 : BitVec 8) ∈ allPcs 5 (254 : BitVec 8) 2 := by
  simp +decide [allPcs]

-- Original row pcs_stride_twice.
example : (254 : BitVec 8) ∈ allPcs 8 (254 : BitVec 8) 2 ∧
    (2 : BitVec 8) ∈ allPcs 8 (254 : BitVec 8) 2 ∧
    ¬ (6 : BitVec 8) ∈ allPcs 8 (254 : BitVec 8) 2 := by
  simp +decide [allPcs]

-- Original row pcs_stride_extra.
example : (254 : BitVec 8) ∈ allPcs 9 (254 : BitVec 8) 2 ∧
    (2 : BitVec 8) ∈ allPcs 9 (254 : BitVec 8) 2 ∧
    (6 : BitVec 8) ∈ allPcs 9 (254 : BitVec 8) 2 ∧
    ¬ (10 : BitVec 8) ∈ allPcs 9 (254 : BitVec 8) 2 := by
  simp +decide [allPcs]

-- Original row pcs_dimension_stride.
example : (7 : BitVec 8) ∈ allPcs 513 (7 : BitVec 8) 8 ∧
    ¬ (8 : BitVec 8) ∈ allPcs 513 (7 : BitVec 8) 8 ∧
    ¬ (0 : BitVec 8) ∈ allPcs 513 (7 : BitVec 8) 8 := by
  simp +decide [allPcs]

-- Original row pcs_large_stride.
example : (7 : BitVec 8) ∈ allPcs 3 (7 : BitVec 8) 12 ∧
    ¬ (8 : BitVec 8) ∈ allPcs 3 (7 : BitVec 8) 12 ∧
    ¬ (0 : BitVec 8) ∈ allPcs 3 (7 : BitVec 8) 12 := by
  simp +decide [allPcs]

-- Original row pcs_width1_duplicates.
example : (0 : BitVec 1) ∈ allPcs 5 (1 : BitVec 1) 0 ∧
    (1 : BitVec 1) ∈ allPcs 5 (1 : BitVec 1) 0 := by
  simp +decide [allPcs]

-- Original row pcs_width1_stride.
example : ¬ (0 : BitVec 1) ∈ allPcs 5 (1 : BitVec 1) 1 ∧
    (1 : BitVec 1) ∈ allPcs 5 (1 : BitVec 1) 1 := by
  simp +decide [allPcs]

-- Original row pcs_width32_wrap.
example : (4294967288 : BitVec 32) ∈ allPcs 17 (4294967288 : BitVec 32) 4 ∧
    (8 : BitVec 32) ∈ allPcs 17 (4294967288 : BitVec 32) 4 ∧
    ¬ (24 : BitVec 32) ∈ allPcs 17 (4294967288 : BitVec 32) 4 := by
  simp +decide [allPcs]

-- Original row pcs_width64_wrap.
example : (18446744073709551608 : BitVec 64) ∈ allPcs 17 (18446744073709551608 : BitVec 64) 4 ∧
    (8 : BitVec 64) ∈ allPcs 17 (18446744073709551608 : BitVec 64) 4 ∧
    ¬ (24 : BitVec 64) ∈ allPcs 17 (18446744073709551608 : BitVec 64) 4 := by
  simp +decide [allPcs]

def runChecks : IO Bool := do
  IO.println "PASS original native stride PC coverage (13 kernel replays)"
  return true
end Flapjack.Test.AsmPropsPcCoverageParity
