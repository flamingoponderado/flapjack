import Flapjack.RiscV.WordToStack
import Flapjack.RiscV.WordCopyProp
import Flapjack.RiscV.WordCse
import Flapjack.RiscV.Backend
import Flapjack.RiscV.Encoding

/-! Matching executed observations of the original overflow constructors.
The full original HOL results live in word_overflow_production_probe.out.
These are carrier/consumer fixtures, not a full pass simulation theorem. -/
namespace Flapjack.Test.WordOverflowProduction
open Flapjack Flapjack.RiscV

private def stateView {width : Nat} [NeZero width] (left right : Nat)
    (operation : WordArith Nat) (flag : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let initial : WordStackMachineState width :=
    { registers := fun r => BitVec.ofNat width
        (if r = 2 then left else if r = 3 then right else 99),
      stack := fun _ => 0, stores := fun _ => 0,
      memory := fun _ => 0, sharedMemory := fun _ => 0 }
  (evalWordStackMachine initial (.inst (.arith operation))).map fun final =>
    ((final.registers 0).toNat, (final.registers flag).toNat,
      (final.registers 2).toNat, (final.registers 3).toNat)

-- overflow_class_add_8_0
example :
    let a : WordArith (BitVec 8) := .addOverflow 99 3 5 98
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 103, 105], 99, [99, 98], [3, 5], false) := by rfl

-- overflow_class_add_8_1
example :
    let a : WordArith (BitVec 8) := .addOverflow 1 1 1 1
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 101, 101], 1, [1, 1], [1, 1], false) := by rfl

-- overflow_class_add_8_2
example :
    let a : WordArith (BitVec 8) := .addOverflow 1180591620717411303425 1180591620717411303427 1180591620717411303429 0
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 1180591620717411303527, 1180591620717411303529], 1180591620717411303425, [1180591620717411303425, 0], [1180591620717411303427, 1180591620717411303429], false) := by rfl

-- overflow_class_sub_8_0
example :
    let a : WordArith (BitVec 8) := .subOverflow 99 3 5 98
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 103, 105], 99, [99, 98], [3, 5], false) := by rfl

-- overflow_class_sub_8_1
example :
    let a : WordArith (BitVec 8) := .subOverflow 1 1 1 1
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 101, 101], 1, [1, 1], [1, 1], false) := by rfl

-- overflow_class_sub_8_2
example :
    let a : WordArith (BitVec 8) := .subOverflow 1180591620717411303425 1180591620717411303427 1180591620717411303429 0
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 1180591620717411303527, 1180591620717411303529], 1180591620717411303425, [1180591620717411303425, 0], [1180591620717411303427, 1180591620717411303429], false) := by rfl

-- overflow_class_add_80_0
example :
    let a : WordArith (BitVec 80) := .addOverflow 99 3 5 98
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 103, 105], 99, [99, 98], [3, 5], false) := by rfl

-- overflow_class_add_80_1
example :
    let a : WordArith (BitVec 80) := .addOverflow 1 1 1 1
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 101, 101], 1, [1, 1], [1, 1], false) := by rfl

-- overflow_class_add_80_2
example :
    let a : WordArith (BitVec 80) := .addOverflow 1180591620717411303425 1180591620717411303427 1180591620717411303429 0
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([31, 1180591620717411303527, 1180591620717411303529], 1180591620717411303425, [1180591620717411303425, 0], [1180591620717411303427, 1180591620717411303429], false) := by rfl

-- overflow_class_sub_80_0
example :
    let a : WordArith (BitVec 80) := .subOverflow 99 3 5 98
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 103, 105], 99, [99, 98], [3, 5], false) := by rfl

-- overflow_class_sub_80_1
example :
    let a : WordArith (BitVec 80) := .subOverflow 1 1 1 1
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 101, 101], 1, [1, 1], [1, 1], false) := by rfl

-- overflow_class_sub_80_2
example :
    let a : WordArith (BitVec 80) := .subOverflow 1180591620717411303425 1180591620717411303427 1180591620717411303429 0
    (wordCseArithToNumList a, wordCseFirstRegOfArith a, wordCseArithWrites a,
      wordCseArithReads a, wordCseCanMemArith a) =
      ([32, 1180591620717411303527, 1180591620717411303529], 1180591620717411303425, [1180591620717411303425, 0], [1180591620717411303427, 1180591620717411303429], false) := by rfl

-- overflow_state_add_1_0_0
example : stateView (width := 1) 0 0
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_1_0_1
example : stateView (width := 1) 0 0
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_1_1_0
example : stateView (width := 1) 0 1
    (.addOverflow 0 2 3 4) 4 =
    some (1, 0, 0, 1) := by decide +kernel

-- overflow_state_add_1_1_1
example : stateView (width := 1) 0 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 1) := by decide +kernel

-- overflow_state_add_1_2_0
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_2_1
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_3_0
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_3_1
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_4_0
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_4_1
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_5_0
example : stateView (width := 1) 0 1
    (.addOverflow 0 2 3 4) 4 =
    some (1, 0, 0, 1) := by decide +kernel

-- overflow_state_add_1_5_1
example : stateView (width := 1) 0 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 1) := by decide +kernel

-- overflow_state_add_1_6_0
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_6_1
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_7_0
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 1, 1) := by decide +kernel

-- overflow_state_add_1_7_1
example : stateView (width := 1) 1 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 1, 1) := by decide +kernel

-- overflow_state_sub_1_0_0
example : stateView (width := 1) 0 0
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_1_0_1
example : stateView (width := 1) 0 0
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_1_1_0
example : stateView (width := 1) 0 1
    (.subOverflow 0 2 3 4) 4 =
    some (1, 1, 0, 1) := by decide +kernel

-- overflow_state_sub_1_1_1
example : stateView (width := 1) 0 1
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 0, 1) := by decide +kernel

-- overflow_state_sub_1_2_0
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_2_1
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_3_0
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_3_1
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_4_0
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_4_1
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_5_0
example : stateView (width := 1) 0 1
    (.subOverflow 0 2 3 4) 4 =
    some (1, 1, 0, 1) := by decide +kernel

-- overflow_state_sub_1_5_1
example : stateView (width := 1) 0 1
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 0, 1) := by decide +kernel

-- overflow_state_sub_1_6_0
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_6_1
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_7_0
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_sub_1_7_1
example : stateView (width := 1) 1 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1, 1) := by decide +kernel

-- overflow_state_add_8_0_0
example : stateView (width := 8) 0 0
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_8_0_1
example : stateView (width := 8) 0 0
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_8_1_0
example : stateView (width := 8) 127 1
    (.addOverflow 0 2 3 4) 4 =
    some (128, 1, 127, 1) := by decide +kernel

-- overflow_state_add_8_1_1
example : stateView (width := 8) 127 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 127, 1) := by decide +kernel

-- overflow_state_add_8_2_0
example : stateView (width := 8) 128 255
    (.addOverflow 0 2 3 4) 4 =
    some (127, 1, 128, 255) := by decide +kernel

-- overflow_state_add_8_2_1
example : stateView (width := 8) 128 255
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 128, 255) := by decide +kernel

-- overflow_state_add_8_3_0
example : stateView (width := 8) 128 1
    (.addOverflow 0 2 3 4) 4 =
    some (129, 0, 128, 1) := by decide +kernel

-- overflow_state_add_8_3_1
example : stateView (width := 8) 128 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 128, 1) := by decide +kernel

-- overflow_state_add_8_4_0
example : stateView (width := 8) 255 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 255, 1) := by decide +kernel

-- overflow_state_add_8_4_1
example : stateView (width := 8) 255 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 255, 1) := by decide +kernel

-- overflow_state_add_8_5_0
example : stateView (width := 8) 127 255
    (.addOverflow 0 2 3 4) 4 =
    some (126, 0, 127, 255) := by decide +kernel

-- overflow_state_add_8_5_1
example : stateView (width := 8) 127 255
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 127, 255) := by decide +kernel

-- overflow_state_add_8_6_0
example : stateView (width := 8) 128 128
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 128, 128) := by decide +kernel

-- overflow_state_add_8_6_1
example : stateView (width := 8) 128 128
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 128, 128) := by decide +kernel

-- overflow_state_add_8_7_0
example : stateView (width := 8) 255 255
    (.addOverflow 0 2 3 4) 4 =
    some (254, 0, 255, 255) := by decide +kernel

-- overflow_state_add_8_7_1
example : stateView (width := 8) 255 255
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 255, 255) := by decide +kernel

-- overflow_state_sub_8_0_0
example : stateView (width := 8) 0 0
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_8_0_1
example : stateView (width := 8) 0 0
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_8_1_0
example : stateView (width := 8) 127 1
    (.subOverflow 0 2 3 4) 4 =
    some (126, 0, 127, 1) := by decide +kernel

-- overflow_state_sub_8_1_1
example : stateView (width := 8) 127 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 127, 1) := by decide +kernel

-- overflow_state_sub_8_2_0
example : stateView (width := 8) 128 255
    (.subOverflow 0 2 3 4) 4 =
    some (129, 0, 128, 255) := by decide +kernel

-- overflow_state_sub_8_2_1
example : stateView (width := 8) 128 255
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 128, 255) := by decide +kernel

-- overflow_state_sub_8_3_0
example : stateView (width := 8) 128 1
    (.subOverflow 0 2 3 4) 4 =
    some (127, 1, 128, 1) := by decide +kernel

-- overflow_state_sub_8_3_1
example : stateView (width := 8) 128 1
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 128, 1) := by decide +kernel

-- overflow_state_sub_8_4_0
example : stateView (width := 8) 255 1
    (.subOverflow 0 2 3 4) 4 =
    some (254, 0, 255, 1) := by decide +kernel

-- overflow_state_sub_8_4_1
example : stateView (width := 8) 255 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 255, 1) := by decide +kernel

-- overflow_state_sub_8_5_0
example : stateView (width := 8) 127 255
    (.subOverflow 0 2 3 4) 4 =
    some (128, 1, 127, 255) := by decide +kernel

-- overflow_state_sub_8_5_1
example : stateView (width := 8) 127 255
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 127, 255) := by decide +kernel

-- overflow_state_sub_8_6_0
example : stateView (width := 8) 128 128
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 128, 128) := by decide +kernel

-- overflow_state_sub_8_6_1
example : stateView (width := 8) 128 128
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 128, 128) := by decide +kernel

-- overflow_state_sub_8_7_0
example : stateView (width := 8) 255 255
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 255, 255) := by decide +kernel

-- overflow_state_sub_8_7_1
example : stateView (width := 8) 255 255
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 255, 255) := by decide +kernel

-- overflow_state_add_64_0_0
example : stateView (width := 64) 0 0
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_64_0_1
example : stateView (width := 64) 0 0
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_64_1_0
example : stateView (width := 64) 9223372036854775807 1
    (.addOverflow 0 2 3 4) 4 =
    some (9223372036854775808, 1, 9223372036854775807, 1) := by decide +kernel

-- overflow_state_add_64_1_1
example : stateView (width := 64) 9223372036854775807 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 9223372036854775807, 1) := by decide +kernel

-- overflow_state_add_64_2_0
example : stateView (width := 64) 9223372036854775808 18446744073709551615
    (.addOverflow 0 2 3 4) 4 =
    some (9223372036854775807, 1, 9223372036854775808, 18446744073709551615) := by decide +kernel

-- overflow_state_add_64_2_1
example : stateView (width := 64) 9223372036854775808 18446744073709551615
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 9223372036854775808, 18446744073709551615) := by decide +kernel

-- overflow_state_add_64_3_0
example : stateView (width := 64) 9223372036854775808 1
    (.addOverflow 0 2 3 4) 4 =
    some (9223372036854775809, 0, 9223372036854775808, 1) := by decide +kernel

-- overflow_state_add_64_3_1
example : stateView (width := 64) 9223372036854775808 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 9223372036854775808, 1) := by decide +kernel

-- overflow_state_add_64_4_0
example : stateView (width := 64) 18446744073709551615 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 18446744073709551615, 1) := by decide +kernel

-- overflow_state_add_64_4_1
example : stateView (width := 64) 18446744073709551615 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 18446744073709551615, 1) := by decide +kernel

-- overflow_state_add_64_5_0
example : stateView (width := 64) 9223372036854775807 18446744073709551615
    (.addOverflow 0 2 3 4) 4 =
    some (9223372036854775806, 0, 9223372036854775807, 18446744073709551615) := by decide +kernel

-- overflow_state_add_64_5_1
example : stateView (width := 64) 9223372036854775807 18446744073709551615
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 9223372036854775807, 18446744073709551615) := by decide +kernel

-- overflow_state_add_64_6_0
example : stateView (width := 64) 9223372036854775808 9223372036854775808
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 9223372036854775808, 9223372036854775808) := by decide +kernel

-- overflow_state_add_64_6_1
example : stateView (width := 64) 9223372036854775808 9223372036854775808
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 9223372036854775808, 9223372036854775808) := by decide +kernel

-- overflow_state_add_64_7_0
example : stateView (width := 64) 18446744073709551615 18446744073709551615
    (.addOverflow 0 2 3 4) 4 =
    some (18446744073709551614, 0, 18446744073709551615, 18446744073709551615) := by decide +kernel

-- overflow_state_add_64_7_1
example : stateView (width := 64) 18446744073709551615 18446744073709551615
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 18446744073709551615, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_0_0
example : stateView (width := 64) 0 0
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_64_0_1
example : stateView (width := 64) 0 0
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_64_1_0
example : stateView (width := 64) 9223372036854775807 1
    (.subOverflow 0 2 3 4) 4 =
    some (9223372036854775806, 0, 9223372036854775807, 1) := by decide +kernel

-- overflow_state_sub_64_1_1
example : stateView (width := 64) 9223372036854775807 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 9223372036854775807, 1) := by decide +kernel

-- overflow_state_sub_64_2_0
example : stateView (width := 64) 9223372036854775808 18446744073709551615
    (.subOverflow 0 2 3 4) 4 =
    some (9223372036854775809, 0, 9223372036854775808, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_2_1
example : stateView (width := 64) 9223372036854775808 18446744073709551615
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 9223372036854775808, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_3_0
example : stateView (width := 64) 9223372036854775808 1
    (.subOverflow 0 2 3 4) 4 =
    some (9223372036854775807, 1, 9223372036854775808, 1) := by decide +kernel

-- overflow_state_sub_64_3_1
example : stateView (width := 64) 9223372036854775808 1
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 9223372036854775808, 1) := by decide +kernel

-- overflow_state_sub_64_4_0
example : stateView (width := 64) 18446744073709551615 1
    (.subOverflow 0 2 3 4) 4 =
    some (18446744073709551614, 0, 18446744073709551615, 1) := by decide +kernel

-- overflow_state_sub_64_4_1
example : stateView (width := 64) 18446744073709551615 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 18446744073709551615, 1) := by decide +kernel

-- overflow_state_sub_64_5_0
example : stateView (width := 64) 9223372036854775807 18446744073709551615
    (.subOverflow 0 2 3 4) 4 =
    some (9223372036854775808, 1, 9223372036854775807, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_5_1
example : stateView (width := 64) 9223372036854775807 18446744073709551615
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 9223372036854775807, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_6_0
example : stateView (width := 64) 9223372036854775808 9223372036854775808
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 9223372036854775808, 9223372036854775808) := by decide +kernel

-- overflow_state_sub_64_6_1
example : stateView (width := 64) 9223372036854775808 9223372036854775808
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 9223372036854775808, 9223372036854775808) := by decide +kernel

-- overflow_state_sub_64_7_0
example : stateView (width := 64) 18446744073709551615 18446744073709551615
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 18446744073709551615, 18446744073709551615) := by decide +kernel

-- overflow_state_sub_64_7_1
example : stateView (width := 64) 18446744073709551615 18446744073709551615
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 18446744073709551615, 18446744073709551615) := by decide +kernel

-- overflow_state_add_80_0_0
example : stateView (width := 80) 0 0
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_80_0_1
example : stateView (width := 80) 0 0
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_add_80_1_0
example : stateView (width := 80) 604462909807314587353087 1
    (.addOverflow 0 2 3 4) 4 =
    some (604462909807314587353088, 1, 604462909807314587353087, 1) := by decide +kernel

-- overflow_state_add_80_1_1
example : stateView (width := 80) 604462909807314587353087 1
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 604462909807314587353087, 1) := by decide +kernel

-- overflow_state_add_80_2_0
example : stateView (width := 80) 604462909807314587353088 1208925819614629174706175
    (.addOverflow 0 2 3 4) 4 =
    some (604462909807314587353087, 1, 604462909807314587353088, 1208925819614629174706175) := by decide +kernel

-- overflow_state_add_80_2_1
example : stateView (width := 80) 604462909807314587353088 1208925819614629174706175
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 604462909807314587353088, 1208925819614629174706175) := by decide +kernel

-- overflow_state_add_80_3_0
example : stateView (width := 80) 604462909807314587353088 1
    (.addOverflow 0 2 3 4) 4 =
    some (604462909807314587353089, 0, 604462909807314587353088, 1) := by decide +kernel

-- overflow_state_add_80_3_1
example : stateView (width := 80) 604462909807314587353088 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 604462909807314587353088, 1) := by decide +kernel

-- overflow_state_add_80_4_0
example : stateView (width := 80) 1208925819614629174706175 1
    (.addOverflow 0 2 3 4) 4 =
    some (0, 0, 1208925819614629174706175, 1) := by decide +kernel

-- overflow_state_add_80_4_1
example : stateView (width := 80) 1208925819614629174706175 1
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 1208925819614629174706175, 1) := by decide +kernel

-- overflow_state_add_80_5_0
example : stateView (width := 80) 604462909807314587353087 1208925819614629174706175
    (.addOverflow 0 2 3 4) 4 =
    some (604462909807314587353086, 0, 604462909807314587353087, 1208925819614629174706175) := by decide +kernel

-- overflow_state_add_80_5_1
example : stateView (width := 80) 604462909807314587353087 1208925819614629174706175
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 604462909807314587353087, 1208925819614629174706175) := by decide +kernel

-- overflow_state_add_80_6_0
example : stateView (width := 80) 604462909807314587353088 604462909807314587353088
    (.addOverflow 0 2 3 4) 4 =
    some (0, 1, 604462909807314587353088, 604462909807314587353088) := by decide +kernel

-- overflow_state_add_80_6_1
example : stateView (width := 80) 604462909807314587353088 604462909807314587353088
    (.addOverflow 0 2 3 0) 0 =
    some (1, 1, 604462909807314587353088, 604462909807314587353088) := by decide +kernel

-- overflow_state_add_80_7_0
example : stateView (width := 80) 1208925819614629174706175 1208925819614629174706175
    (.addOverflow 0 2 3 4) 4 =
    some (1208925819614629174706174, 0, 1208925819614629174706175, 1208925819614629174706175) := by decide +kernel

-- overflow_state_add_80_7_1
example : stateView (width := 80) 1208925819614629174706175 1208925819614629174706175
    (.addOverflow 0 2 3 0) 0 =
    some (0, 0, 1208925819614629174706175, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_0_0
example : stateView (width := 80) 0 0
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_80_0_1
example : stateView (width := 80) 0 0
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 0, 0) := by decide +kernel

-- overflow_state_sub_80_1_0
example : stateView (width := 80) 604462909807314587353087 1
    (.subOverflow 0 2 3 4) 4 =
    some (604462909807314587353086, 0, 604462909807314587353087, 1) := by decide +kernel

-- overflow_state_sub_80_1_1
example : stateView (width := 80) 604462909807314587353087 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 604462909807314587353087, 1) := by decide +kernel

-- overflow_state_sub_80_2_0
example : stateView (width := 80) 604462909807314587353088 1208925819614629174706175
    (.subOverflow 0 2 3 4) 4 =
    some (604462909807314587353089, 0, 604462909807314587353088, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_2_1
example : stateView (width := 80) 604462909807314587353088 1208925819614629174706175
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 604462909807314587353088, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_3_0
example : stateView (width := 80) 604462909807314587353088 1
    (.subOverflow 0 2 3 4) 4 =
    some (604462909807314587353087, 1, 604462909807314587353088, 1) := by decide +kernel

-- overflow_state_sub_80_3_1
example : stateView (width := 80) 604462909807314587353088 1
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 604462909807314587353088, 1) := by decide +kernel

-- overflow_state_sub_80_4_0
example : stateView (width := 80) 1208925819614629174706175 1
    (.subOverflow 0 2 3 4) 4 =
    some (1208925819614629174706174, 0, 1208925819614629174706175, 1) := by decide +kernel

-- overflow_state_sub_80_4_1
example : stateView (width := 80) 1208925819614629174706175 1
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1208925819614629174706175, 1) := by decide +kernel

-- overflow_state_sub_80_5_0
example : stateView (width := 80) 604462909807314587353087 1208925819614629174706175
    (.subOverflow 0 2 3 4) 4 =
    some (604462909807314587353088, 1, 604462909807314587353087, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_5_1
example : stateView (width := 80) 604462909807314587353087 1208925819614629174706175
    (.subOverflow 0 2 3 0) 0 =
    some (1, 1, 604462909807314587353087, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_6_0
example : stateView (width := 80) 604462909807314587353088 604462909807314587353088
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 604462909807314587353088, 604462909807314587353088) := by decide +kernel

-- overflow_state_sub_80_6_1
example : stateView (width := 80) 604462909807314587353088 604462909807314587353088
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 604462909807314587353088, 604462909807314587353088) := by decide +kernel

-- overflow_state_sub_80_7_0
example : stateView (width := 80) 1208925819614629174706175 1208925819614629174706175
    (.subOverflow 0 2 3 4) 4 =
    some (0, 0, 1208925819614629174706175, 1208925819614629174706175) := by decide +kernel

-- overflow_state_sub_80_7_1
example : stateView (width := 80) 1208925819614629174706175 1208925819614629174706175
    (.subOverflow 0 2 3 0) 0 =
    some (0, 0, 1208925819614629174706175, 1208925819614629174706175) := by decide +kernel

private def ssaView (operation : WordArith (BitVec 64)) :=
  let (state, program) := wordSsaRenameProgram
    { current := [(2, 10), (3, 11), (4, 12)], next := 21 }
    (.inst (.arith operation))
  (program, lookupNatInfo 2 state.current, lookupNatInfo 5 state.current, state.next)

private def copyCollision : WordCopyState :=
  { wordCopyEmpty with indicesReady := false, aliases := [(3, 1), (2, 9)] }

-- overflow_ssa_add
example : ssaView (.addOverflow 2 3 4 5) =
    (.seq (.inst (.arith (.addOverflow 21 11 12 0))) (.move 1 [(25, 0)]),
      some 21, some 25, 29) := by
  simp [ssaView, wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRead, wordSsaFresh, wordSsaSeq, lookupNatInfo]

-- overflow_copy_add_0 / overflow_copy_add_1
example : (wordCopyInst (α := BitVec 64) wordCopyEmpty (.arith (.addOverflow 1 2 3 4))).1 =
    .arith (.addOverflow 1 2 3 4) := by decide +kernel
example : (wordCopyInst (α := BitVec 64) copyCollision (.arith (.addOverflow 1 2 3 4))).1 =
    .arith (.addOverflow 1 9 3 4) := by decide +kernel

-- overflow_stack_add_0
example : wordToStackInst
    { locations := [(1, .register 0), (3, .register 1), (5, .register 2),
        (0, .register 0)], scratch := 4, addressScratch := 5, stackBase := 0 }
    (.arith (.addOverflow 1 3 5 0) : WordInst Nat) =
    some (.inst (.arith (.addOverflow 0 1 2 0))) := by rfl

-- overflow_stack_add_1
example : wordToStackInst
    { locations := [(13, .stack 5), (11, .stack 6), (15, .stack 4),
        (0, .register 0)], scratch := 4, addressScratch := 5, stackBase := 0 }
    (.arith (.addOverflow 13 11 15 0) : WordInst Nat) =
    some (.seq (.stackLoad 4 6) (.seq (.stackLoad 5 4)
      (.seq (.inst (.arith (.addOverflow 4 4 5 0))) (.stackStore 4 5)))) := by rfl

-- overflow_ssa_sub
example : ssaView (.subOverflow 2 3 4 5) =
    (.seq (.inst (.arith (.subOverflow 21 11 12 0))) (.move 1 [(25, 0)]),
      some 21, some 25, 29) := by
  simp [ssaView, wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRead, wordSsaFresh, wordSsaSeq, lookupNatInfo]

-- overflow_copy_sub_0 / overflow_copy_sub_1
example : (wordCopyInst (α := BitVec 64) wordCopyEmpty (.arith (.subOverflow 1 2 3 4))).1 =
    .arith (.subOverflow 1 2 3 4) := by decide +kernel
example : (wordCopyInst (α := BitVec 64) copyCollision (.arith (.subOverflow 1 2 3 4))).1 =
    .arith (.subOverflow 1 9 3 4) := by decide +kernel

-- overflow_stack_sub_0
example : wordToStackInst
    { locations := [(1, .register 0), (3, .register 1), (5, .register 2),
        (0, .register 0)], scratch := 4, addressScratch := 5, stackBase := 0 }
    (.arith (.subOverflow 1 3 5 0) : WordInst Nat) =
    some (.inst (.arith (.subOverflow 0 1 2 0))) := by rfl

-- overflow_stack_sub_1
example : wordToStackInst
    { locations := [(13, .stack 5), (11, .stack 6), (15, .stack 4),
        (0, .register 0)], scratch := 4, addressScratch := 5, stackBase := 0 }
    (.arith (.subOverflow 13 11 15 0) : WordInst Nat) =
    some (.seq (.stackLoad 4 6) (.seq (.stackLoad 5 4)
      (.seq (.inst (.arith (.subOverflow 4 4 5 0))) (.stackStore 4 5)))) := by rfl

-- Original overflow_add_enc_0, through actual dispatch.
example : (wordArithToInstructions (.addOverflow 5 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 147, 207, 255, 255, 179, 2, 49, 0, 51, 194, 81, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

-- Original overflow_add_enc_3, through actual dispatch.
example : (wordArithToInstructions (.addOverflow 30 29 28 27 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 207, 206, 1, 147, 207, 255, 255, 51, 143, 206, 1, 179, 77, 238, 1, 179, 253, 191, 1, 147, 221, 253, 3] := by decide +kernel

-- Original overflow_add_enc_5, through actual dispatch.
example : (wordArithToInstructions (.addOverflow 4 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 147, 207, 255, 255, 51, 2, 49, 0, 51, 194, 65, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

-- Original overflow_add_enc_6, through actual dispatch.
example : (wordArithToInstructions (.addOverflow 2 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 147, 207, 255, 255, 51, 1, 49, 0, 51, 194, 33, 0, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

example : wordArithToInstructions (.addOverflow 5 2 5 4 : WordArith (BitVec 64)) = none := by rfl
example : wordArithToInstructions (.addOverflow 5 2 3 31 : WordArith (BitVec 64)) = none := by rfl

-- Original overflow_sub_enc_0, through actual dispatch.
example : (wordArithToInstructions (.subOverflow 5 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 179, 2, 49, 64, 51, 194, 81, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

-- Original overflow_sub_enc_3, through actual dispatch.
example : (wordArithToInstructions (.subOverflow 30 29 28 27 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 207, 206, 1, 51, 143, 206, 65, 179, 77, 238, 1, 147, 205, 253, 255, 179, 253, 191, 1, 147, 221, 253, 3] := by decide +kernel

-- Original overflow_sub_enc_5, through actual dispatch.
example : (wordArithToInstructions (.subOverflow 4 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 51, 2, 49, 64, 51, 194, 65, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

-- Original overflow_sub_enc_6, through actual dispatch.
example : (wordArithToInstructions (.subOverflow 2 2 3 4 : WordArith (BitVec 64))).map
    encodeInstructions = some [179, 79, 49, 0, 51, 1, 49, 64, 51, 194, 33, 0, 19, 66, 242, 255, 51, 242, 79, 0, 19, 82, 242, 3] := by decide +kernel

example : wordArithToInstructions (.subOverflow 5 2 5 4 : WordArith (BitVec 64)) = none := by rfl
example : wordArithToInstructions (.subOverflow 5 2 3 31 : WordArith (BitVec 64)) = none := by rfl

end Flapjack.Test.WordOverflowProduction
