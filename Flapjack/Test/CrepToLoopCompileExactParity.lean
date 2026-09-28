import Flapjack.Pancake.CrepToLoop.ContextExact

/-! Exact-carrier source equations for every constructor of
`crep_to_loop$compile_def`, checked against the direct HOL EVAL fixture
`scripts/hol-probes/crep_to_loop_compile_probe.out`. -/

namespace Flapjack.Test.CrepToLoopCompileExactParity

open Flapjack
open Flapjack.Basis.Pure.MlString

def context : CrepToLoopContextExact :=
  { vars :=
      (HolFiniteMapExact.empty.updateEq (1, 7)).updateEq (2, 8) |>.updateEq (3, 9)
        |>.updateEq (4, 10)
    funcs := HolFiniteMapExact.empty.updateEq (ofString "f", (42, 2))
    vmax := 4
    target := .riscv }

def live : NumSet := sptListInsert [1, 2] .ln

example : loopNestedSeqHOL (width := 8) ([] : List (HolLoopProg 8)) = .skip := rfl
example : loopNestedSeqHOL (width := 8) [.break 3] =
    .seq (.break 3) .skip := rfl
example : loopNestedSeqHOL (width := 8) [.break 3, .tick] =
    .seq (.break 3) (.seq .tick .skip) := rfl

example : compileHOLExact context live (.skip : CrepProgHOL 8) = .skip := by
  simp [compileHOLExact]
example : compileHOLExact context live (.break 3 : CrepProgHOL 8) = .break 3 := by
  simp [compileHOLExact]
example : compileHOLExact context live (.continue 4 : CrepProgHOL 8) = .continue 4 := by
  simp [compileHOLExact]
example : compileHOLExact context live (.tick : CrepProgHOL 8) = .tick := by
  simp [compileHOLExact]

example : compileHOLExact context live
    (.return [.const (5 : BitVec 8)] : CrepProgHOL 8) =
      .seq (.assign 5 (.const 5)) (.seq (.return [5]) .skip) := by
  simp [compileHOLExact, compileExpsHOLExact, compileExpHOLExact, context,
    HolFiniteMapExact.empty, genTemps, loopNestedSeqHOL, List.range,
    List.range.loop, List.zipWith, live]

example : compileHOLExact context live
    (.raise (6 : BitVec 8) : CrepProgHOL 8) =
      .seq (.assign 5 (.const 6)) (.raise 5) := by
  simp [compileHOLExact, context]

example : compileHOLExact context live
    (.shMem .load8 1 (.const (7 : BitVec 8)) : CrepProgHOL 8) =
      .seq (.shMem .load8 7 (.const 7)) .skip := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.store (.const (8 : BitVec 8)) (.const 9) : CrepProgHOL 8) =
      .seq (.assign 5 (.const 9))
        (.seq (.store (.const 8) 5) .skip) := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.store32 (.const (10 : BitVec 8)) (.const 11) : CrepProgHOL 8) =
      .seq (.assign 5 (.const 10))
        (.seq (.assign 6 (.const 11))
          (.seq (.store32 5 6) .skip)) := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.storeByte (.const (12 : BitVec 8)) (.const 13) : CrepProgHOL 8) =
      .seq (.assign 5 (.const 12))
        (.seq (.assign 6 (.const 13))
          (.seq (.storeByte 5 6) .skip)) := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.storeGlob (3 : BitVec 5) (.const (14 : BitVec 8)) : CrepProgHOL 8) =
      .seq (.setGlobal 3 (.const 14)) .skip := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.seq (.break 1) .tick : CrepProgHOL 8) = .seq (.break 1) .tick := by
  simp [compileHOLExact]

example : compileHOLExact context live
    (.assign 1 (.var 2) : CrepProgHOL 8) =
      .seq (.assign 7 (.var 8)) .skip := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.primitive [1] .addCarry [2] : CrepProgHOL 8) =
      .primitive [7] .addCarry [8] := by
  simp [compileHOLExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, live]

example : compileHOLExact context live
    (.dec 5 (.const (15 : BitVec 8)) (.assign 5 (.var 5)) : CrepProgHOL 8) =
      .seq .skip
        (.seq (.assign 5 (.const 15))
          (.seq (.assign 5 (.var 5)) .skip)) := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.ite (.const (1 : BitVec 8)) (.break 2) .tick : CrepProgHOL 8) =
      .seq (.assign 5 (.const 1))
        (.seq (.ite .notEqual 5 (.imm (0 : BitVec 8)) (.break 2) .tick live)
          .skip) := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.while (.const (1 : BitVec 8)) (.break 2) : CrepProgHOL 8) =
      .loop live
        (.seq (.assign 5 (.const 1))
          (.seq (.ite .notEqual 5 (.imm (0 : BitVec 8))
            (.seq (.break 2) (.continue 0)) (.break 0) live) .skip)) live := by
  simp [compileHOLExact, compileExpHOLExact, context, HolFiniteMapExact.empty,
    loopNestedSeqHOL, live]

example : compileHOLExact context live
    (.call (some ([1], some ((3 : BitVec 8), .break 7))) (ofString "f")
      [.const (16 : BitVec 8)] : CrepProgHOL 8) =
      .seq (.assign 5 (.const 16))
        (.seq (.call (some ([7], live)) (some 42) [5]
          (some (5,
            .ite .notEqual 5 (.imm (3 : BitVec 8)) (.raise 5)
              (.seq .tick (.break 7)) live,
            .skip, live))) .skip) := by
  simp [compileHOLExact, compileExpsHOLExact, compileExpHOLExact,
    findLabExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, genTemps, loopNestedSeqHOL,
    List.range, List.range.loop, List.zipWith, live]

example : compileHOLExact context live
    (.extCall (ofString "ffi") 1 2 3 4 : CrepProgHOL 8) =
      .ffi (ofString "ffi") 7 8 9 10 live := by
  simp [compileHOLExact, context, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, live]

/-- The checked projection covers the exact compiler's nested call, return-live,
handler-live, and `MlString` outputs in the source-level parity fixture above. -/
example : loopProgExecRel
    (holLoopProgToExecutableCanonical
      (compileHOLExact context live
        (.call (some ([1], some ((3 : BitVec 8), .break 7))) (ofString "f")
          [.const (16 : BitVec 8)] : CrepProgHOL 8)))
    (compileHOLExact context live
      (.call (some ([1], some ((3 : BitVec 8), .break 7))) (ofString "f")
        [.const (16 : BitVec 8)] : CrepProgHOL 8)) :=
  holLoopProgToExecutableCanonical_rel _

/-- The FFI exact compiler fixture is related through the checked total
`MlString` decoding/re-encoding law. -/
example : loopProgExecRel
    (holLoopProgToExecutableCanonical
      (compileHOLExact context live
        (.extCall (ofString "ffi") 1 2 3 4 : CrepProgHOL 8)))
    (compileHOLExact context live
      (.extCall (ofString "ffi") 1 2 3 4 : CrepProgHOL 8)) :=
  holLoopProgToExecutableCanonical_rel _

end Flapjack.Test.CrepToLoopCompileExactParity
