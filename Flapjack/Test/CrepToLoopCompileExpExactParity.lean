import Flapjack.Pancake.CrepToLoop.ContextExact

/-! Direct cases for the exact-carrier `crep_to_loop$compile_exp_def` port.
The expected equations are from `scripts/hol-probes/crep_to_loop_compile_exp_probe.out`.
-/

namespace Flapjack.Test.CrepToLoopCompileExpExactParity

open Flapjack

def context : CrepToLoopContextExact :=
  mkCtxtExact .riscv HolFiniteMapExact.empty HolFiniteMapExact.empty 0

def contextWithVar : CrepToLoopContextExact :=
  mkCtxtExact .riscv (HolFiniteMapExact.empty.updateEq (1, 7))
    HolFiniteMapExact.empty 0

def live : NumSet := sptListInsert [1, 2] .ln

example : compileCrepopHOLExact (width := 8) .mul .riscv 2 3 4 live =
    ([.arith (.longMul 4 4 2 3)], 4) := rfl

example : compileCrepopHOLExact (width := 8) .mul .armv7 2 3 4 live =
    ([.arith (.longMul 4 5 2 3)], 5) := rfl

example : compileExpHOLExact context 5 live
    (.baseAddr : CrepExpHOL 8) = ([], .baseAddr, 5, live) := by
  simp [compileExpHOLExact, context, mkCtxtExact, HolFiniteMapExact.empty, live]

example : compileExpHOLExact contextWithVar 5 live
    (.var 1 : CrepExpHOL 8) = ([], .var 7, 5, live) := by
  simp [compileExpHOLExact, contextWithVar, mkCtxtExact, HolFiniteMapExact.empty,
    HolFiniteMapExact.updateEq, FUPDATE_HOL, live]

example : compileExpHOLExact context 5 live
    (.load32 (.const (3 : BitVec 8)) : CrepExpHOL 8) =
      ([.assign 5 (.const 3), .load32 5 5], .var 5, 6, sptInsert 5 () live) := by
  simp [compileExpHOLExact, context, mkCtxtExact, HolFiniteMapExact.empty, live]

example : compileExpHOLExact context 5 live
    (.op .add [.const (1 : BitVec 8), .const 2, .const 3] : CrepExpHOL 8) =
      ([], .op .add [.const 1, .const 2, .const 3], 5, live) := by
  simp [compileExpHOLExact, compileExpsHOLExact, context, mkCtxtExact,
    HolFiniteMapExact.empty, live]

example : compileExpHOLExact context 5 live
    (.crepOp .mul [.const (6 : BitVec 8), .const 7] : CrepExpHOL 8) =
      ([.assign 5 (.const 6), .assign 6 (.const 7),
        .arith (.longMul 7 7 5 6)], .var 7, 8,
        sptInsert 7 () (sptListInsert [5, 6] live)) := by
  simp [compileExpHOLExact, compileExpsHOLExact, compileCrepopHOLExact, context,
    mkCtxtExact, HolFiniteMapExact.empty, List.range, List.range.loop, List.zipWith,
    sptListInsert, live]

example : compileExpHOLExact context 5 live
    (.cmp .equal (.const (1 : BitVec 8)) (.const 0) : CrepExpHOL 8) =
      ([.assign 6 (.const 1), .assign 7 (.const 0),
        .ite .equal 6 (.reg 7) (.assign 6 (.const 1)) (.assign 6 (.const 0))
          (sptListInsert [6, 7] live)],
       .var 6, 8, sptListInsert [6, 7] live) := by
  simp [compileExpHOLExact, context,
    mkCtxtExact, HolFiniteMapExact.empty, progIfHOLExact, live]

example : compileExpHOLExact context 5 live
    (.shift .lsl (.const (2 : BitVec 8)) (.const 1) : CrepExpHOL 8) =
      ([], .shift .lsl (.const 2) (.const 1), 5, live) := by
  simp [compileExpHOLExact, context, mkCtxtExact, HolFiniteMapExact.empty, live]

example : compileExpsHOLExact context 5 live
    ([.baseAddr, .const (1 : BitVec 8)] : List (CrepExpHOL 8)) =
      ([], [.baseAddr, .const 1], 5, live) := by
  simp [compileExpHOLExact, compileExpsHOLExact, context, mkCtxtExact,
    HolFiniteMapExact.empty, live]

end Flapjack.Test.CrepToLoopCompileExpExactParity
