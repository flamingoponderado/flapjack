import Flapjack.Compiler.Backend.WordBignum.Compile

/-! Replay pinned HOL mini-language compiler examples. -/
namespace Flapjack.Test.WordBignumCompileParity
open Flapjack Flapjack.Compiler.Backend.WordBignum

private abbrev M := Mini (BitVec 64)
private abbrev C := CodeAcc 64
private def initial : C := (40, [])

#guard lookupCode (.assign 1 (.op .add [.var 1, .const 3]) : M)
    [(.assign 1 (.op .add [.var 1, .const 4]), 7, .skip),
     (.assign 1 (.op .add [.var 1, .const 3]), 8, .skip),
     (.assign 1 (.op .add [.var 1, .const 3]), 9, .skip)] == some 8

#guard lookupCode (.assign 1 (.op .add [.var 1, .const 3]) : M)
    [(.assign 1 (.op .add [.var 1, .const 4]), 7, .skip)] == none

#guard match compileBounded 0 39 2 1 initial (.skip : M) with
  | some (.skip, 2, 1, (40, [])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.continue : M) with
  | some (.call none (some 39) [0] none, 2, 1, (40, [])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.delete [1, 2] : M) with
  | some (.skip, 2, 1, (40, [])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.loopBody .skip : M) with
  | some (.skip, 2, 1, (40, [])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.swap : M) with
  | some (.seq (.assign 1 (.lookup (.temp a)))
      (.seq (.set (.temp b) (.lookup (.temp c))) (.set (.temp d) (.var 1))), 2, 2, (40, [])) =>
      a == 31 && b == 31 && c == 30 && d == 30
  | _ => false

#guard match compileBounded 0 39 2 1 initial
    (.ite .equal 3 (.reg 4) .skip .continue : M) with
  | some (.seq (.assign 1 (.lookup (.temp a))) (.seq (.assign 2 (.lookup (.temp b)))
      (.ite .equal 1 (.reg 2) .skip (.call none (some 39) [0] none))), 2, 3, (40, [])) =>
      a == 3 && b == 4
  | _ => false

#guard match compileBounded 0 39 2 1 initial
    (.ite .equal 3 (.imm 7) .skip .continue : M) with
  | some (.seq (.assign 1 (.lookup (.temp a)))
      (.ite .equal 1 (.imm value) .skip (.call none (some 39) [0] none)), 2, 2, (40, [])) =>
      a == 3 && value == 7
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.assign 33 (.var 34) : M) with
  | some (.seq (.assign 1 (.lookup (.temp src))) (.set (.temp dst) (.var 1)), 2, 2, (40, [])) =>
      src == 2 && dst == 1
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.recurse [0, 33] [17] : M) with
  | some (.seq (.get 2 (.temp a)) (.seq (.get 35 (.temp b))
      (.call (some ([1], (.ls (), cuts),
        .seq (.set (.temp c) (.var 2)) (.seq (.set (.temp d) (.var 35)) .skip), 39, 2))
        (some 39) [] none)), 3, 1, (40, [])) =>
      a == 0 && b == 1 && c == 0 && d == 1 &&
        decide (sptToAList cuts = [(35, ()), (2, ())])
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.loop false [] .skip : M) with
  | some (.call (some ([1], (.ls (), .ln), .skip, 39, 2)) (some 40) [] none,
      3, 2, (41, [(.skip, 40, .skip)])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 (40, [(.skip, 45, .skip)]) (.loop false [] .skip : M) with
  | some (.call (some ([1], (.ls (), .ln), .skip, 39, 2)) (some 45) [] none,
      3, 2, (40, [(.skip, 45, .skip)])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial
    (.seq (.loop false [] .skip) (.loop true [3] .skip) : M) with
  | some (.seq (.call (some ([1], (.ls (), .ln), .skip, 39, 2)) (some 40) [] none)
      (.call (some ([2], (.ls (), .ln), .skip, 39, 3)) (some 40) [] none),
      4, 3, (41, [(.skip, 40, .skip)])) => true
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.load 3 4 .in2 : M) with
  | some (.seq (.assign 1 (.op .add [.lookup (.temp base),
      .shift .lsl (.lookup (.temp index)) (.const shift)]))
      (.seq (.assign 2 (.load (.var 1))) (.set (.temp dst) (.var 2))), 2, 3, (40, [])) =>
      base == 30 && index == 4 && shift == 3 && dst == 3
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.store 3 4 : M) with
  | some (.seq (.assign 1 (.lookup (.temp src)))
      (.seq (.assign 2 (.op .add [.lookup (.temp base),
        .shift .lsl (.lookup (.temp index)) (.const shift)])) (.store (.var 2) 1)), 2, 3, (40, [])) =>
      src == 3 && base == 29 && index == 4 && shift == 3
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.sub 1 2 3 (.imm 5) (.reg 7) : M) with
  | some (.seq (.assign 5 (.lookup (.temp carry)))
      (.seq (.assign 4 (.const neg)) (.seq (.assign 3 (.lookup (.temp left)))
        (.seq (.inst (.arith (.addCarry 2 3 4 5)))
          (.seq (.set (.temp a) (.var 2)) (.set (.temp b) (.var 5)))))), 2, 6, (40, [])) =>
      carry == 7 && neg == (~~~(5 : BitVec 64)) && left == 3 && a == 1 && b == 2
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.add 1 2 3 (.imm 5) (.reg 7) : M) with
  | some (.seq (.assign 5 (.lookup (.temp carry)))
      (.seq (.assign 4 (.const word)) (.seq (.assign 3 (.lookup (.temp left)))
        (.seq (.inst (.arith (.addCarry 2 3 4 5)))
          (.seq (.set (.temp a) (.var 2)) (.set (.temp b) (.var 5)))))), 2, 6, (40, [])) =>
      carry == 7 && word == 5 && left == 3 && a == 1 && b == 2
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.mul 1 2 3 4 : M) with
  | some (.seq (.assign 4 (.lookup (.temp right))) (.seq (.assign 3 (.lookup (.temp left)))
      (.seq (.inst (.arith (.longMul 1 2 3 4)))
        (.seq (.set (.temp a) (.var 1)) (.set (.temp b) (.var 2))))), 2, 5, (40, [])) =>
      right == 4 && left == 3 && a == 2 && b == 1
  | _ => false

#guard match compileBounded 0 39 2 1 initial (.div 1 2 3 4 5 : M) with
  | some (.seq (.assign 5 (.lookup (.temp a))) (.seq (.assign 4 (.lookup (.temp b)))
      (.seq (.assign 3 (.lookup (.temp c)))
        (.seq (.mustTerminate (.seq (.call (some ([1], (.ls (), .ln), .skip, 39, 2))
          (some 23) [3, 4, 5] none) (.assign 2 (.lookup (.temp t)))))
          (.seq (.set (.temp d) (.var 1)) (.set (.temp e) (.var 2)))))), 3, 6, (40, [])) =>
      a == 5 && b == 4 && c == 3 && t == 28 && d == 1 && e == 2
  | _ => false

end Flapjack.Test.WordBignumCompileParity
