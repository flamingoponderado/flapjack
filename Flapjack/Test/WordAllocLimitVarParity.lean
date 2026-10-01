import Flapjack.Pancake.WordLang.OccurrencesExact
import Flapjack.Compiler.Backend.WordAlloc.LimitVar
import Flapjack.Compiler.Backend.RegAlloc

namespace Flapjack.Test.WordAllocLimitVar
open Flapjack Flapjack.Compiler.Backend.WordAlloc

private def observe {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Nat × Nat × Bool × Bool :=
  (maxVarHOL program, limitVar program, isAllocVar (limitVar program),
    everyVarHOL (fun x => decide (x < limitVar program)) program)

example : observe (.assign 0 (.const 0) : WordLangProgHOL (BitVec 32)) =
    (0, 5, true, true) := by decide +kernel

example : observe (.assign 1 (.const 0) : WordLangProgHOL (BitVec 32)) =
    (1, 5, true, true) := by decide +kernel

example : observe (.assign 2 (.const 0) : WordLangProgHOL (BitVec 32)) =
    (2, 5, true, true) := by decide +kernel

example : observe (.assign 3 (.const 0) : WordLangProgHOL (BitVec 32)) =
    (3, 5, true, true) := by decide +kernel

example : observe (.assign 4 (.const 0) : WordLangProgHOL (BitVec 32)) =
    (4, 9, true, true) := by decide +kernel

example : observe (.skip : WordLangProgHOL (BitVec 1)) =
    (0, 5, true, true) := by decide +kernel

example : observe (.assign 7 (.const 0) : WordLangProgHOL (BitVec 64)) =
    (7, 9, true, true) := by decide +kernel

example : observe (.assign 8 (.const 0) : WordLangProgHOL (BitVec 80)) =
    (8, 13, true, true) := by decide +kernel

example : observe (.inst (.mem .load16 999 (.addr 777 3)) : WordLangProgHOL (BitVec 64)) =
    (0, 5, true, true) := by decide +kernel

example : observe (.call none (some 999) [] (some (1000,.assign 1001 (.var 1002),1003,1004)) : WordLangProgHOL (BitVec 32)) =
    (0, 5, true, true) := by decide +kernel

example : observe (.call (some ([1],(.ln,.ln),.assign 26 (.const 0),7,8)) (some 0) [] none : WordLangProgHOL (BitVec 64)) =
    (26, 29, true, true) := by decide +kernel

example : observe (.assign 1208925819614629174706176 (.var 7) : WordLangProgHOL (BitVec 1)) =
    (1208925819614629174706176, 1208925819614629174706181, true, true) := by decide +kernel

example {width : Nat} [NeZero width] (program : WordLangProgHOL (BitVec width)) :
    limitVar program = maxVarHOL program + (4 - maxVarHOL program % 4) + 1 := rfl

end Flapjack.Test.WordAllocLimitVar
