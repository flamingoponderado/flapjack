import Flapjack.Pancake.CrepToLoop.Optimise

/-! Exact-carrier regressions for original HOL `crep_to_loop$comp_func_def`
rows in `scripts/hol-probes/crep_to_loop_comp_func_probe.out`. -/

namespace Flapjack.Test.CrepToLoopCompFuncExactParity

open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

private instance : NeZero 8 := ⟨by decide⟩

private abbrev P8 := HolLoopProg 8

def compFuncExactGuard : Bool :=
  (match compFuncHOLExact (width := 8) .riscv
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (Nat × Nat))
      [] (.skip : CrepProgHOL 8) with
   | .skip => true | _ => false) &&
  (match compFuncHOLExact (width := 8) .riscv
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (Nat × Nat))
      [5] (.return [.var 5] : CrepProgHOL 8) with
   | .seq (.assign 1 (.var 0)) (.seq (.return [1]) .skip) => true
   | _ => false) &&
  (match compFuncHOLExact (width := 8) .riscv
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (Nat × Nat))
      [5, 7] (.return [.var 5, .var 7] : CrepProgHOL 8) with
   | .seq (.assign 2 (.var 0))
       (.seq (.assign 3 (.var 1)) (.seq (.return [2, 3]) .skip)) => true
   | _ => false) &&
  (match compFuncHOLExact (width := 8) .riscv
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (Nat × Nat))
      [5, 5] (.return [.var 5] : CrepProgHOL 8) with
   | .seq (.assign 2 (.var 1)) (.seq (.return [2]) .skip) => true
   | _ => false) &&
  (match compFuncHOLExact (width := 8) .riscv
      (HolFiniteMapExact.empty : HolFiniteMapExact MlString (Nat × Nat))
      [5, 7, 9] (.ite (.const 1) .skip .skip : CrepProgHOL 8) with
   | .seq (.assign 3 (.const 1))
       (.seq (.ite .notEqual 3 (.imm 0) .skip .skip live) .skip) =>
       decide (live = sptListToNumSet [0, 1, 2])
   | _ => false)

#guard compFuncExactGuard

end Flapjack.Test.CrepToLoopCompFuncExactParity
