import Flapjack.Pancake.CrepToLoop.ContextExact

/-!
Build-time replay of the six `crep_to_loop$ocompile_def` direct HOL EVAL rows
in `scripts/hol-probes/crep_to_loop_ocompile_probe.out` against the exact Lean
port `ocompileHOLExact` (`Flapjack.Pancake.CrepToLoop.ContextExact`). The rows
are replayed by `#guard`, so they are evaluated during Lean elaboration (build
and test execution); they are not kernel-checked theorems.

The expected shapes are the unwrapped original-HOL terms: `LN` is `Spt.ln`,
`NotEqual` is `Cmp.notEqual`, `Imm 3w` is `RegImm.imm (3 : BitVec 8)`, and
`AddCarry` is `PrimOp.addCarry`.
-/

namespace Flapjack.Test.CrepToLoopOcompileHOLParity

open Flapjack
open Flapjack.Basis.Pure.MlString

/-- Exact HOL probe context:
`context (FEMPTY |+ (1,7) |+ (2,8) |+ (3,9) |+ (4,10))
   (FEMPTY |+ (strlit "f", (42,2))) 4 RISC_V`. -/
def context : CrepToLoopContextExact :=
  { vars :=
      (HolFiniteMapExact.empty.updateEq (1, 7)).updateEq (2, 8) |>.updateEq (3, 9)
        |>.updateEq (4, 10)
    funcs := HolFiniteMapExact.empty.updateEq (ofString "f", (42, 2))
    vmax := 4
    target := .riscv }

/-- The probe's `live = insert 2 () (insert 1 () LN)`. -/
def live : NumSet := sptListInsert [1, 2] .ln

/-- Structural replay of the six direct HOL `ocompile` rows. `HolLoopProg` has
no `DecidableEq`, so each row is matched against its exact constructor shape. -/
def ocompileGuard : Bool :=
  (match ocompileHOLExact context live (.skip : CrepProgHOL 8) with
  | .mark .skip => true
  | _ => false) &&
  (match ocompileHOLExact context live (.tick : CrepProgHOL 8) with
  | .mark .tick => true
  | _ => false) &&
  (match ocompileHOLExact context live (.assign 1 (.var 2) : CrepProgHOL 8) with
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false) &&
  (match ocompileHOLExact context live (.primitive [1] .addCarry [2] : CrepProgHOL 8) with
  | .mark (.primitive [7] .addCarry [8]) => true
  | _ => false) &&
  (match ocompileHOLExact context live
      (.return [.const (5 : BitVec 8)] : CrepProgHOL 8) with
  | .mark (.seq (.mark (.assign 5 (.const 5)))
      (.mark (.seq (.mark (.return [5])) (.mark .skip)))) => true
  | _ => false) &&
  (match ocompileHOLExact context live
      (.call (some ([1], some ((3 : BitVec 8), .break 7))) (ofString "f")
        [.const (16 : BitVec 8)] : CrepProgHOL 8) with
  | .mark (.seq (.mark (.assign 5 (.const 16)))
      (.mark (.seq
        (.mark (.call (some ([7], .ln)) (some 42) [5]
          (some (5,
            .mark (.ite .notEqual 5 (.imm (3 : BitVec 8)) (.mark (.raise 5))
              (.mark (.seq (.mark .tick) (.mark (.break 7)))) .ln),
            .mark .skip, .ln))))
        (.mark .skip)))) => true
  | _ => false)

#guard ocompileGuard

def runChecks : IO Bool := do
  if ocompileGuard then
    IO.println "PASS exact ocompileHOL matches all 6 crep_to_loop ocompile HOL rows (#guard build-time replay)"
    pure true
  else
    IO.println "FAIL exact ocompileHOL does not match the crep_to_loop ocompile HOL rows (#guard build-time replay)"
    pure false

end Flapjack.Test.CrepToLoopOcompileHOLParity
