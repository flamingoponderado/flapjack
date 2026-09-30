import Flapjack.FpSemHOL
import Flapjack.Misc.MachineIeee

/-!
# Parity for the ported `fpSem` operation tables (`Flapjack.FpSemHOL`)

Kernel-checked definitional equalities showing that each `fpSem*Comp` clause is
exactly the corresponding rendered `machine_ieee`/`binary_ieee` `fp64_*`
operation, plus executable Boolean rows for the comparison operations.  The
tagged source is `cakeml/semantics/fpSemScript.sml:8-66`.
-/

namespace Flapjack.Test.FpSemOpsParity

open Flapjack

/-! ## Definitional equalities: each clause of the `*_comp` tables -/

example : fpSemFpCmpComp .less = holFp64LessThan := rfl

example : fpSemFpCmpComp .lessEqual = holFp64LessEqual := rfl

example : fpSemFpCmpComp .greater = holFp64GreaterThan := rfl

example : fpSemFpCmpComp .greaterEqual = holFp64GreaterEqual := rfl

example : fpSemFpCmpComp .equal = holFp64Equal := rfl

example : fpSemFpCmp .lt = holFp64LessThan := rfl

example : fpSemFpCmp .leq = holFp64LessEqual := rfl

example : fpSemFpCmp .gt = holFp64GreaterThan := rfl

example : fpSemFpCmp .geq = holFp64GreaterEqual := rfl

example : fpSemFpUopComp .abs = holFp64Abs := rfl

example : fpSemFpUopComp .neg = holFp64Negate := rfl

example : fpSemFpUopComp .sqrt = holFp64Sqrt .roundTiesToEven := rfl

example : fpSemFpBopComp .add = holFp64Add .roundTiesToEven := rfl

example : fpSemFpBopComp .sub = holFp64Sub .roundTiesToEven := rfl

example : fpSemFpBopComp .mul = holFp64Mul .roundTiesToEven := rfl

example : fpSemFpBopComp .div = holFp64Div .roundTiesToEven := rfl

example : fpSemFpTopComp .fma = fpSemFpfma := rfl

/-! ## Concrete Boolean rows, checked in the kernel -/

example : holFp64LessThan 1 2 = true := by decide +kernel

example : holFp64LessEqual 1 1 = true := by decide +kernel

example : holFp64GreaterThan 2 1 = true := by decide +kernel

example : holFp64GreaterEqual 1 1 = true := by decide +kernel

example : holFp64Equal 1 1 = true := by decide +kernel

example : holFp64LessThan 2 1 = false := by decide +kernel

example : fpSemFpCmpComp .less 1 2 = true := by decide +kernel

example : fpSemFpCmpComp .greater 2 1 = true := by decide +kernel

example : fpSemFpCmp .lt 1 2 = true := by decide +kernel

example : fpSemFpCmp .leq 1 1 = true := by decide +kernel

example : fpSemFpCmp .gt 2 1 = true := by decide +kernel

example : fpSemFpCmp .geq 1 1 = true := by decide +kernel

example : fpSemFpCmp .lt 2 1 = false := by decide +kernel

/-! ## Executable checks -/

def check (name : String) (actual : Bool) : IO Bool := do
  if actual then
    IO.println s!"PASS {name}"
    pure true
  else
    IO.println s!"FAIL {name}"
    pure false

def runChecks : IO Bool := do
  let results ← [
    check "fp64 lessThan 1 2" (holFp64LessThan 1 2),
    check "fp64 lessEqual 1 1" (holFp64LessEqual 1 1),
    check "fp64 greaterThan 2 1" (holFp64GreaterThan 2 1),
    check "fp64 greaterEqual 1 1" (holFp64GreaterEqual 1 1),
    check "fp64 equal 1 1" (holFp64Equal 1 1),
    check "fp64 not lessThan 2 1" (!holFp64LessThan 2 1),
    check "fp64 not greaterThan 1 2" (!holFp64GreaterThan 1 2),
    check "fp64 not greaterEqual 1 2" (!holFp64GreaterEqual 1 2),
    check "fp64 not equal 1 2" (!holFp64Equal 1 2) ].mapM id
  pure (results.all id)

end Flapjack.Test.FpSemOpsParity
