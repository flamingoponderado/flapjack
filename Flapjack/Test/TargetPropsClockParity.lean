import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock
import Flapjack.Test.TargetSemEvaluateParity

namespace Flapjack.Test.TargetPropsClockParity
open Flapjack

-- Original HOL tp_clock_statement=T. Same complete generic statement.
example {width : Nat} [NeZero width] {state projection : Type} {σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (k : Nat)
    (ms : state) (extra : Nat) (result : MachineResult) (ms1 : state) (ffi1 : HolFfiState σ)
    (h : evaluateTargetHOL mc ffi k ms = (result, ms1, ffi1)) (hnt : result ≠ .timeOut) :
    evaluateTargetHOL mc ffi (k + extra) ms = (result, ms1, ffi1) :=
  evaluateTargetAddClock mc ffi k ms extra result ms1 ffi1 h hnt

-- Original HOL tp_halt_stable=T: clocks one and five, whole state/FFI triple.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (TargetSemEvaluateParity.fixture mc) with haltPc := 0 } ffi 1 7 =
      evaluateTargetHOL { (TargetSemEvaluateParity.fixture mc) with haltPc := 0 } ffi 5 7 := by
  simp [evaluateTargetHOL, TargetSemEvaluateParity.fixture]

-- Original HOL tp_error_stable=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (TargetSemEvaluateParity.fixture mc) ffi 1 7 =
      evaluateTargetHOL (TargetSemEvaluateParity.fixture mc) ffi 5 7 := by
  simp [evaluateTargetHOL, TargetSemEvaluateParity.fixture, Misc.findIndex]

end Flapjack.Test.TargetPropsClockParity
