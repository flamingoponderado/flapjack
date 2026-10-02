import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClockIoEventsMono
namespace Flapjack.Test.TargetPropsClockIoEventsParity
open Flapjack
-- Original tp_clock_io_full_statement=T: full statement, sole clock-order premise.
example {width : Nat} [NeZero width] {state projection : Type} {σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ)
    (k : Nat) (ms : state) (kprime : Nat) (hle : k ≤ kprime) :
    (evaluateTargetHOL mc ffi k ms).2.2.ioEvents <+:
      (evaluateTargetHOL mc ffi kprime ms).2.2.ioEvents :=
  evaluateTargetAddClockIoEventsMono mc ffi k ms kprime hle
end Flapjack.Test.TargetPropsClockIoEventsParity
