import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateIoEventsMono
namespace Flapjack.Test.TargetPropsIoEventsParity
open Flapjack
-- Original tp_io_full_statement=T: entire quantified statement, no premise.
example {width : Nat} [NeZero width] {state projection : Type} {σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (k : Nat) (ms : state) :
    ffi.ioEvents <+: (evaluateTargetHOL mc ffi k ms).2.2.ioEvents :=
  evaluateTargetIoEventsMono mc ffi k ms
end Flapjack.Test.TargetPropsIoEventsParity
