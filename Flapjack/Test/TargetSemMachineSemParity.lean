import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem

namespace Flapjack.Test.TargetSemMachineSemParity
open Flapjack

-- Original HOL ts_terminate_clause=T: all witnesses and event equality retained.
example {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state)
    (outcome : HolOutcome) (events : List HolIoEvent) :
    machineSemHOL mc ffi ms (.terminate outcome events) ↔
      ∃ k ms' ffi', evaluateTargetHOL mc ffi k ms = (.halt outcome, ms', ffi') ∧
        ffi'.ioEvents = events := Iff.rfl

-- Original HOL ts_diverge_clause=T: no clock bound or assumed trace equality.
example {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state)
    (trace : HolLList HolIoEvent) :
    machineSemHOL mc ffi ms (.diverge trace) ↔
      (∀ k, ∃ ms' ffi', evaluateTargetHOL mc ffi k ms = (.timeOut, ms', ffi')) ∧
        HolLList.lprefixLub
          (fun ll => ∃ k : Nat,
            HolLList.fromList (evaluateTargetHOL mc ffi k ms).2.2.ioEvents = ll) trace := Iff.rfl

-- Original HOL ts_fail_clause=T: actual evaluator Error projection.
example {width : Nat} [NeZero width] {state projection σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) :
    machineSemHOL mc ffi ms .fail ↔ ∃ k, (evaluateTargetHOL mc ffi k ms).1 = .error := Iff.rfl

end Flapjack.Test.TargetSemMachineSemParity
