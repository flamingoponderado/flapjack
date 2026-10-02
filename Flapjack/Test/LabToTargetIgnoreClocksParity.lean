import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks
namespace Flapjack.Test.LabToTargetIgnoreClocksParity
open Flapjack
example {width : Nat} [NeZero width]
    {state projection : Type} {σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (k k' : Nat) (ms : state)
    (r1 r2 : MachineResult) (ms1 ms2 : state) (st1 st2 : HolFfiState σ)
    (h : evaluateTargetHOL mc ffi k ms = (r1, ms1, st1) ∧ r1 ≠ .timeOut ∧
      evaluateTargetHOL mc ffi k' ms = (r2, ms2, st2) ∧ r2 ≠ .timeOut) :
    (r1, ms1, st1) = (r2, ms2, st2) :=
  evaluateTargetIgnoreClocks mc ffi k k' ms r1 r2 ms1 ms2 st1 st2 h
end Flapjack.Test.LabToTargetIgnoreClocksParity
