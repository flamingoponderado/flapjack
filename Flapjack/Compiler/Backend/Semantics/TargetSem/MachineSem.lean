import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate
import Flapjack.Misc.LprefixLub

namespace Flapjack

/-- Literal target machine behaviour relation. Termination uses an actual
Halt result and its exact event list; divergence requires TimeOut at every
natural clock and the least upper bound of the entire clock-indexed trace set;
failure requires an actual Error result. The IMAGE/UNIV set is represented
by its existential membership predicate, without bounding the clocks. -/
@[hol "cakeml/compiler/backend/semantics/targetSemScript.sml" "machine_sem_def"
  (words_as_type_indexed_bitvec)]
def machineSemHOL {width : Nat} [NeZero width] {state projection : Type} {σ : Type}
    (mc : MachineConfig width state projection) (ffi : HolFfiState σ) (ms : state) :
    HolBehaviour → Prop
  | .terminate outcome events =>
      ∃ k ms' ffi', evaluateTargetHOL mc ffi k ms = (.halt outcome, ms', ffi') ∧
        ffi'.ioEvents = events
  | .diverge trace =>
      (∀ k, ∃ ms' ffi', evaluateTargetHOL mc ffi k ms = (.timeOut, ms', ffi')) ∧
        HolLList.lprefixLub
          (fun ll => ∃ k : Nat,
            HolLList.fromList (evaluateTargetHOL mc ffi k ms).2.2.ioEvents = ll) trace
  | .fail => ∃ k, (evaluateTargetHOL mc ffi k ms).1 = .error

end Flapjack
