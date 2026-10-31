import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
import Flapjack.Misc.LprefixLub

/-! Whole-program observations of the BVI evaluator. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.SemanticPrimitivesHOL

/-- A terminating observation of an initial BVI call. This is auxiliary
infrastructure for the Flapjack whole-program semantics. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (behavior : HolBehaviour) : Prop :=
  ∃ clock result state outcome,
    evaluateTuple ([.call 0 (some start) [] none], [],
      initialState ffi code oracle compiler clock) = (result, state) ∧
    (match result with
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | .val _ => outcome = HolOutcome.success
     | _ => False) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Observable behavior of an initial BVI program. This remains untagged
until the evaluator and its internally used finite-map state representation
have been reviewed against the source semantics. -/
noncomputable def semantics {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) : HolBehaviour :=
  open Classical in
  let run := fun clock => evaluateTuple ([.call 0 (some start) [] none], [],
    initialState ffi code oracle compiler clock)
  if ∃ clock error, (run clock).1 = .err error ∧
      error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event) then .fail
  else match holOptionSome (terminatingObservation ffi code oracle compiler start) with
  | some behavior => behavior
  | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (run clock).2.ffi.ioEvents))

end Flapjack.Compiler.Backend.BviSem
