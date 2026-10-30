import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Misc.LprefixLub

/-! Whole-program observations of the BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL

/-- A terminating observation of an initial BVL call. This is auxiliary
infrastructure for the Flapjack whole-program semantics. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) (behavior : HolBehaviour) : Prop :=
  ∃ clock result state outcome,
    evaluateTuple ([.call 0 (some start) []], [], initialState ffi code oracle compiler clock) = (result, state) ∧
    (match result with
     | .err (.abort .timeoutError) => False
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | _ => outcome = HolOutcome.success) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Observable behavior of an initial BVL program. This is untagged pending
representation review of the finite map in the internally used evaluator
state; the existing finite-map qualifier requires its owner in the signature. -/
noncomputable def semantics {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvl.Exp)) (oracle : CompileOracle C)
    (compiler : Compiler C) (start : Nat) : HolBehaviour :=
  open Classical in
  let run := fun clock => evaluateTuple ([.call 0 (some start) []], [],
    initialState ffi code oracle compiler clock)
  if ∃ clock, (run clock).1 = .err (.abort .typeError) then .fail
  else match holOptionSome (terminatingObservation ffi code oracle compiler start) with
  | some behavior => behavior
  | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
      trace = HolLList.fromList (run clock).2.ffi.ioEvents))

end Flapjack.Compiler.Backend.BvlSem
