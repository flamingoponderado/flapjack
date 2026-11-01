import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Misc.LprefixLub
import Flapjack.HolArb

/-! Whole-program observations of the data-language evaluator. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL
open Classical

/-- Whether an execution ends in a space-safe state. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "evaluate_safe_def"]
noncomputable def evaluateSafe {C F : Type} (program : DataLang.Prog) (state : State C F) : Bool :=
  (evaluate program state).2.safeForSpace

/-- Peak heap length observed during an execution. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "evaluate_peak_def"]
noncomputable def evaluatePeak {C F : Type} (program : DataLang.Prog) (state : State C F) : Nat :=
  (evaluate program state).2.peakHeapLength

/-- A terminating observation of the initial call. This predicate factors the
source's guarded choice and has no independent HOL declaration. -/
def terminatingObservation {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C) (compiler : Compiler C)
    (limits : Limits) (frameSizes : Spt Nat) (start : Nat) (behavior : HolBehaviour) : Prop :=
  ∃ clock state result outcome,
    evaluate (.call none (some start) [] none)
      (initialState ffi code oracle compiler true limits frameSizes clock) = (some result, state) ∧
    (match result with
     | .err (.abort (.ffiError event)) => outcome = HolOutcome.ffiOutcome event
     | .val _ => outcome = HolOutcome.success
     | _ => False) ∧
    behavior = HolBehaviour.terminate outcome state.ffi.ioEvents

/-- Original whole-program behavior, including fatal outcomes and the least
upper bound of all finite-clock FFI traces. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "semantics_def"]
noncomputable def semantics {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C) (compiler : Compiler C)
    (limits : Limits) (frameSizes : Spt Nat) (start : Nat) : HolBehaviour :=
  let run := fun clock => evaluate (.call none (some start) [] none)
    (initialState ffi code oracle compiler true limits frameSizes clock)
  if ∃ clock, match (run clock).1 with
      | none => True
      | some (.err error) => error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
      | _ => False then .fail
  else match holOptionSome (terminatingObservation ffi code oracle compiler limits frameSizes start) with
    | some behavior => behavior
    | none => .diverge (HolLList.buildLprefixLub (fun trace => ∃ clock,
        trace = HolLList.fromList (run clock).2.ffi.ioEvents))

/-- Space safety for every initial clock with HOL's arbitrary compiler and
oracle at the unit configuration type. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "data_lang_safe_for_space_def"]
noncomputable def dataLangSafeForSpace {F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (limits : Limits) (frameSizes : Spt Nat) (start : Nat) : Prop :=
  let oracle : CompileOracle Unit := @holArb (CompileOracle Unit) ⟨fun _ => ((), [])⟩
  let compiler : Compiler Unit := @holArb (Compiler Unit) ⟨fun _ _ => none⟩
  ∀ clock, (evaluate (.call none (some start) [] none)
    (initialState ffi code oracle compiler true limits frameSizes clock)).2.safeForSpace = true

/-- Construct the data-language limits from the backend configuration. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "compute_limits_def"]
def computeLimits (lengthBits : Nat) (arch64 fpOps fpTops : Bool) (stackHeapLimit : Nat × Nat) : Limits :=
  ⟨stackHeapLimit.2, lengthBits, stackHeapLimit.1, arch64, fpOps, fpTops⟩

end Flapjack.Compiler.Backend.DataSem
