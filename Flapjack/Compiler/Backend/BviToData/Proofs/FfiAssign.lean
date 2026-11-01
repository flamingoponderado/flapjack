import Flapjack.Compiler.Backend.BviToData.Proofs.Compare
import Flapjack.Compiler.Backend.BviToData.Proofs.ApplyFfi

/-! Terminal FFI behavior of compiled data-language assignments. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A terminal FFI outcome in BVI is the same terminal result of the actual
compiled assignment, including its live-name cut and state flushing. -/
theorem evaluate_iAssign_ffiError {C F : Type} (name : Basis.Pure.MlString.MlString)
    (target : DataSem.State C F) (source : BviSem.BviState C F)
    (operands live corr : List Nat) (env : List BvlSem.Value)
    (args : List DataSem.Value) (dest : Nat) (event : HolFinalEvent)
    (related : stateRel source target)
    (vars : DataProps.varCorr env corr (sptMap dataToBviValue target.locals))
    (livePresent : ∀ key ∈ live, sptLookup key target.locals ≠ none)
    (read : DataSem.getVars operands target.locals = some args)
    (run : BviSem.doApp (.ffi name) (args.map dataToBviValue) source = .err (.abort (.ffiError event))) :
    ∃ targetNext,
      DataSem.evaluate (iAssign dest (.ffi name) operands live corr) target =
        (some (.err (.abort (.ffiError event))), targetNext) ∧ stateRel source targetNext := by
  let roots := operands ++ live ++ corr
  let cut := sptMkWf (sptInter target.locals (namesOfList roots))
  let prepared := { target with locals := cut }
  have rootsPresent : ∀ key ∈ roots, sptLookup key target.locals ≠ none :=
    roots_present target operands live corr env args vars livePresent read
  have cutRel : stateRel source prepared := by simpa [prepared, stateRel] using related
  have cutEnv : DataSem.cutEnv (namesOfList roots) target.locals = some cut :=
    cutEnv_namesOfList roots target.locals rootsPresent
  simp only [roots, List.append_assoc] at cutEnv
  have ffiError := doApp_ffi_error name args source prepared event cutRel run
  refine ⟨DataSem.flushState true (DataSem.installSfs (.ffi name) prepared), ?_, ?_⟩
  · simp [iAssign, DataLang.opRequiresNames, DataLang.opSpaceReset, DataSem.evaluate, read,
      DataSem.cutStateOpt, DataSem.cutState, List.append_assoc, cutEnv, ffiError, prepared]
  · simpa [stateRel, DataSem.flushState, DataSem.installSfs, prepared] using related

end Flapjack.Compiler.Backend.BviToData
