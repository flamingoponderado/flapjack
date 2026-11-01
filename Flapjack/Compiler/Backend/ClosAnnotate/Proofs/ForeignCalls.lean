import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.BlockExtend
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.IntegerOperations
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.WordOperations

/-! Foreign-call primitives under the closure-annotation state relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Updating corresponding references and the shared FFI state preserves the
candidate state relation. -/
theorem stateRel_updateRefFfi {C F : Type} (source target : State C F) (states : StateRel source target)
    (index : Nat) (left right : Ref Value) (refsRel : RefRel left right) (ffi : HolFfiState F) :
    StateRel { source with refs := source.refs.updateEq (index, left), ffi := ffi }
      { target with refs := target.refs.updateEq (index, right), ffi := ffi } := by
  refine ⟨states.1, rfl, states.2.2.1, states.2.2.2.1, states.2.2.2.2.1,
    states.2.2.2.2.2.1, ?_, states.2.2.2.2.2.2.2⟩
  intro key
  by_cases same : key = index
  · subst key
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, OptionRel] using refsRel
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using states.2.2.2.2.2.2.1 key

/-- An FFI call uses the same bytes and shared external-call state on both
sides; final events and returned byte arrays are related. -/
theorem primitiveSimulation_ffi {C F : Type} (name : Basis.Pure.MlString.MlString) :
    PrimitiveSimulation (C := C) (F := F) (.ffi name) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
  | cons first rest =>
    cases rest with
    | nil =>
      exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
    | cons second rest =>
      cases rest with
      | nil =>
        cases first with
        | byteVector config =>
          cases second with
          | refPtr flag index =>
            have refRel := states.2.2.2.2.2.2.1 index
            cases sourceRef : source.refs.lookup index with
            | none =>
              cases targetRef : target.refs.lookup index with
              | none =>
                exact ⟨.err (.abort .typeError), by simp [doApp, targetRef], by
                  simp [doApp, sourceRef, AppResultRel, ResultRel]⟩
              | some ref => simp [sourceRef, targetRef, OptionRel] at refRel
            | some ref =>
              cases targetRef : target.refs.lookup index with
              | none => simp [sourceRef, targetRef, OptionRel] at refRel
              | some nextRef =>
                have refs : RefRel ref nextRef := by simpa [sourceRef, targetRef, OptionRel] using refRel
                cases ref with
                | valueArray fields =>
                  cases nextRef <;> simp [RefRel] at refs
                  exact ⟨.err (.abort .typeError), by simp [doApp, targetRef], by
                    simp [doApp, sourceRef, AppResultRel, ResultRel]⟩
                | thunk mode value =>
                  cases nextRef <;> simp [RefRel] at refs
                  exact ⟨.err (.abort .typeError), by simp [doApp, targetRef], by
                    simp [doApp, sourceRef, AppResultRel, ResultRel]⟩
                | byteArray bytes =>
                  cases nextRef with
                  | valueArray fields => simp [RefRel] at refs
                  | thunk mode value => simp [RefRel] at refs
                  | byteArray nextBytes =>
                    have sameBytes : bytes = nextBytes := refs
                    subst nextBytes
                    have sameFfi := states.2.1
                    cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                    | final event =>
                      refine ⟨.err (.abort (.ffiError event)), ?_, ?_⟩
                      · simp [doApp, targetRef, ← sameFfi, call]
                      · simp [doApp, sourceRef, call, AppResultRel, ResultRel]
                    | ret nextFfi updated =>
                      have updatedStates := stateRel_updateRefFfi source target states index
                        (.byteArray updated) (.byteArray updated) rfl nextFfi
                      refine ⟨.val (unitValue, { target with refs := target.refs.updateEq (index, .byteArray updated), ffi := nextFfi }), ?_, ?_⟩
                      · simp [doApp, targetRef, ← sameFfi, call]
                      · simp only [doApp, sourceRef, call, AppResultRel]
                        exact ⟨.block _ [] [] .nil, updatedStates⟩
          | _ => exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
        | _ => cases second <;> exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩
      | cons third rest =>
        exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩

/-- Foreign calls are simulated when their arguments are. -/
theorem evaluate_ffi_op {C F : Type} (trace : BackendCommon.Tra) (name : Basis.Pure.MlString.MlString)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.ffi name) args] :=
  evaluate_ordinary_op trace _ args (by intro h; cases h) (by intro h; cases h)
    argsIH (primitiveSimulation_ffi name)

/-- The current proof-side dispatcher rejects labels on both sides. -/
theorem primitiveSimulation_label {C F : Type} (label : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.label label) := by
  intro values nextValues source target valuesRel states
  exact ⟨.err (.abort .typeError), by simp [doApp], by simp [doApp, AppResultRel, ResultRel]⟩

/-- Primitive simulation for all non-memory operations whose evaluator
does not enter installation or thunk control flow. -/
theorem primitiveSimulation_nonMemory {C F : Type} (op : ClosLang.Op)
    (notMemory : ∀ mem, op ≠ .memOp mem) (notThunk : ∀ thunk, op ≠ .thunkOp thunk)
    (notInstall : op ≠ .install) : PrimitiveSimulation (C := C) (F := F) op := by
  cases op with
  | label label => exact primitiveSimulation_label label
  | ffi name => exact primitiveSimulation_ffi name
  | intOp operation => exact primitiveSimulation_int operation
  | wordOp operation => exact primitiveSimulation_word operation
  | blockOp operation => exact primitiveSimulation_block operation
  | globOp operation => exact primitiveSimulation_globalOp operation
  | memOp operation => exact False.elim (notMemory operation rfl)
  | thunkOp operation => exact False.elim (notThunk operation rfl)
  | install => exact False.elim (notInstall rfl)

/-- The candidate evaluator simulates all ordinary non-memory operations. -/
theorem evaluate_nonMemory_op {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (notMemory : ∀ mem, op ≠ .memOp mem)
    (notThunk : ∀ thunk, op ≠ .thunkOp thunk) (notInstall : op ≠ .install)
    (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace op args] :=
  evaluate_ordinary_op trace op args notInstall (notThunk _) argsIH
    (primitiveSimulation_nonMemory op notMemory notThunk notInstall)

end Flapjack.Compiler.Backend.ClosAnnotate
