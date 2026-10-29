import Flapjack.Compiler.Backend.FlatToClos.Proofs.CopyUpdate

/-! FFI cases for the proof-side flat-to-closure simulation. These lemmas
are Flapjack infrastructure and have not been reviewed as HOL ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- A returning FFI call updates corresponding byte arrays and external
states on both sides. -/
theorem ffiReturn_related {C F : Type} (source : FlatSem.State C F)
    (target : ClosSem.State C F) (pointer : Nat) (flag : Bool)
    (bytes updated : List HolChar) (configuration name : MlString)
    (ffi : Flapjack.HolFfiState F) (states : StateRel source target)
    (found : storeLookup pointer source.refs = some (.w8array bytes))
    (call : Flapjack.callFFIHOL source.ffi (.extCall name) configuration.explode bytes = .ret ffi updated) :
    ∃ targetNext,
      FlatSem.doAppData source (.ffi name) [.litv (.strLit configuration), .loc flag pointer] =
        some (some ({ source with refs := source.refs.set pointer (.w8array updated), ffi := ffi }, .val FlatSem.unitValue)) ∧
      ClosSem.doApp (.ffi name) [.byteVector configuration.explode, .refPtr flag pointer] target =
        .val (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set pointer (.w8array updated), ffi := ffi } targetNext := by
  have targetFound := lookup_byteArray states found
  have foundList : source.refs[pointer]? = some (.w8array bytes) := by simpa [storeLookup] using found
  have newStores := storeRel_setByteArray source.refs target.refs pointer bytes updated states.2.2.2.1 foundList
  have targetCall : Flapjack.callFFIHOL target.ffi (.extCall name) configuration.explode bytes = .ret ffi updated := by
    rw [← states.2.1]
    exact call
  refine ⟨{ target with refs := target.refs.updateEq (pointer, .byteArray updated), ffi := ffi }, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppData, storeLookup, foundList, call, storeAssign, storeValueSameType]
  · simp [ClosSem.doApp, targetFound, targetCall]
  · rcases states with ⟨maxApp, _, clock, _, globals, values, install⟩
    exact ⟨maxApp, rfl, clock, newStores, globals, values, install⟩

/-- FFI application requires exactly two arguments. -/
theorem ffi_wrong_arity {C F : Type} (state : FlatSem.State C F) (name : MlString)
    (args : List FlatSem.Value) (wrong : args.length ≠ 2) :
    (FlatSem.applyResult state (.src (.ffi name)) args).2 = .err (.abort .typeError) := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  all_goals simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
    FlatSem.doAppMemory, FlatSem.doAppData]

/-- FFI expressions simulate argument evaluation, external calls, returned
byte-array updates, and terminal FFI events. -/
theorem evaluate_ffi {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (name : MlString) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src (.ffi name)) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src (.ffi name)) args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps, compileExp, compileOp] at ⊢
  simp only [compile, compileExps_reverse] at argsSim
  rw [FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultShape : (FlatSem.applyResult next (.src (.ffi name)) sourceArgs.reverse).2 ≠
            .err (.abort .typeError) := by
          have fixed := flatFix
          rw [flatRun] at fixed
          have h := notTypeError
          rw [FlatSem.evaluate, flatRun, fixed] at h
          simpa using h
        have argLength : sourceArgs.length = 2 := by
          by_contra wrong
          apply resultShape
          apply ffi_wrong_arity
          simpa using wrong
        cases related with
        | nil => simp at argLength
        | cons pointerRel tail =>
          cases tail with
          | nil => simp at argLength
          | cons configRel tail =>
            cases tail with
            | cons _ _ => simp at argLength
            | nil =>
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at resultShape
              cases configRel <;>
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                  FlatSem.doAppMemory, FlatSem.doAppData] at resultShape
              case string configuration =>
                cases pointerRel <;> try simp at resultShape
                case loc flag pointer =>
                  cases found : storeLookup pointer next.refs with
                  | none => simp [found] at resultShape
                  | some entry =>
                    cases entry <;> simp [found] at resultShape
                    case w8array bytes =>
                      have targetFound := lookup_byteArray states found
                      cases call : Flapjack.callFFIHOL next.ffi (.extCall name) configuration.explode bytes with
                      | ret ffi updated =>
                        obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                          ffiReturn_related next nextTarget pointer flag bytes updated configuration name ffi states found call
                        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          sourceUpdate, targetUpdate, updatedStates, FlatSem.unitValue, ClosSem.unitValue,
                          EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]
                      | final event =>
                        have targetCall : Flapjack.callFFIHOL nextTarget.ffi (.extCall name) configuration.explode bytes = .final event := by
                          rw [← states.2.1]
                          exact call
                        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
                          FlatSem.doAppData, found, call, ClosSem.doApp, targetFound, targetCall, states,
                          EvalResultRel.abort (.ffiError event)]

end Flapjack.Compiler.Backend.FlatToClos
