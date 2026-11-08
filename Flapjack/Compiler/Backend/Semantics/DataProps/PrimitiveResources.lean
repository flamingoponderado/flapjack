import Flapjack.Compiler.Backend.Semantics.DataProps.NonFfiResources
import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateControl
import Flapjack.Compiler.Backend.BackendProps

/-! Resource observations of data-language primitive applications. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Successful space accounting preserves FFI and stack maximum and cannot
turn an unsafe source state into a safe one. These are Flapjack helpers for
the source evaluator's resource monotonicity proof. -/
theorem doSpace_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (run : doSpace op args state = some next) :
    next.ffi = state.ffi ∧ next.stackMax = state.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  unfold doSpace at run
  split at run
  · simp only [Option.some.injEq] at run
    subst next
    simp
    tauto
  · dsimp only at run
    split at run
    · simp only [Option.some.injEq] at run
      subst next
      simp
    · simp only [consumeSpace] at run
      split at run
      · simp at run
      · simp only [Option.some.injEq] at run
        subst next
        simp

/-- Stack accounting preserves FFI events, cannot improve the safety flag,
and can only increase the optional maximum stack usage. -/
theorem doStack_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) :
    (doStack op args state).ffi = state.ffi ∧
    ((doStack op args state).safeForSpace = true → state.safeForSpace = true) ∧
    BackendProps.optionLe state.stackMax (doStack op args state).stackMax := by
  constructor
  · rfl
  constructor
  · simp [doStack]
    tauto
  · unfold doStack
    cases state.stackMax <;>
      cases Option.map₂ (· + ·) (stackConsumed state.stackFrameSizes state.limits op args)
        (Option.map₂ (· + ·) (sizeOfStack state.stack) state.localsSize) <;>
      simp [BackendProps.optionLe]

/-- Length checks and explicit limit checks preserve FFI and stack maximum
and never change an unsafe state to a safe state. -/
theorem doLimSafe_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) :
    (doLimSafe state op args).ffi = state.ffi ∧ (doLimSafe state op args).stackMax = state.stackMax ∧
      ((doLimSafe state op args).safeForSpace = true → state.safeForSpace = true) := by
  simp [doLimSafe]

/-- Successful installation does not change FFI events or the stack maximum
and always clears the safety flag. -/
theorem doInstall_resource_frame {C F R : Type} (args : List Value) (state next : State C F)
    (value : Value) (run : doInstall (R := R) args state = .val (value, next)) :
    next.ffi = state.ffi ∧ next.stackMax = state.stackMax ∧ next.safeForSpace = false := by
  simp only [doInstall] at run
  repeat' (split at run <;> try simp_all)
  all_goals obtain ⟨_, rfl⟩ := run
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- The production installation dispatcher resets the stack bound and safety
flag while retaining FFI events. -/
theorem doApp_install_resource_frame {C F : Type} (args : List Value) (state next : State C F)
    (value : Value) (run : doApp .install args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧
    BackendProps.optionLe state.stackMax next.stackMax ∧
    (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  have facts := doInstall_resource_frame args { state with stackMax := none, stackFrameSizes := .ln } next value run
  obtain ⟨ffi, stack, safe⟩ := facts
  simp [ffi, stack, safe, BackendProps.optionLe]

/-- A returning FFI application extends the event list while preserving the
resource fields; this is a component of the original primitive monotonicity results. -/
theorem doAppAux_ffi_resource_frame {C F : Type} (name : Basis.Pure.MlString.MlString) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.ffi name) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ next.stackMax = state.stackMax ∧
      next.safeForSpace = state.safeForSpace := by
  cases args with
  | nil => simp [doAppAux] at run
  | cons a rest =>
    cases rest with
    | nil => simp [doAppAux] at run
    | cons b rest =>
      cases rest with
      | cons c tail => simp [doAppAux] at run
      | nil =>
        cases a with
        | number n => simp [doAppAux] at run
        | word64 w => simp [doAppAux] at run
        | codePtr p => simp [doAppAux] at run
        | block ts tag vs => simp [doAppAux] at run
        | refPtr flag configPtr =>
          cases b with
          | number n => simp [doAppAux] at run
          | word64 w => simp [doAppAux] at run
          | codePtr p => simp [doAppAux] at run
          | block ts tag vs => simp [doAppAux] at run
          | refPtr bit ptr =>
            cases configFound : sptLookup configPtr state.refs with
            | none => simp [doAppAux, configFound] at run
            | some configEntry =>
              cases configEntry with
              | valueArray values => simp [doAppAux, configFound] at run
              | thunk mode value => simp [doAppAux, configFound] at run
              | mutBlock tag done left child right => simp [doAppAux, configFound] at run
              | byteArray immutable config =>
                cases immutable with
                | false => simp [doAppAux, configFound] at run
                | true =>
                  cases bytesFound : sptLookup ptr state.refs with
                  | none => simp [doAppAux, configFound, bytesFound] at run
                  | some bytesEntry =>
                    cases bytesEntry with
                    | valueArray values => simp [doAppAux, configFound, bytesFound] at run
                    | thunk mode value => simp [doAppAux, configFound, bytesFound] at run
                    | mutBlock tag done left child right => simp [doAppAux, configFound, bytesFound] at run
                    | byteArray mutable bytes =>
                      cases mutable with
                      | true => simp [doAppAux, configFound, bytesFound] at run
                      | false =>
                        cases call : callFFIHOL state.ffi (.extCall name) config bytes with
                        | final outcome => simp [doAppAux, configFound, bytesFound, call] at run
                        | ret ffi updated =>
                          simp [doAppAux, configFound, bytesFound, call] at run
                          obtain ⟨rfl, rfl⟩ := run
                          exact ⟨callFFIHOL_return_ioEvents_prefix state.ffi (.extCall name) config bytes ffi updated call, rfl, rfl⟩

/-- Every successful auxiliary application preserves the event prefix and resource ordering. -/
theorem doAppAux_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux op args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  by_cases ffi : ∃ name, op = .ffi name
  · obtain ⟨name, rfl⟩ := ffi
    obtain ⟨events, stack, safe⟩ := doAppAux_ffi_resource_frame name args state next value run
    exact ⟨events, by simpa [stack] using BackendProps.optionLe_refl state.stackMax, by simp [safe]⟩
  · have app : applyNonFfi op args state = some (value, next) := by
      simp only [doAppAux] at run
      repeat' (split at run <;> try simp_all)
    obtain ⟨sameFfi, safe⟩ := (applyNonFfi_successFields op args state next value state.safeForSpace app).2
    have stack := (doAppAux_fieldFrame op args state next value run).2.2.1
    exact ⟨by simp [sameFfi], by simpa [stack] using BackendProps.optionLe_refl state.stackMax, safe⟩

/-- Lift an auxiliary primitive's resource facts through the actual space,
limit, and stack accounting performed by the dispatcher. -/
theorem accounted_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state accounted next : State C F) (value : Value)
    (space : doSpace op args state = some accounted)
    (aux : doAppAux op args (doStack op args (doLimSafe accounted op args)) = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  have spaceFacts := doSpace_resource_frame op args state accounted space
  have limitFacts := doLimSafe_resource_frame op args accounted
  have stackFacts := doStack_resource_frame op args (doLimSafe accounted op args)
  have auxFacts := doAppAux_resource_frame op args _ next value aux
  refine ⟨?_, ?_, ?_⟩
  · simpa [stackFacts.1, limitFacts.1, spaceFacts.1] using auxFacts.1
  · apply BackendProps.optionLe_trans _ _ _ ⟨?_, auxFacts.2.1⟩
    simpa [limitFacts.2.1, spaceFacts.2.1] using stackFacts.2.2
  · intro safe
    exact spaceFacts.2.2 (limitFacts.2.2 (stackFacts.2.1 (auxFacts.2.2 safe)))

end Flapjack.Compiler.Backend.DataSem
