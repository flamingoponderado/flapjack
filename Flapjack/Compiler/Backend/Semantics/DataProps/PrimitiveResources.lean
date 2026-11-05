import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateControl
import Flapjack.Compiler.Backend.BackendProps

/-! Resource observations of data-language primitive bookkeeping. -/
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

/-- Lift an auxiliary primitive's resource facts through the actual space,
limit, and stack accounting performed by the dispatcher. -/
theorem accounted_resource_frame {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state accounted next : State C F) (value : Value)
    (space : doSpace op args state = some accounted)
    (aux : doAppAux op args (doStack op args (doLimSafe accounted op args)) = .val (value, next))
    (auxFrame : ∀ (before after : State C F) (v : Value), doAppAux op args before = .val (v, after) →
      before.ffi.ioEvents <+: after.ffi.ioEvents ∧ BackendProps.optionLe before.stackMax after.stackMax ∧
      (after.safeForSpace = true → before.safeForSpace = true)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  have spaceFacts := doSpace_resource_frame op args state accounted space
  have limitFacts := doLimSafe_resource_frame op args accounted
  have stackFacts := doStack_resource_frame op args (doLimSafe accounted op args)
  have auxFacts := auxFrame _ next value aux
  refine ⟨?_, ?_, ?_⟩
  · simpa [stackFacts.1, limitFacts.1, spaceFacts.1] using auxFacts.1
  · apply BackendProps.optionLe_trans _ _ _ ⟨?_, auxFacts.2.1⟩
    simpa [limitFacts.2.1, spaceFacts.2.1] using stackFacts.2.2
  · intro safe
    exact spaceFacts.2.2 (limitFacts.2.2 (stackFacts.2.1 (auxFacts.2.2 safe)))

/-- Arithmetic auxiliary operations do not alter the state. -/
theorem doAppAux_int_resource_frame {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.intOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases result : doIntApp op args with
  | none => simp [doAppAux, applyNonFfi, result] at run
  | some number =>
    simp [doAppAux, applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [BackendProps.optionLe_refl]

/-- Word auxiliary operations, including floating-point words, do not alter
the state. -/
theorem doAppAux_word_resource_frame {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.wordOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases result : doWordApp op args with
  | none => simp [doAppAux, applyNonFfi, result] at run
  | some word =>
    simp [doAppAux, applyNonFfi, result] at run
    obtain ⟨rfl, rfl⟩ := run
    simp [BackendProps.optionLe_refl]

/-- Full integer primitive accounting respects the three observations. -/
theorem doApp_int_resource_frame {C F : Type} (op : ClosLang.IntOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.intOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases op <;> simp only [doApp] at run
  all_goals try simp at run
  all_goals split at run
  all_goals try simp at run
  all_goals rename_i accounted space
  all_goals exact accounted_resource_frame _ args state accounted next value space run (fun before after v h => doAppAux_int_resource_frame _ args before after v h)

/-- Full word primitive accounting respects the three observations. -/
theorem doApp_word_resource_frame {C F : Type} (op : ClosLang.WordOp) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.wordOp op) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.wordOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact accounted_resource_frame _ args state accounted next value space run
      (fun before after v h => doAppAux_word_resource_frame op args before after v h)

/-- A successful code-label lookup does not change source resources. -/
theorem doAppAux_label_resource_frame {C F : Type} (label : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.label label) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  cases args with
  | cons a rest => simp [doAppAux, applyNonFfi] at run
  | nil =>
    cases found : sptLookup label state.code with
    | none => simp [doAppAux, applyNonFfi, found] at run
    | some entry =>
      simp [doAppAux, applyNonFfi, found] at run
      obtain ⟨rfl, rfl⟩ := run
      simp [BackendProps.optionLe_refl]

/-- The production code-label dispatcher satisfies resource monotonicity. -/
theorem doApp_label_resource_frame {C F : Type} (label : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.label label) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧ BackendProps.optionLe state.stackMax next.stackMax ∧
      (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.label label) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    exact accounted_resource_frame _ args state accounted next value space run
      (fun before after v h => doAppAux_label_resource_frame label args before after v h)

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

/-- A successful FFI primitive satisfies all three resource monotonicity
properties through the full production accounting path. -/
theorem doApp_ffi_resource_frame {C F : Type} (name : Basis.Pure.MlString.MlString)
    (args : List Value) (state next : State C F) (value : Value)
    (run : doApp (.ffi name) args state = .val (value, next)) :
    state.ffi.ioEvents <+: next.ffi.ioEvents ∧
    BackendProps.optionLe state.stackMax next.stackMax ∧
    (next.safeForSpace = true → state.safeForSpace = true) := by
  simp only [doApp] at run
  cases space : doSpace (.ffi name) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have spaceFacts := doSpace_resource_frame (.ffi name) args state accounted space
    have limitFacts := doLimSafe_resource_frame (.ffi name) args accounted
    have stackFacts := doStack_resource_frame (.ffi name) args (doLimSafe accounted (.ffi name) args)
    have auxFacts := doAppAux_ffi_resource_frame name args _ next value run
    refine ⟨?_, ?_, ?_⟩
    · simpa [stackFacts.1, limitFacts.1, spaceFacts.1] using auxFacts.1
    · simpa [auxFacts.2.1, limitFacts.2.1, spaceFacts.2.1] using stackFacts.2.2
    · intro safe
      apply spaceFacts.2.2
      apply limitFacts.2.2
      apply stackFacts.2.1
      simpa [auxFacts.2.2] using safe


end Flapjack.Compiler.Backend.DataSem
