module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

@[expose] public section

/-! Source-side inversion used by the data-to-word FFI assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend

/-- Inverting a successful FFI primitive exposes the two reference reads and
the actual foreign-call return used in the HOL assignment proof. This is a
factoring of the `do_app_aux` case analysis, not a separate HOL declaration. -/
private theorem doAppAux_ffi_success {C F : Type}
    (name : Basis.Pure.MlString.MlString) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doAppAux (.ffi name) args state = .val (value, next)) :
    ∃ (firstFlag secondFlag : Bool) (first second : Nat)
      (config bytes updated : List (BitVec 8)) (ffi : HolFfiState F),
      args = [.refPtr firstFlag first, .refPtr secondFlag second] ∧
      sptLookup first state.refs = some (.byteArray true config) ∧
      sptLookup second state.refs = some (.byteArray false bytes) ∧
      callFFIHOL state.ffi (.extCall name) config bytes = .ret ffi updated ∧
      value = DataSem.unitValue ∧
      next = { state with refs := sptInsert second (.byteArray false updated) state.refs,
                          ffi := ffi } := by
  cases args with
  | nil => simp [DataSem.doAppAux] at run
  | cons a rest =>
    cases rest with
    | nil => simp [DataSem.doAppAux] at run
    | cons b rest =>
      cases rest with
      | cons c rest => simp [DataSem.doAppAux] at run
      | nil =>
        cases a <;> cases b <;> simp only [DataSem.doAppAux] at run
        all_goals try contradiction
        all_goals split at run <;> try contradiction
        all_goals split at run <;> try contradiction
        all_goals simp only [SemanticPrimitivesHOL.Result.val.injEq, Prod.mk.injEq] at run
        all_goals obtain ⟨rfl, rfl⟩ := run
        all_goals exact ⟨_, _, _, _, _, _, _, _, rfl, by assumption,
          by assumption, by assumption, rfl, rfl⟩

/-- A successful source FFI application has precisely the byte-array reads and
foreign-call return used in the assignment simulation. The intermediate state
records the original space, limit and stack accounting, including all fields. -/
theorem doApp_ffi_success {C F : Type}
    (name : Basis.Pure.MlString.MlString) (args : List DataSem.Value)
    (state next : DataSem.State C F) (value : DataSem.Value)
    (run : DataSem.doApp (.ffi name) args state = .val (value, next)) :
    ∃ (base : DataSem.State C F) (firstFlag secondFlag : Bool) (first second : Nat)
      (config bytes updated : List (BitVec 8)) (ffi : HolFfiState F),
      DataSem.doSpace (.ffi name) args state = some base ∧
      args = [.refPtr firstFlag first, .refPtr secondFlag second] ∧
      sptLookup first state.refs = some (.byteArray true config) ∧
      sptLookup second state.refs = some (.byteArray false bytes) ∧
      callFFIHOL state.ffi (.extCall name) config bytes = .ret ffi updated ∧
      updated.length = bytes.length ∧
      value = DataSem.unitValue ∧
      next = { DataSem.doStack (.ffi name) args (DataSem.doLimSafe base (.ffi name) args) with
        refs := sptInsert second (.byteArray false updated) state.refs, ffi := ffi } := by
  cases spaceRun : DataSem.doSpace (.ffi name) args state with
  | none => simp [DataSem.doApp, spaceRun] at run
  | some base =>
    have auxRun : DataSem.doAppAux (.ffi name) args
        (DataSem.doStack (.ffi name) args (DataSem.doLimSafe base (.ffi name) args)) =
          .val (value, next) := by
      simpa [DataSem.doApp, spaceRun] using run
    have refs : base.refs = state.refs := by
      simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceRun
      subst base
      rfl
    have ffiEq : base.ffi = state.ffi := by
      simp [DataSem.doSpace, DataLang.opSpaceReset] at spaceRun
      subst base
      rfl
    obtain ⟨flag1, flag2, first, second, config, bytes, updated, ffi,
      argsEq, firstRead, secondRead, call, result, nextEq⟩ :=
      doAppAux_ffi_success name args _ next value auxRun
    simp only [DataSem.doStack, DataSem.doLimSafe] at firstRead secondRead call nextEq
    rw [refs] at firstRead secondRead nextEq
    rw [ffiEq] at call
    have lengthEq := callFFIHOL_ret_length state.ffi (.extCall name) config bytes updated ffi call
    exact ⟨base, flag1, flag2, first, second, config, bytes, updated, ffi,
      rfl, argsEq, firstRead, secondRead, call, lengthEq, result, nextEq⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
