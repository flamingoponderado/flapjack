module

public import Flapjack.Compiler.Backend.Semantics.BviSem.ApplyRuntimeFrame
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section

/-! Adjusting the compiler configuration carried by a BVI oracle. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Replace the compiler and map the configuration of every oracle entry,
leaving the runtime state unchanged. Untagged pending review of the BVI
state and evaluator carriers against HOL. -/
def adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) : BviState D F :=
  ⟨state.refs, state.clock, state.global, compiler,
    fun n => (f (state.compileOracle n).1, (state.compileOracle n).2), state.code, state.ffi⟩

/-- The original and adjusted callbacks agree at every oracle entry. -/
def adjustOracleOk {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) : Prop :=
  ∀ n, (state.compile (state.compileOracle n).1 (state.compileOracle n).2).map
      (fun (bytes, data, config) => (bytes, data, f config)) =
    compiler (f (state.compileOracle n).1) (state.compileOracle n).2

/-- Clock changes commute with adjusting the oracle and preserve callback
agreement. This helper is not a HOL declaration port. -/
theorem adjustOracle_clock {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (clock : Nat) :
    adjustOracle compiler f { state with clock := clock } =
        { adjustOracle compiler f state with clock := clock } ∧
      (adjustOracleOk compiler f { state with clock := clock } ↔ adjustOracleOk compiler f state) := by
  constructor <;> rfl

/-- Oracle adjustment commutes with clock decrements. -/
theorem adjustOracle_decClock {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (amount : Nat) :
    adjustOracle compiler f (decClock amount state) = decClock amount (adjustOracle compiler f state) ∧
      (adjustOracleOk compiler f (decClock amount state) ↔ adjustOracleOk compiler f state) := by
  constructor <;> rfl

/-- Clock clamping commutes with oracle adjustment and preserves callback
agreement in the returned state. -/
theorem adjustOracle_fixClock {C D F R : Type} (compiler : Compiler D) (f : C → D)
    (state next : BviState C F) (result : R) :
    fixClock (adjustOracle compiler f state) (result, adjustOracle compiler f next) =
        (result, adjustOracle compiler f (fixClock state (result, next)).2) ∧
      (adjustOracleOk compiler f (fixClock state (result, next)).2 ↔ adjustOracleOk compiler f next) := by
  constructor <;> rfl

/-- The disabled pass's initial state adjusts to the downstream initial
state; the first configuration component is threaded by the callback. -/
theorem adjustOracle_identity_initial {C D F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (compiler : Compiler D) (clock : Nat) :
    adjustOracle compiler Prod.snd
        (initialState ffi code oracle (BackendProps.stateCc (fun c p => (c, p)) compiler) clock) =
      initialState ffi code (BackendProps.stateCo (fun c p => (c, p)) oracle) compiler clock := by
  rfl

/-- The identity-pass callback agrees with its adjusted version at every
initial oracle entry. -/
theorem adjustOracleOk_identity_initial {C D F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × Bvi.Exp)) (oracle : CompileOracle (C × D))
    (compiler : Compiler D) (clock : Nat) :
    adjustOracleOk compiler Prod.snd
      (initialState ffi code oracle (BackendProps.stateCc (fun c p => (c, p)) compiler) clock) := by
  intro n
  cases h : oracle n with
  | mk config program =>
    rcases config with ⟨passConfig, targetConfig⟩
    cases hcompiler : compiler targetConfig program with
    | none => simp [initialState, BackendProps.stateCc, h, hcompiler]
    | some output =>
      rcases output with ⟨bytes, data, config⟩
      simp [initialState, BackendProps.stateCc, h, hcompiler]

/-- Successful installation preserves callback agreement while shifting the
oracle, and produces the adjusted target state. -/
theorem doInstall_adjustOracle {C D F R : Type} (compiler : Compiler D) (f : C → D)
    (args : List Value) (state next : BviState C F) (value : Value)
    (ok : adjustOracleOk compiler f state)
    (run : doInstall (R := R) args state = .val (value, next)) :
    doInstall (R := R) args (adjustOracle compiler f state) =
        .val (value, adjustOracle compiler f next) ∧ adjustOracleOk compiler f next := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals repeat' split at run
  all_goals simp_all
  all_goals have okZero := ok 0
  all_goals simp_all [adjustOracleOk, adjustOracle, doInstall]
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals simp_all
  all_goals grind

/-- Installation can fail only with the source type error. -/
theorem doInstall_error_is_typeError {C F R : Type} (args : List Value)
    (state : BviState C F) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult R)
    (run : doInstall args state = .err error) : error = .abort .typeError := by
  unfold doInstall at run
  repeat' split at run
  all_goals simp_all
  all_goals repeat' split at run
  all_goals simp_all

/-- Adjust a successful result of the BVI-specific primitive dispatcher. -/
def adjustOracleAux {C D F : Type} (compiler : Compiler D) (f : C → D)
    (result : Option (Option (Value × BviState C F))) : Option (Option (Value × BviState D F)) :=
  result.map fun inner => inner.map fun (value, state) => (value, adjustOracle compiler f state)

/-- BVI-specific primitives commute with oracle adjustment. The nested
option preserves both type errors and delegation to BVL. -/
theorem doAppAux_adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (op : ClosLang.Op) (args : List Value) (state : BviState C F) :
    doAppAux op args (adjustOracle compiler f state) =
      adjustOracleAux compiler f (doAppAux op args state) := by
  unfold doAppAux adjustOracleAux adjustOracle
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try (cases hg : state.global <;> simp_all)
  all_goals try (rename_i ptr; cases hr : state.refs.lookup ptr <;> simp_all)
  all_goals try (rename_i value; cases value <;> simp_all)
  all_goals try (split <;> simp_all)
  all_goals try grind

/-- A handled BVI primitive leaves the callback and future oracle unchanged. -/
theorem doAppAux_preserves_compiler_oracle {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doAppAux op args state = some (some (value, next))) :
    next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold doAppAux at run
  repeat' split at run
  all_goals simp_all
  all_goals try simp_all only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  all_goals aesop

/-- A successfully handled primitive produces the adjusted state and keeps
the oracle-callback agreement needed by later installation. -/
theorem doAppAux_adjustOracle_success {C D F : Type} (compiler : Compiler D) (f : C → D)
    (op : ClosLang.Op) (args : List Value) (state next : BviState C F) (value : Value)
    (ok : adjustOracleOk compiler f state)
    (run : doAppAux op args state = some (some (value, next))) :
    doAppAux op args (adjustOracle compiler f state) =
        some (some (value, adjustOracle compiler f next)) ∧ adjustOracleOk compiler f next := by
  have fields := doAppAux_preserves_compiler_oracle op args state next value run
  constructor
  · rw [doAppAux_adjustOracle, run]
    rfl
  · simpa [adjustOracleOk, fields.1, fields.2] using ok

/-- The adjusted fallback input keeps its own arbitrary BVL fields while
copying the original runtime fields. -/
theorem toBvl_adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) :
    toBvl (adjustOracle compiler f state) =
      BvlProps.fallbackFrame (toBvl state) (toBvl (adjustOracle compiler f state)) := by
  simp [toBvl, BvlProps.fallbackFrame, adjustOracle]

/-- Transfer a BVI primitive result into an adjusted oracle frame. -/
def adjustOracleResult {C D F : Type} (compiler : Compiler D) (f : C → D)
    (result : Flapjack.SemanticPrimitivesHOL.Result (Value × BviState C F) ExnOrRet) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BviState D F) ExnOrRet :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, adjustOracle compiler f state)

/-- The BVI fallback dispatcher commutes with oracle adjustment for non-install
operations, including errors and external-call outcomes. -/
theorem doAppFallback_adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (op : ClosLang.Op) (args : List Value) (state : BviState C F) (notInstall : op ≠ .install) :
    doAppFallback op args (adjustOracle compiler f state) =
      adjustOracleResult compiler f (doAppFallback op args state) := by
  unfold doAppFallback
  rw [doAppAux_adjustOracle]
  cases aux : doAppAux op args state with
  | none => simp [adjustOracleAux, adjustOracleResult]
  | some inner =>
    cases inner with
    | some pair => cases pair; simp [adjustOracleAux, adjustOracleResult]
    | none =>
      simp only [adjustOracleAux, Option.map]
      have notGlobal : ∀ operation, op ≠ .globOp operation := by
        intro operation eq
        subst op
        exact doAppAux_delegates_not_global operation args state aux
      have domain : sptDomain (toBvl state).code =
          sptDomain (toBvl (adjustOracle compiler f state)).code := by
        simp [toBvl_domain, adjustOracle]
      rw [toBvl_adjustOracle]
      cases run : BvlSem.doApp op args (toBvl state) with
      | err error =>
        have swapped := BvlProps.doAppFallbackRerrSwap op args (toBvl state) error
          (toBvl (adjustOracle compiler f state)) notGlobal
          ⟨run, notInstall, Or.inl (by intro key present; rwa [domain])⟩
        rw [swapped]
        cases error <;> simp [adjustOracleResult]
      | val pair =>
        obtain ⟨value, next⟩ := pair
        have swapped := BvlProps.doAppFallbackRvalSwap op args (toBvl state) next value
          (toBvl (adjustOracle compiler f state)) notGlobal
          ⟨run, notInstall, by intro key present; rwa [← domain]⟩
        rw [swapped]
        simp [adjustOracleResult, BvlProps.fallbackFrame, fromBvl, adjustOracle]

/-- Successful fallback operations leave the compiler and oracle fields
unchanged, including operations delegated to BVL. -/
theorem doAppFallback_preserves_compiler_oracle {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state next : BviState C F) (value : Value)
    (run : doAppFallback op args state = .val (value, next)) :
    next.compile = state.compile ∧ next.compileOracle = state.compileOracle := by
  unfold doAppFallback at run
  cases aux : doAppAux op args state with
  | none => simp [aux] at run
  | some inner =>
    cases inner with
    | some pair =>
      obtain ⟨result, last⟩ := pair
      have fields := doAppAux_preserves_compiler_oracle op args state last result aux
      simp [aux] at run
      obtain ⟨rfl, rfl⟩ := run
      exact fields
    | none =>
      simp only [aux] at run
      cases app : BvlSem.doApp op args (toBvl state) with
      | err error => cases error <;> simp [app] at run
      | val pair =>
        obtain ⟨result, last⟩ := pair
        simp [app] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨rfl, rfl⟩

/-- Every successful BVI primitive commutes with oracle adjustment and
preserves callback agreement, including dynamic installation. -/
theorem doApp_adjustOracle_success {C D F : Type} (compiler : Compiler D) (f : C → D)
    (op : ClosLang.Op) (args : List Value) (state next : BviState C F) (value : Value)
    (ok : adjustOracleOk compiler f state) (run : doApp op args state = .val (value, next)) :
    doApp op args (adjustOracle compiler f state) = .val (value, adjustOracle compiler f next) ∧
      adjustOracleOk compiler f next := by
  by_cases isInstall : op = .install
  · subst op
    exact doInstall_adjustOracle compiler f args state next value ok run
  · have fallbackRun : doAppFallback op args state = .val (value, next) := by
      cases op <;> simp_all [doApp]
    have fields := doAppFallback_preserves_compiler_oracle op args state next value fallbackRun
    constructor
    · have adjusted := doAppFallback_adjustOracle compiler f op args state isInstall
      cases op <;> simp_all [doApp, adjustOracleResult]
    · simpa [adjustOracleOk, fields.1, fields.2] using ok

/-- Any non-type-error BVI primitive error is unchanged by oracle adjustment.
Installation is excluded because all of its errors are type errors. -/
theorem doApp_adjustOracle_error {C D F : Type} (compiler : Compiler D) (f : C → D)
    (op : ClosLang.Op) (args : List Value) (state : BviState C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ExnOrRet)
    (notType : error ≠ .abort .typeError) (run : doApp op args state = .err error) :
    doApp op args (adjustOracle compiler f state) = .err error := by
  by_cases isInstall : op = .install
  · subst op
    exact (notType (doInstall_error_is_typeError args state error run)).elim
  · have fallbackRun : doAppFallback op args state = .err error := by
      cases op <;> simp_all [doApp]
    have adjusted := doAppFallback_adjustOracle compiler f op args state isInstall
    cases op <;> simp_all [doApp, adjustOracleResult]

end Flapjack.Compiler.Backend.BviProps
