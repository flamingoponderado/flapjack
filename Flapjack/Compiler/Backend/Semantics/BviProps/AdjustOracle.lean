import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! Adjusting the compiler configuration carried by a BVI oracle. -/
namespace Flapjack.Compiler.Backend.BviProps
open Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Reframe a BVL state with callbacks of another configuration type while
preserving every field observable by non-install primitives. -/
def reframeBvl {C D F : Type} (template : BvlSem.State D F) (state : BvlSem.State C F) : BvlSem.State D F :=
  ⟨state.globals, state.refs, state.clock, template.compile, template.compileOracle, state.code, state.ffi⟩

/-- Transfer a successful optional primitive result to the new BVL frame. -/
def reframeBvlOption {C D F : Type} (template : BvlSem.State D F)
    (result : Option (Value × BvlSem.State C F)) : Option (Value × BvlSem.State D F) :=
  result.map fun (value, state) => (value, reframeBvl template state)

/-- BVL global primitives are independent of compiler callback types. -/
theorem applyGlobal_reframeBvl {C D F : Type} (template : BvlSem.State D F)
    (state : BvlSem.State C F) (op : ClosLang.GlobOp) (args : List Value) :
    BvlSem.applyGlobal op args (reframeBvl template state) =
      reframeBvlOption template (BvlSem.applyGlobal op args state) := by
  unfold BvlSem.applyGlobal reframeBvlOption reframeBvl
  repeat' split
  all_goals simp_all [Function.comp_def]

/-- BVL block primitives are independent of compiler callback types. -/
theorem applyBlock_reframeBvl {C D F : Type} (template : BvlSem.State D F)
    (state : BvlSem.State C F) (op : ClosLang.BlockOp) (args : List Value) :
    BvlSem.applyBlock op args (reframeBvl template state) =
      reframeBvlOption template (BvlSem.applyBlock op args state) := by
  unfold BvlSem.applyBlock reframeBvlOption reframeBvl
  repeat' split
  all_goals simp_all [Option.map_bind]

/-- BVL memory primitives are independent of compiler callback types. -/
theorem applyMemory_reframeBvl {C D F : Type} (template : BvlSem.State D F)
    (state : BvlSem.State C F) (op : ClosLang.MemOp) (args : List Value) :
    BvlSem.applyMemory op args (reframeBvl template state) =
      reframeBvlOption template (BvlSem.applyMemory op args state) := by
  unfold BvlSem.applyMemory reframeBvlOption reframeBvl
  repeat' split
  all_goals simp_all [Option.map_bind]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind]))

/-- BVL numeric primitives are independent of compiler callback types. -/
theorem applyNumeric_reframeBvl {C D F : Type} (template : BvlSem.State D F)
    (state : BvlSem.State C F) (op : ClosLang.Op) (args : List Value) :
    BvlSem.applyNumeric op args (reframeBvl template state) =
      reframeBvlOption template (BvlSem.applyNumeric op args state) := by
  cases op <;> simp [BvlSem.applyNumeric, reframeBvlOption, reframeBvl, Option.map_map, Function.comp_def]

/-- Transfer a BVL primitive result into a frame with different callbacks. -/
def reframeBvlResult {C D F : Type} (template : BvlSem.State D F)
    (result : Flapjack.SemanticPrimitivesHOL.Result (Value × BvlSem.State C F) Value) :
    Flapjack.SemanticPrimitivesHOL.Result (Value × BvlSem.State D F) Value :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, reframeBvl template state)

/-- All non-install BVL primitives commute with reframing their compiler
callbacks. Install is handled separately by the oracle agreement invariant. -/
theorem doApp_reframeBvl {C D F : Type} (template : BvlSem.State D F)
    (state : BvlSem.State C F) (op : ClosLang.Op) (args : List Value)
    (notInstall : op ≠ .install) :
    BvlSem.doApp op args (reframeBvl template state) =
      reframeBvlResult template (BvlSem.doApp op args state) := by
  cases op with
  | globOp operation =>
    simp only [BvlSem.doApp, applyGlobal_reframeBvl]
    cases h : BvlSem.applyGlobal operation args state with
    | none => simp [reframeBvlOption, reframeBvlResult]
    | some pair => cases pair; simp [reframeBvlOption, reframeBvlResult]
  | blockOp operation =>
    simp only [BvlSem.doApp, applyBlock_reframeBvl]
    cases h : BvlSem.applyBlock operation args state with
    | none => simp [reframeBvlOption, reframeBvlResult]
    | some pair => cases pair; simp [reframeBvlOption, reframeBvlResult]
  | memOp operation =>
    simp only [BvlSem.doApp, applyMemory_reframeBvl]
    cases h : BvlSem.applyMemory operation args state with
    | none => simp [reframeBvlOption, reframeBvlResult]
    | some pair => cases pair; simp [reframeBvlOption, reframeBvlResult]
  | intOp operation =>
    simp only [BvlSem.doApp, applyNumeric_reframeBvl]
    cases h : BvlSem.applyNumeric (.intOp operation) args state with
    | none => simp [reframeBvlOption, reframeBvlResult]
    | some pair => cases pair; simp [reframeBvlOption, reframeBvlResult]
  | wordOp operation =>
    simp only [BvlSem.doApp, applyNumeric_reframeBvl]
    cases h : BvlSem.applyNumeric (.wordOp operation) args state with
    | none => simp [reframeBvlOption, reframeBvlResult]
    | some pair => cases pair; simp [reframeBvlOption, reframeBvlResult]
  | install => exact (notInstall rfl).elim
  | label index =>
    simp only [BvlSem.doApp, reframeBvl]
    split <;> simp [reframeBvlResult, reframeBvl]
  | ffi name =>
    simp only [BvlSem.doApp, reframeBvl]
    repeat' split
    all_goals simp_all [reframeBvlResult, reframeBvl]
  | thunkOp operation =>
    simp only [BvlSem.doApp, reframeBvl]
    repeat' split
    all_goals simp_all [reframeBvlResult, reframeBvl]
    all_goals split <;> simp_all

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

/-- The BVL fallback input for an adjusted state is the original BVL input
reframed with the adjusted callback types. -/
theorem toBvl_adjustOracle {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) :
    toBvl (adjustOracle compiler f state) =
      reframeBvl (toBvl (adjustOracle compiler f state)) (toBvl state) := by
  simp [toBvl, reframeBvl, adjustOracle]

/-- Copying BVL fallback fields back commutes with oracle adjustment. -/
theorem fromBvl_reframeBvl {C D F : Type} (compiler : Compiler D) (f : C → D)
    (state : BviState C F) (next : BvlSem.State C F) :
    fromBvl (reframeBvl (toBvl (adjustOracle compiler f state)) next) (adjustOracle compiler f state) =
      adjustOracle compiler f (fromBvl next state) := by
  cases state
  cases next
  rfl

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
      rw [toBvl_adjustOracle, doApp_reframeBvl _ _ _ _ notInstall]
      cases run : BvlSem.doApp op args (toBvl state) with
      | err error => cases error <;> simp [reframeBvlResult, adjustOracleResult]
      | val pair =>
        obtain ⟨value, next⟩ := pair
        simp [reframeBvlResult, adjustOracleResult, fromBvl_reframeBvl]

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
