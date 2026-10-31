import Flapjack.Compiler.Backend.Semantics.BviSem.Apply
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

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

end Flapjack.Compiler.Backend.BviProps
