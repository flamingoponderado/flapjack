module

public import Flapjack.Compiler.Backend.Semantics.DataProps.StackResult

@[expose] public section

/-! Primitive cases of the result-sensitive evaluator control invariant. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Installation never returns a raised exception. This auxiliary fact has
no direct HOL declaration. -/
theorem doInstall_ne_raise {C F R : Type} (args : List Value) (state : State C F) (value : R) :
    doInstall args state ≠ .err (.raise value) := by
  simp only [doInstall]
  repeat' (split <;> try simp_all)

/-- The primitive dispatcher reports aborts but does not raise a language
exception. This auxiliary fact has no direct HOL declaration. -/
theorem doAppAux_ne_raise {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) : doAppAux op args state ≠ .err (.raise value) := by
  simp only [doAppAux]
  repeat' (split <;> try simp_all)

/-- Primitive application never returns a raised language exception. -/
theorem doApp_ne_raise {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (value : Value) : doApp op args state ≠ .err (.raise value) := by
  cases op with
  | install => exact doInstall_ne_raise args _ value
  | intOp op =>
    cases op <;> simp only [doApp] <;> (try split) <;> simp_all [doAppAux_ne_raise]
  | label label => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | ffi name => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | wordOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | blockOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | globOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | memOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]
  | thunkOp op => simp only [doApp]; split <;> simp_all [doAppAux_ne_raise]

/-- Assignment satisfies the result-sensitive control invariant, including
primitive errors and code installation. -/
theorem evaluate_assign_stackResult {C F : Type} (dest : Nat) (op : ClosLang.Op) (names : List Nat)
    (live : Option NumSet) (state next : State C F) (result : Option (Result (List Value) Value))
    (run : evaluate (.assign dest op names live) state = (result, next)) : stackResult state result next := by
  by_cases invalid : (DataLang.opRequiresNames op == live.isNone) = true
  · simp [evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  · cases read : getVars names state.locals with
    | none =>
      simp [evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      trivial
    | some args =>
      cases cut : cutStateOpt live state with
      | none =>
        simp [evaluate, invalid, read, cut] at run
        obtain ⟨rfl, rfl⟩ := run
        trivial
      | some prepared =>
        cases app : doApp op args prepared with
        | err error =>
          cases error with
          | abort reason =>
            simp [evaluate, invalid, read, cut, app] at run
            obtain ⟨rfl, rfl⟩ := run
            trivial
          | raise value => exact False.elim (doApp_ne_raise op args prepared value app)
        | val pair =>
          obtain ⟨value, applied⟩ := pair
          have frame := doApp_controlFrame op args prepared applied value app
          have control : applied.stack = prepared.stack ∧ applied.handler = prepared.handler :=
            ⟨frame.2.1, frame.2.2.1⟩
          have cutControl := cutStateOpt_control live state prepared cut
          simp [evaluate, invalid, read, cut, app] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨control.1.trans cutControl.1, control.2.trans cutControl.2.1⟩

/-- Skip, move, tick and space reservation have no value-return or raise
outcome; their continuing outcomes preserve control. -/
theorem evaluate_skip_stackResult {C F : Type} (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate .skip state = (result, next)) : stackResult state result next := by
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨rfl, rfl⟩

theorem evaluate_move_stackResult {C F : Type} (dest src : Nat) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.move dest src) state = (result, next)) : stackResult state result next := by
  cases read : getVar src state.locals with
  | none =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some value =>
    simp [evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl⟩

theorem evaluate_tick_stackResult {C F : Type} (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate .tick state = (result, next)) : stackResult state result next := by
  by_cases zero : state.clock = 0
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  · simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨rfl, rfl⟩

theorem evaluate_makeSpace_stackResult {C F : Type} (amount : Nat) (names : NumSet) (state next : State C F)
    (result : Option (Result (List Value) Value))
    (run : evaluate (.makeSpace amount names) state = (result, next)) : stackResult state result next := by
  cases cut : cutEnv names state.locals with
  | none =>
    simp [evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    trivial
  | some env =>
    have control := evaluate_makeSpace_control amount names state (addSpace { state with locals := env } amount)
      (by simp [evaluate, cut])
    simp [evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨control.1, control.2.1⟩

end Flapjack.Compiler.Backend.DataSem
