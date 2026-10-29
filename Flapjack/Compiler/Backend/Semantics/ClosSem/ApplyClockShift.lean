import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyClock
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install

/-! Clock-extension prerequisites for the proof-side closure evaluator.
The dispatcher and finite-map carriers remain pending HOL correspondence review. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.SemanticPrimitivesHOL

/-- Add clock to the state in a successful optional primitive result. -/
def addClockOption {C F : Type} (extra : Nat) (result : Option (Value × State C F)) :
    Option (Value × State C F) :=
  result.map fun (value, state) => (value, { state with clock := state.clock + extra })

/-- Global primitives commute with adding clock. -/
theorem applyGlobal_addClock {C F : Type} (op : ClosLang.GlobOp) (args : List Value)
    (state : State C F) (extra : Nat) :
    applyGlobal op args { state with clock := state.clock + extra } =
      addClockOption extra (applyGlobal op args state) := by
  unfold applyGlobal addClockOption
  repeat' split
  all_goals simp_all [Function.comp_def]

/-- Block primitives commute with adding clock. -/
theorem applyBlock_addClock {C F : Type} (op : ClosLang.BlockOp) (args : List Value)
    (state : State C F) (extra : Nat) :
    applyBlock op args { state with clock := state.clock + extra } =
      addClockOption extra (applyBlock op args state) := by
  unfold applyBlock addClockOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]

/-- Numeric primitives commute with adding clock. -/
theorem applyNumeric_addClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (extra : Nat) :
    applyNumeric op args { state with clock := state.clock + extra } =
      addClockOption extra (applyNumeric op args state) := by
  cases op <;> simp [applyNumeric, addClockOption, Option.map_map, Function.comp_def]


/-- Memory primitives commute with adding clock. -/
theorem applyMemory_addClock {C F : Type} (op : ClosLang.MemOp) (args : List Value)
    (state : State C F) (extra : Nat) :
    applyMemory op args { state with clock := state.clock + extra } =
      addClockOption extra (applyMemory op args state) := by
  unfold applyMemory addClockOption
  repeat' split
  all_goals simp_all [Option.map_bind, Function.comp_def]
  all_goals try omega
  all_goals try (repeat' (congr 1; funext value; cases value <;> simp [Option.map_bind, Function.comp_def]))


/-- Add clock to the state in a successful primitive result. -/
def addClockResult {C F : Type} (extra : Nat) (result : Result (Value × State C F) Value) :
    Result (Value × State C F) Value :=
  match result with
  | .err error => .err error
  | .val (value, state) => .val (value, { state with clock := state.clock + extra })

/-- Every ordinary primitive application commutes with adding clock. -/
theorem doApp_addClock {C F : Type} (op : ClosLang.Op) (args : List Value)
    (state : State C F) (extra : Nat) :
    doApp op args { state with clock := state.clock + extra } =
      addClockResult extra (doApp op args state) := by
  cases op with
  | globOp operation =>
    cases found : applyGlobal operation args state with
    | none => simp [doApp, applyGlobal_addClock, found, addClockOption, addClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyGlobal_addClock, found, addClockOption, addClockResult]
  | blockOp operation =>
    cases found : applyBlock operation args state with
    | none => simp [doApp, applyBlock_addClock, found, addClockOption, addClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyBlock_addClock, found, addClockOption, addClockResult]
  | memOp operation =>
    cases found : applyMemory operation args state with
    | none => simp [doApp, applyMemory_addClock, found, addClockOption, addClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyMemory_addClock, found, addClockOption, addClockResult]
  | intOp operation =>
    cases found : applyNumeric (.intOp operation) args state with
    | none => simp [doApp, applyNumeric_addClock, found, addClockOption, addClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyNumeric_addClock, found, addClockOption, addClockResult]
  | wordOp operation =>
    cases found : applyNumeric (.wordOp operation) args state with
    | none => simp [doApp, applyNumeric_addClock, found, addClockOption, addClockResult]
    | some pair =>
      obtain ⟨value, next⟩ := pair
      simp [doApp, applyNumeric_addClock, found, addClockOption, addClockResult]
  | label | install => rfl
  | ffi | thunkOp =>
    simp only [doApp, addClockResult]
    repeat' split
    all_goals simp_all
    all_goals aesop



/-- Successful installation commutes with adding clock, including its
updates to code and the compilation oracle. -/
theorem doInstall_success_addClock {C F : Type} (values : List Value) (state next : State C F)
    (expressions : List ClosLang.Exp) (extra : Nat)
    (run : doInstall values state = (.val expressions, next)) :
    doInstall values { state with clock := state.clock + extra } =
      (.val expressions, { next with clock := next.clock + extra }) := by
  classical
  unfold doInstall at run
  repeat' first | split at run | simp_all
  all_goals simp_all [doInstall]
  all_goals try split
  all_goals simp_all
  all_goals try (rcases run with ⟨_, rfl⟩; simp; omega)

end Flapjack.Compiler.Backend.ClosSem
