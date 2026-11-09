module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Misc.Sptree.FromList
public import Flapjack.Misc.Sptree.MkWf
public import Flapjack.Misc.ListEl
public import Mathlib.Data.Option.NAry

@[expose] public section

/-! Stack, call and thunk operations used by the data-language evaluator. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.Compiler.Backend.BackendCommon

instance controlInst1 : Nonempty Value := ⟨.number 0⟩

/-- The accounted size of an environment or exception frame. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "size_of_stack_frame_def"]
def sizeOfStackFrame : Stack → Option Nat
  | .env size _ => size
  | .exc size _ _ => size.map (3 + ·)

/-- An unbounded frame makes the total stack size unbounded. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "size_of_stack_def"]
def sizeOfStack (stack : List Stack) : Option Nat :=
  stack.foldr (fun frame size => Option.map₂ (· + ·) (sizeOfStackFrame frame) size) (some 1)

/-- Clear locals and optionally the stack, retaining all other fields. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "flush_state_def"]
def flushState {C F : Type} (all : Bool) (state : State C F) : State C F :=
  if all then { state with locals := .ln, stack := [], localsSize := some 0 }
  else { state with locals := .ln, localsSize := some 0 }

/-- Enter a call with argument locals and update the maximum stack size. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "call_env_def"]
def callEnv {C F : Type} (args : List Value) (size : Option Nat) (state : State C F) : State C F :=
  let stackMax := Option.map₂ max state.stackMax (Option.map₂ (· + ·) (sizeOfStack state.stack) size)
  let stackSafe := (stackMax.map (fun n => decide (state.limits.stackLimit > n))).getD false
  { state with locals := sptFromList args, localsSize := size, stackMax := stackMax,
               safeForSpace := state.safeForSpace && stackSafe }

/-- Save locals, optionally installing an exception handler. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "push_env_def"]
def pushEnv {C F : Type} (env : Spt Value) (handler : Bool) (state : State C F) : State C F :=
  let frame := if handler then Stack.exc state.localsSize env state.handler else Stack.env state.localsSize env
  let stack := frame :: state.stack
  let stackMax := Option.map₂ max state.stackMax (sizeOfStack stack)
  let stackSafe := (stackMax.map (fun n => decide (state.limits.stackLimit > n))).getD false
  { state with stack := stack, stackMax := stackMax,
               handler := if handler then state.stack.length else state.handler,
               safeForSpace := state.safeForSpace && stackSafe }

/-- Restore the next saved environment and its handler when present. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "pop_env_def"]
def popEnv {C F : Type} (state : State C F) : Option (State C F) :=
  match state.stack with
  | .env size env :: rest => some { state with locals := env, stack := rest, localsSize := size }
  | .exc size env handler :: rest =>
      some { state with locals := env, stack := rest, localsSize := size, handler := handler }
  | [] => none

/-- Drop frames up to the saved exception frame. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "jump_exc_def"]
def jumpExc {C F : Type} (state : State C F) : Option (State C F) :=
  if state.handler < state.stack.length then
    match state.stack.drop (state.stack.length - (state.handler + 1)) with
    | .exc size env handler :: rest =>
        some { state with handler := handler, locals := env, stack := rest, localsSize := size }
    | _ => none
  else none

/-- Retain the requested local names only when each one exists. The result
is normalized just as in the original sparse-tree semantics. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "cut_env_def"]
noncomputable def cutEnv {α : Type} (names : NumSet) (env : Spt α) : Option (Spt α) := by
  classical
  exact if ∀ key, sptMem key names → sptMem key env then some (sptMkWf (sptInter env names)) else none

/-- Cut the local environment while preserving the rest of the state. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "cut_state_def"]
noncomputable def cutState {C F : Type} (names : NumSet) (state : State C F) : Option (State C F) :=
  (cutEnv names state.locals).map fun env => { state with locals := env }

/-- Leave the state unchanged when there is no live-name restriction. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "cut_state_opt_def"]
noncomputable def cutStateOpt {C F : Type} (names : Option NumSet) (state : State C F) : Option (State C F) :=
  match names with
  | none => some state
  | some names => cutState names state

/-- Update locals by a left-biased union with the zipped bindings. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "set_vars_def"]
def setVars {C F : Type} (names : List Nat) (values : List Value) (state : State C F) : State C F :=
  { state with locals := sptUnion (sptFromAList (names.zip values)) state.locals }

/-- Clear space-safety when an installation primitive runs. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "install_sfs_def"]
def installSfs {C F : Type} (op : ClosLang.Op) (state : State C F) : State C F :=
  { state with safeForSpace := match op with | .install => false | _ => state.safeForSpace }

/-- Resolve direct or indirect calls and return their optional frame size. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "find_code_def"]
noncomputable def findCode {α β : Type} (dest : Option Nat) (args : List Value)
    (code : Spt (Nat × α)) (frameSizes : Spt β) : Option (List Value × α × Option β) :=
  match dest with
  | some label =>
      match sptLookup label code with
      | none => none
      | some (arity, body) => if args.length = arity then some (args, body, sptLookup label frameSizes) else none
  | none =>
      if args.isEmpty then none else
        match holLast args with
        | .codePtr label =>
            match sptLookup label code with
            | none => none
            | some (arity, body) =>
                if args.length = arity + 1 then some (args.dropLast, body, sptLookup label frameSizes) else none
        | _ => none

/-- Test for a Boolean block independently of its timestamp. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "isBool_def"]
def isBool (expected : Bool) : Value → Bool
  | .block _ tag [] => decide (boolToTag expected = tag)
  | _ => false

/-- Decode the two Boolean block tags. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "dest_Boolv_def"]
def destBool : Value → Option Bool
  | .block _ tag values => if values = [] ∧ tag < 2 then some (decide (tag = 1)) else none
  | _ => none

/-- Results of examining a reference as a thunk. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : AstHOL.ThunkMode → Value → DestThunkResult

/-- Inspect the source reference tree, respecting the reference-pointer bit. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "dest_thunk_def"]
def destThunk (value : Value) (refs : Spt (BvlSem.Ref Value)) : DestThunkResult :=
  match value with
  | .refPtr bit address =>
      match sptLookup address refs with
      | none => .badRef
      | some (.thunk mode body) => if bit then .badRef else .isThunk mode body
      | some _ => .notThunk
  | _ => .notThunk

/-- The data evaluator excludes installation and mutable-cons allocation
from the operations admitted by this check. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "allowed_op_def"]
def allowedOp {α : Type} (op : ClosLang.Op) (_unused : α) : Prop :=
  op ≠ .install ∧ ∀ tag index, op ≠ .memOp (.mutCons tag index)

/-- An evaluated thunk cannot be updated with a value that itself denotes a thunk. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "bad_thunk_update_def"]
def badThunkUpdate (mode : AstHOL.ThunkMode) (value : Value) (refs : Spt (BvlSem.Ref Value)) : Prop :=
  mode = .evaluated ∧ destThunk value refs ≠ .notThunk

/-- The clock is unchanged when an environment frame is pushed. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "push_env_clock"]
theorem pushEnv_clock {C F : Type} (env : Spt Value) (handler : Bool) (state : State C F) :
    (pushEnv env handler state).clock = state.clock := by
  simp [pushEnv]

/-- A successful pop preserves the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "pop_env_clock"]
theorem popEnv_clock {C F : Type} (state next : State C F) (run : popEnv state = some next) :
    next.clock = state.clock := by
  cases stack : state.stack with
  | nil => simp [popEnv, stack] at run
  | cons frame rest =>
    cases frame <;> simp [popEnv, stack] at run <;> subst next <;> rfl

end Flapjack.Compiler.Backend.DataSem
