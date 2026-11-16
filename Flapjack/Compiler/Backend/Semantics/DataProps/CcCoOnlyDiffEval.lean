module

public import Flapjack.Compiler.Backend.Semantics.DataProps.CcCoOnlyDiffApp
public import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

@[expose] public section

/-!
# Evaluation under a compiler-configuration change

Every state operation of the data evaluator except primitive application reads
only the fields compared by `ccCoOnlyDiff`, so each of them commutes with the
compiler rebuild. With those facts, evaluation at a rebuilt state mirrors
evaluation at the original state, and the two final states still agree.

These declarations are Flapjack-only infrastructure: they are the field-level
steps for the port of HOL `evaluate_cc_co_only_diff`
(`dataPropsScript.sml:3114`), which is not ported yet, so they carry no `@[hol]`
tag of their own.
-/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- Replacing the locals commutes with the rebuild. -/
theorem castCompiler_locals {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) :
    { castCompiler s t with locals := env } = castCompiler { s with locals := env } t := rfl

/-- Reading a local variable reads only the environment. -/
theorem getVar_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) (name : Nat) :
    getVar name (castCompiler s t).locals = getVar name s.locals := rfl

/-- Reading several local variables reads only the environment. -/
theorem getVars_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : List Nat) :
    getVars names (castCompiler s t).locals = getVars names s.locals := rfl

/-- Writing a local variable commutes with the rebuild. -/
theorem setVar_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (name : Nat) (value : DataSem.Value) :
    setVar name value (castCompiler s t) = castCompiler (setVar name value s) t := rfl

/-- Writing several local variables commutes with the rebuild. -/
theorem setVars_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : List Nat) (values : List DataSem.Value) :
    setVars names values (castCompiler s t) = castCompiler (setVars names values s) t := rfl

/-- Clock decrement commutes with the rebuild. -/
theorem decClock_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    decClock (castCompiler s t) = castCompiler (decClock s) t := rfl

/-- Clock clamping commutes with the rebuild. -/
theorem fixClock_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (outcome : Option (Result (List DataSem.Value) DataSem.Value)) (mid : State C1 F) :
    fixClock (castCompiler s t) (outcome, castCompiler mid t) =
      (outcome, castCompiler (fixClock s (outcome, mid)).2 t) := rfl

/-- Clock clamping preserves agreement of the resulting states. -/
theorem fixClock_agree {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (outcome : Option (Result (List DataSem.Value) DataSem.Value)) (mid : State C1 F)
    (other : State C2 F) (agree : ccCoOnlyDiff mid other) :
    ccCoOnlyDiff (fixClock s (outcome, mid)).2
      (fixClock (castCompiler s t) (outcome, other)).2 := by
  simp only [fixClock, ccCoOnlyDiff] at agree ⊢
  simp_all

/-- Flushing the locals commutes with the rebuild. -/
theorem flushState_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (all : Bool) :
    flushState all (castCompiler s t) = castCompiler (flushState all s) t := by
  cases all <;> rfl

/-- The installation safety update commutes with the rebuild. -/
theorem installSfs_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (op : ClosLang.Op) :
    installSfs op (castCompiler s t) = castCompiler (installSfs op s) t := rfl

/-- Space allocation commutes with the rebuild. -/
theorem addSpace_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (amount : Nat) :
    addSpace (castCompiler s t) amount = castCompiler (addSpace s amount) t := rfl

/-- Cutting the local environment reads only the environment. -/
theorem cutEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : NumSet) :
    cutEnv names (castCompiler s t).locals = cutEnv names s.locals := rfl

/-- Cutting the local environment of the state commutes with the rebuild. -/
theorem cutState_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : NumSet) :
    cutState names (castCompiler s t) =
      (cutState names s).map (fun next => castCompiler next t) := by
  simp only [cutState]
  cases h : cutEnv names s.locals with
  | none => rfl
  | some env => rfl

/-- The optional environment cut commutes with the rebuild. -/
theorem cutStateOpt_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (names : Option NumSet) :
    cutStateOpt names (castCompiler s t) =
      (cutStateOpt names s).map (fun next => castCompiler next t) := by
  cases names with
  | none => rfl
  | some names => exact cutState_castCompiler s t names

/-- Exception unwinding commutes with the rebuild. -/
theorem jumpExc_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    jumpExc (castCompiler s t) =
      (jumpExc s).map (fun next => castCompiler next t) := by
  simp only [jumpExc]
  by_cases inside : s.handler < s.stack.length
  · simp only [inside, if_true]
    cases h : s.stack.drop (s.stack.length - (s.handler + 1)) with
    | nil => rfl
    | cons frame rest =>
      cases frame with
      | env size env => rfl
      | exc size env handler => rfl
  · simp [inside]

/-- Popping a frame commutes with the rebuild. -/
theorem popEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F) :
    popEnv (castCompiler s t) = (popEnv s).map (fun next => castCompiler next t) := by
  simp only [popEnv]
  cases h : s.stack with
  | nil => rfl
  | cons frame rest =>
    cases frame with
    | env size env => rfl
    | exc size env handler => rfl

/-- Entering a call commutes with the rebuild. -/
theorem callEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (args : List DataSem.Value) (size : Option Nat) :
    callEnv args size (castCompiler s t) = castCompiler (callEnv args size s) t := rfl

/-- Pushing an environment commutes with the rebuild. -/
theorem pushEnv_castCompiler {C1 C2 F : Type} (s : State C1 F) (t : State C2 F)
    (env : Spt DataSem.Value) (handler : Bool) :
    pushEnv env handler (castCompiler s t) = castCompiler (pushEnv env handler s) t := rfl


end Flapjack.Compiler.Backend.DataProps
