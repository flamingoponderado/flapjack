module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.DataSem.Stack
public import Flapjack.Compiler.Backend.Semantics.DataSem.Value

@[expose] public section

/-! `dataPropsScript.sml` initial-state and locals facts for the data
evaluator's state. -/

namespace Flapjack.Compiler.Backend.DataSem

/-- Exact HOL `initial_state_simp` (`dataPropsScript.sml:113`): the eight
    projected fields of the initial state, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "initial_state_simp"]
theorem initialState_simp {C F : Type} (f : HolFfiState F) (c : Spt (Nat × DataLang.Prog))
    (co : CompileOracle C) (cc : Compiler C) (ts : Bool) (l : Limits) (ss : Spt Nat) (k : Nat) :
    (initialState f c co cc ts l ss k).clock = k ∧
    (initialState f c co cc ts l ss k).locals = .ln ∧
    (initialState f c co cc ts l ss k).code = c ∧
    (initialState f c co cc ts l ss k).ffi = f ∧
    (initialState f c co cc ts l ss k).compileOracle = co ∧
    (initialState f c co cc ts l ss k).compile = cc ∧
    (initialState f c co cc ts l ss k).stack = [] ∧
    (initialState f c co cc ts l ss k).peakHeapLength = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `initial_state_with_simp` (`dataPropsScript.sml:126`): rewriting
    the clock, stack or locals of the initial state to the value it already
    has yields the initial state. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "initial_state_with_simp"]
theorem initialState_with_simp {C F : Type} (f : HolFfiState F) (c : Spt (Nat × DataLang.Prog))
    (co : CompileOracle C) (cc : Compiler C) (ts : Bool) (l : Limits) (ss : Spt Nat)
    (k k' : Nat) :
    ({ initialState f c co cc ts l ss k with clock := k' } : State C F) =
        initialState f c co cc ts l ss k' ∧
    ({ initialState f c co cc ts l ss k with stack := [] } : State C F) =
        initialState f c co cc ts l ss k ∧
    ({ initialState f c co cc ts l ss k with locals := .ln } : State C F) =
        initialState f c co cc ts l ss k :=
  ⟨rfl, rfl, rfl⟩

/-- Exact HOL `with_same_locals` (`dataPropsScript.sml:181`): rewriting a
    state's locals to their own value is the identity. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "with_same_locals"]
theorem with_same_locals {C F : Type} (s : State C F) :
    ({ s with locals := s.locals } : State C F) = s := by
  rfl

/-- Exact HOL `do_stack_const` (`dataPropsScript.sml:154`): the stack-space
    computation leaves sixteen fields alone, in HOL's order. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_stack_const"]
theorem doStack_const {C F : Type} (op : ClosLang.Op) (vs : List Value) (s : State C F) :
    (doStack op vs s).locals = s.locals ∧
    (doStack op vs s).localsSize = s.localsSize ∧
    (doStack op vs s).stack = s.stack ∧
    (doStack op vs s).stackFrameSizes = s.stackFrameSizes ∧
    (doStack op vs s).global = s.global ∧
    (doStack op vs s).handler = s.handler ∧
    (doStack op vs s).refs = s.refs ∧
    (doStack op vs s).compile = s.compile ∧
    (doStack op vs s).clock = s.clock ∧
    (doStack op vs s).code = s.code ∧
    (doStack op vs s).ffi = s.ffi ∧
    (doStack op vs s).space = s.space ∧
    (doStack op vs s).tstamps = s.tstamps ∧
    (doStack op vs s).limits = s.limits ∧
    (doStack op vs s).peakHeapLength = s.peakHeapLength ∧
    (doStack op vs s).compileOracle = s.compileOracle := by
  simp [doStack]

/-- Exact HOL `Boolv_11` (`dataPropsScript.sml:167`): two Boolean blocks are
    equal exactly when their Booleans are. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "Boolv_11"]
theorem boolValue_inj (b1 b2 : Bool) : boolValue b1 = boolValue b2 ↔ b1 = b2 := by
  cases b1
  all_goals cases b2
  all_goals simp [boolValue, Flapjack.Compiler.Backend.BackendCommon.boolToTag,
    Flapjack.Compiler.Backend.BackendCommon.trueTag,
    Flapjack.Compiler.Backend.BackendCommon.falseTag]

end Flapjack.Compiler.Backend.DataSem
