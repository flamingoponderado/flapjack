module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State

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

end Flapjack.Compiler.Backend.DataSem
