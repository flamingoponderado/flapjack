import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-! Closure evaluator state with finite-support code and reference maps. -/
namespace Flapjack.Compiler.Backend.ClosSem

/-- Program payload accepted by the closure compiler callback. The first
component is the main expression sequence; the second contains code entries. -/
abbrev Program := List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)

/-- Callback matching the closure compiler's source-level interface. -/
abbrev Compiler (C : Type) := C → Program → Option (List (BitVec 8) × List (BitVec 64) × C)

/-- Sequence of future compiler configurations and closure programs. -/
abbrev CompileOracle (C : Type) := Nat → C × Program

/-- Proof-side closure state. The two HOL finite maps use the canonical
finite-support carrier; this declaration remains untagged until the required
representation witness and full source correspondence review are complete. -/
structure State (C F : Type) where
  globals : List (Option Value)
  refs : HolFiniteMapExact Nat (Ref Value)
  ffi : HolFfiState F
  clock : Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)
  maxApp : Nat

/-- Subtract from the closure clock using natural-number subtraction. This
proof-side operation awaits the finite-map representation review. -/
def decClock {C F : Type} (n : Nat) (state : State C F) : State C F :=
  { state with clock := state.clock - n }

/-- The original closure evaluator starts with empty globals and reference
store, while code and compilation callbacks are supplied by the caller.
This proof-side operation awaits the finite-map representation review. -/
def initialState {C F : Type} (ffi : HolFfiState F) (maxApp : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C) (clock : Nat) : State C F :=
  ⟨[], HolFiniteMapExact.empty, ffi, clock, compiler, oracle, code, maxApp⟩

end Flapjack.Compiler.Backend.ClosSem
