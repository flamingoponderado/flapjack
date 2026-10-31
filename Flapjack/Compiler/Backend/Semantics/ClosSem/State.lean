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

/-- Explicit lookup-and-support view of the closure code and reference maps. -/
structure StateBroad (C F : Type) where
  globals : List (Option Value)
  refs : Nat → Option (Ref Value)
  refsFiniteSupport : ∃ keys : List Nat, ∀ key, refs key ≠ none → key ∈ keys
  ffi : HolFfiState F
  clock : Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : Nat → Option (Nat × ClosLang.Exp)
  codeFiniteSupport : ∃ keys : List Nat, ∀ key, code key ≠ none → key ∈ keys
  maxApp : Nat

/-- Expose the two finite maps as their lookup functions and support witnesses. -/
def State.toBroad {C F : Type} (s : State C F) : StateBroad C F :=
  ⟨s.globals, s.refs.lookup, s.refs.finiteSupport, s.ffi, s.clock, s.compile,
    s.compileOracle, s.code.lookup, s.code.finiteSupport, s.maxApp⟩

/-- Rebuild the closure state using the canonical finite-map carriers. -/
def State.ofBroad {C F : Type} (s : StateBroad C F) : State C F :=
  ⟨s.globals, ⟨s.refs, s.refsFiniteSupport⟩, s.ffi, s.clock, s.compile,
    s.compileOracle, ⟨s.code, s.codeFiniteSupport⟩, s.maxApp⟩

/-- Both finite-map views roundtrip without additional premises. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) := by
  constructor
  · intro s; cases s; rfl
  · intro s
    cases s with
    | mk globals refs ffi clock compile oracle code maxApp =>
      cases refs
      cases code
      rfl

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
