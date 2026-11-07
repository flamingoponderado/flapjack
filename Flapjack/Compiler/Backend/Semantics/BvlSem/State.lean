import Flapjack.Compiler.Backend.Semantics.BvlSem.Value
import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Misc.Sptree

/-! State carrier for the BVL evaluator. -/
namespace Flapjack.Compiler.Backend.BvlSem

/-- Original compiler callback over labeled BVL code. -/
abbrev Compiler (C : Type) := C → List (Nat × Nat × Bvl.Exp) →
  Option (List (BitVec 8) × List (BitVec 64) × C)

/-- Sequence of future compiler configurations and BVL programs. -/
abbrev CompileOracle (C : Type) := Nat → C × List (Nat × Nat × Bvl.Exp)

/-- The original BVL state: references use canonical finite support, while
code uses the source's sparse tree carrier. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "state"
  (fmap_as_finite_support := [refs])]
structure State (C F : Type) where
  globals : List (Option Value)
  refs : HolFiniteMapExact Nat (Ref Value)
  clock : Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : Spt (Nat × Bvl.Exp)
  ffi : HolFfiState F

/-- Explicit lookup-and-support view for the BVL reference store. -/
structure StateBroad (C F : Type) where
  globals : List (Option Value)
  refs : Nat → Option (Ref Value)
  refsFiniteSupport : ∃ keys : List Nat, ∀ key, refs key ≠ none → key ∈ keys
  clock : Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : Spt (Nat × Bvl.Exp)
  ffi : HolFfiState F

/-- Expose the finite map as its lookup and support witness. -/
def State.toBroad {C F : Type} (s : State C F) : StateBroad C F :=
  ⟨s.globals, s.refs.lookup, s.refs.finiteSupport, s.clock, s.compile, s.compileOracle, s.code, s.ffi⟩

/-- Rebuild the canonical finite map from the explicit view. -/
def State.ofBroad {C F : Type} (s : StateBroad C F) : State C F :=
  ⟨s.globals, ⟨s.refs, s.refsFiniteSupport⟩, s.clock, s.compile, s.compileOracle, s.code, s.ffi⟩

/-- The BVL state and its explicit finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) := by
  constructor
  · intro s; cases s; rfl
  · intro s; cases s with | mk globals refs clock compile oracle code ffi => cases refs; rfl

/-- Decrement the BVL clock using natural-number subtraction. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [refs])]
def decClock {C F : Type} (n : Nat) (s : State C F) : State C F :=
  { s with clock := s.clock - n }

/-- Initial BVL state with supplied code, callbacks, FFI, and clock. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "initial_state_def"
  (fmap_as_finite_support := [refs])]
def initialState {C F : Type} (ffi : HolFfiState F) (code : Spt (Nat × Bvl.Exp))
    (oracle : CompileOracle C) (compiler : Compiler C) (clock : Nat) : State C F :=
  ⟨[], HolFiniteMapExact.empty, clock, compiler, oracle, code, ffi⟩

/-- Bound the returned state's clock by the incoming clock. The two states
and the result retain the independent type parameters inferred by HOL. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "fix_clock_def"
  (fmap_as_finite_support := [refs])]
def fixClock {C F D G R : Type} (s : State C F) (result : R × State D G) : R × State D G :=
  (result.1, { result.2 with clock := min s.clock result.2.clock })

/-- Flapjack helper: a fixed result cannot increase the incoming clock. -/
theorem fixClock_clock_le {C F D G R : Type} (s : State C F) (result : R × State D G) :
    (fixClock s result).2.clock ≤ s.clock := Nat.min_le_left _ _

end Flapjack.Compiler.Backend.BvlSem
