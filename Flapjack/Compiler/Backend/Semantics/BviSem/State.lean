import Flapjack.Compiler.Backend.Semantics.BvlSem.State
import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.SemanticPrimitivesHOL

/-! Runtime result and state carriers for the BVI semantics. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem

/-- The source exception payload distinguishes a raised value from returns. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "exn_or_ret"]
inductive ExnOrRet where
  | exn : Value → ExnOrRet
  | ret : List Value → ExnOrRet

/-- The source BVI evaluator result carrier. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "bvi_result"]
abbrev BviResult := Flapjack.SemanticPrimitivesHOL.Result (List Value) ExnOrRet

/-- Compiler callback over labeled BVI programs. -/
abbrev Compiler (C : Type) := C → List (Nat × Nat × Bvi.Exp) →
  Option (List (BitVec 8) × List (BitVec 64) × C)

/-- Future compiler configurations and labeled BVI programs. -/
abbrev CompileOracle (C : Type) := Nat → C × List (Nat × Nat × Bvi.Exp)

/-- BVI state with the source sparse-tree code and canonical reference map. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "state"
  (fmap_as_finite_support := [refs])]
structure BviState (C F : Type) where
  refs : HolFiniteMapExact Nat (Ref Value)
  clock : Nat
  global : Option Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : Spt (Nat × Bvi.Exp)
  ffi : HolFfiState F

/-- Explicit lookup-and-support view of a BVI state. -/
structure BviStateBroad (C F : Type) where
  refs : Nat → Option (Ref Value)
  refsFiniteSupport : ∃ keys : List Nat, ∀ key, refs key ≠ none → key ∈ keys
  clock : Nat
  global : Option Nat
  compile : Compiler C
  compileOracle : CompileOracle C
  code : Spt (Nat × Bvi.Exp)
  ffi : HolFfiState F

/-- Expose the canonical reference map as lookup and finite support. -/
def BviState.toBroad {C F : Type} (s : BviState C F) : BviStateBroad C F :=
  ⟨s.refs.lookup, s.refs.finiteSupport, s.clock, s.global, s.compile, s.compileOracle, s.code, s.ffi⟩

/-- Reconstruct a canonical BVI state from its explicit map view. -/
def BviState.ofBroad {C F : Type} (s : BviStateBroad C F) : BviState C F :=
  ⟨⟨s.refs, s.refsFiniteSupport⟩, s.clock, s.global, s.compile, s.compileOracle, s.code, s.ffi⟩

/-- The BVI state and explicit finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) := by
  constructor
  · intro s; cases s; rfl
  · intro s; cases s with | mk refs clock global compile oracle code ffi => cases refs; rfl

/-- Decrement the BVI clock with natural-number subtraction. -/
@[hol "cakeml/compiler/backend/semantics/bviSemScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [refs])]
def decClock {C F : Type} (n : Nat) (s : BviState C F) : BviState C F :=
  { s with clock := s.clock - n }

/-- Copy the shared reference, clock and FFI fields from BVL to BVI. This
follows the source field update but is untagged until the representation
qualifier can name the references in both state carriers. -/
def fromBvl {C F : Type} (source : BvlSem.State C F) (target : BviState C F) : BviState C F :=
  { target with refs := source.refs, clock := source.clock, ffi := source.ffi }

end Flapjack.Compiler.Backend.BviSem
