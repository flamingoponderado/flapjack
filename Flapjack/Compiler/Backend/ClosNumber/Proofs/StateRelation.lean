import Flapjack.Compiler.Backend.ClosNumber.Proofs.ValueRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.BackendProps.StateCompiler

/-! State relation for the closure-numbering simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Relate closure reference payloads using the numbering value relation. -/
def RefRel (maxApp : Nat) : Ref Value → Ref Value → Prop
  | .valueArray left, .valueArray right => List.Forall₂ (ValueRel maxApp) left right
  | .byteArray left, .byteArray right => left = right
  | .thunk leftMode left, .thunk rightMode right => leftMode = rightMode ∧ ValueRel maxApp left right
  | _, _ => False

/-- Option lifting used for globals and finite-map lookup results. -/
def OptionRel {α β : Type} (relation : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some left, some right => relation left right
  | _, _ => False

/-- Source-shaped numbering state relation. The code and reference stores use
the proof-side finite-support carrier; exact source correspondence and the
numbering evaluator simulation remain open. -/
def StateRel {C F : Type} (source : State (Nat × C) F) (target : State C F) : Prop :=
  source.clock = target.clock ∧ source.ffi = target.ffi ∧ target.maxApp = source.maxApp ∧
  source.compile = stateCc (ignoreTable compileInc) target.compile ∧
  target.compileOracle = stateCo (ignoreTable compileInc) source.compileOracle ∧
  (∀ key, OptionRel (RefRel source.maxApp) (source.refs.lookup key) (target.refs.lookup key)) ∧
  List.Forall₂ (OptionRel (ValueRel source.maxApp)) source.globals target.globals ∧
  (∀ index, (source.compileOracle index).2.2 = [] ∧
    ¬ ClosProps.containsAppSome source.maxApp (source.compileOracle index).2.1) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty

/-- Related states expose identical clocks and maximum application arities. -/
theorem stateRel_clock_maxApp {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (related : StateRel source target) : source.clock = target.clock ∧ source.maxApp = target.maxApp :=
  ⟨related.1, related.2.2.1.symm⟩

/-- Updating both clocks preserves the numbering state relation. -/
theorem stateRel_withClock {C F : Type} {source : State (Nat × C) F} {target : State C F}
    (clock : Nat) (related : StateRel source target) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  simpa [StateRel] using related.2

/-- Initial states satisfy the relation whenever future incremental source
programs contain no pre-numbered applications or auxiliary code. This shows
that the state relation is inhabited under its intended oracle conditions. -/
theorem initialState_stateRel {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle (Nat × C)) (compiler : Compiler C)
    (safe : ∀ index, (oracle index).2.2 = [] ∧ ¬ ClosProps.containsAppSome maxApp (oracle index).2.1) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle
        (stateCc (ignoreTable compileInc) compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty
        (stateCo (ignoreTable compileInc) oracle) compiler clock) := by
  simp [StateRel, initialState, HolFiniteMapExact.empty, OptionRel, safe]

end Flapjack.Compiler.Backend.ClosNumber
