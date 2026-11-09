module

public import Flapjack.Misc.Option.Rel
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension
public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.BackendProps.Pure

@[expose] public section

/-! Candidate state relation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

/-- Related reference payloads have matching constructors and related values. -/
def RefRel : Ref Value → Ref Value → Prop
  | .valueArray left, .valueArray right => List.Forall₂ ValueRel left right
  | .byteArray left, .byteArray right => left = right
  | .thunk mode left, .thunk nextMode right => mode = nextMode ∧ ValueRel left right
  | _, _ => False

/-- A code entry retains its arity while its body is annotated. -/
def CodeRel (left right : Nat × ClosLang.Exp) : Prop :=
  right = (left.1, annotateSing left.1 left.2)

/-- Relate proof-side closure states around annotation. Reference and code
maps are compared by lookup; evaluator and carrier correspondence with HOL
remain to be reviewed. -/
def StateRel {C F : Type} (source target : State C F) : Prop :=
  source.clock = target.clock ∧ source.ffi = target.ffi ∧ source.maxApp = target.maxApp ∧
  target.compileOracle = (pureCo compileInc ∘ source.compileOracle) ∧
  source.compile = pureCc compileInc target.compile ∧
  List.Forall₂ (optionRel ValueRel) source.globals target.globals ∧
  (∀ key, optionRel RefRel (source.refs.lookup key) (target.refs.lookup key)) ∧
  (∀ key, optionRel CodeRel (source.code.lookup key) (target.code.lookup key))

/-- Code entries use exactly the source's singleton free-and-shift relation. -/
theorem codeRel_iff (arity : Nat) (body : ClosLang.Exp) (target : Nat × ClosLang.Exp) :
    CodeRel (arity, body) target ↔
      target.1 = arity ∧ shiftList (altFree [body]).1 0 arity .ln = [target.2] := by
  obtain ⟨nextArity, nextBody⟩ := target
  simp [CodeRel, annotateSing, altFree_singleton, shiftList, eq_comm]

/-- Updating both clocks preserves the annotation state relation. -/
theorem stateRel_withClock {C F : Type} {source target : State C F}
    (related : StateRel source target) (clock : Nat) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  simpa [StateRel] using related.2

/-- The empty initial source and target code stores are related. -/
theorem initialState_related {C F : Type} (ffi : HolFfiState F) (maxApp clock : Nat)
    (oracle : CompileOracle C) (compiler : Compiler C) :
    StateRel (initialState ffi maxApp HolFiniteMapExact.empty oracle (pureCc compileInc compiler) clock)
      (initialState ffi maxApp HolFiniteMapExact.empty (pureCo compileInc ∘ oracle) compiler clock) := by
  simp [StateRel, initialState, optionRel, HolFiniteMapExact.empty]

end Flapjack.Compiler.Backend.ClosAnnotate
