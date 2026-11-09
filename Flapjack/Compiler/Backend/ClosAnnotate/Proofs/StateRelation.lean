import Flapjack.Misc.Option.Rel
import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.EnvironmentExtension
import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.ClosProps.RefRelations
import Flapjack.Compiler.Backend.BackendProps.Pure

/-! Candidate state relation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.BackendProps

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
  (∀ key, optionRel (ClosProps.refRel ValueRel) (source.refs.lookup key) (target.refs.lookup key)) ∧
  (∀ key, optionRel CodeRel (source.code.lookup key) (target.code.lookup key))

/-- Updating both clocks preserves the annotation state relation. -/
theorem stateRel_withClock {C F : Type} {source target : State C F}
    (related : StateRel source target) (clock : Nat) :
    StateRel { source with clock := clock } { target with clock := clock } := by
  simpa [StateRel] using related.2

end Flapjack.Compiler.Backend.ClosAnnotate
