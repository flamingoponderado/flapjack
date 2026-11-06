import Flapjack.Compiler.Backend.ClosCall.Proofs.ApplicationSimulation
import Flapjack.Compiler.Backend.ClosCall.Proofs.EvaluateControlWellformed
import Flapjack.Compiler.Backend.ClosCall.Proofs.RecursiveInvariant
import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateForce
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

/-! Recursive binding simulation under the source invariants. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

/-- Source evaluation of a traversed function preserves well-formedness at
any independent relation fuel, provided its compiler state is extended and
its generated code is included. This is Flapjack-specific infrastructure. -/
theorem callsFuel_fn_source_wellFormed_atFuel {C F : Type} (traversalFuel relationFuel : Nat)
    (name : Basis.Pure.MlString.MlString) (loc arity : Nat) (body out : ClosLang.Exp)
    (initial final g : State) (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (env : List ClosSem.Value) (source : ClosSem.State (NumSet × C) F)
    (run : callsFuel (traversalFuel + 1) (.fn name (some loc) none arity body) initial = some (out, final))
    (initialWf : wellFormed initial)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (annotations : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : LabelsFresh (codeLocations [.fn name (some loc) none arity body]) initial)
    (growth : stateExtends final g)
    (coverage : ∀ k ∈ codeLocations [.fn name (some loc) none arity body], ¬ sptDomain final.1 k → k ∈ allowed)
    (included : codeIncludes final.2 code)
    (envWf : ValuesWellFormedFuel relationFuel g allowed code env)
    (sourceWf : StateWellFormedFuel relationFuel g allowed code source) :
    EvalWellFormedFuel relationFuel g allowed code (evaluate [.fn name (some loc) none arity body] env source) := by
  obtain ⟨targetBody, _, closure⟩ := callsFuel_fn_relation_atFuel traversalFuel relationFuel name loc arity body out
    initial final g allowed code run initialWf locations annotations distinct fresh growth coverage included
  exact evaluate_fn_state_wellFormedFuel name loc arity none body [(arity, targetBody)] env source envWf sourceWf closure

end Flapjack.Compiler.Backend.ClosCall
