module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.State
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.FiniteMap.SubmapExact
public import Flapjack.FiniteMap.DomainExact

@[expose] public section

/-! Closure-state relations for code-map extension. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Compiler.Backend.BackendProps

namespace SubmapRelPort
/-- The state carrier uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ state : StateBroad C F, (State.ofBroad state).toBroad = state) ∧
      (∀ state : State C F, State.ofBroad state.toBroad = state) :=
  ClosSem.holFmapAsFiniteSupportWitness
end SubmapRelPort

/-- Labels installed by an oracle entry. -/
def oracleCodeNames {C : Type} (entry : C × (List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))) : Set Nat :=
  { key | key ∈ entry.2.2.map Prod.fst }

/-- The target has a larger code map, and future oracle labels follow it. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "SUBMAP_rel_def"
  (fmap_as_finite_support := [refs, code])]
def CodeExtension {C F : Type} (source target : State C F) : Prop :=
  target = { source with code := target.code } ∧ source.code.submap target.code ∧
    oracleMonotonic oracleCodeNames (· < ·) target.code.domain source.compileOracle

end Flapjack.Compiler.Backend.ClosSem
