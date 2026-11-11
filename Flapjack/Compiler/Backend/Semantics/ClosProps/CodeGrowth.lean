module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateCodeGrowth

@[expose] public section

/-! Closure evaluation preserves installed code. -/
namespace Flapjack.Compiler.Backend.ClosProps.CodeGrowthPort
open Flapjack ClosSem SemanticPrimitivesHOL

/-- Closure states use the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Evaluation preserves every code entry present in the initial state. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "evaluate_mono"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_mono {C F : Type} (xs : List ClosLang.Exp) (env : List ClosSem.Value)
    (s1 : State C F) (vs : Result (List ClosSem.Value) ClosSem.Value) (s2 : State C F)
    (h : evaluate xs env s1 = (vs, s2)) : s1.code.submap s2.code :=
  evaluate_code_growth.1 xs env s1 s2 vs h

end Flapjack.Compiler.Backend.ClosProps.CodeGrowthPort
