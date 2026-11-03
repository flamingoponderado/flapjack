import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownGlobals
import Flapjack.Compiler.Backend.ClosKnown.Proofs.OpEvaluateGlobals

/-! Global approximation preservation for the executed known traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.ApproxEvaluate
open ClosSem ClosProps ClosProps.StateGlobalSafety UniqueGlobalsPort
open Flapjack.SemanticPrimitivesHOL

/-- Evaluating one program preserves the approximation produced by traversing
another program when their writes are unique and initially disjoint. This is
Flapjack infrastructure until the total traversal is reviewed as HOL `known`. -/
theorem stateGlobalsApproxKnownListEvaluate {C F : Type}
    (xs : List ClosLang.Exp) (env : List ClosSem.Value) (s0 : State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : State C F)
    (c : Config) (ys : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : evaluate xs env s0 = (res, s) ∧ knownListTotal c ys aenv g0 = (eas, g) ∧
      ssgcFree s0 ∧ (∀ v ∈ env, vsgcFree v) ∧ (∀ e ∈ xs, esgcFree e) ∧
      mglobalsDisjoint s0.globals ys ∧ uniqueSetGlobals (xs ++ ys) s0.compileOracle ∧
      stateGlobalsApprox s g0) : stateGlobalsApprox s g := by
  rcases h with ⟨run, known, safe, envSafe, expSafe, disjoint, unique, approx⟩
  have swapped : uniqueSetGlobals (ys ++ xs) s0.compileOracle := by
    intro n k
    have bound := unique n k
    simp only [elistGlobals_append] at bound ⊢
    omega
  have finalDisjoint := mglobalsDisjointEvaluate s0 ys xs env res s
    ⟨run, safe, envSafe, expSafe, swapped, disjoint⟩
  intro key value a ⟨found, lookup⟩
  rcases knownListTotalChangedGlobalsCases c ys aenv g0 eas g known key a lookup with old | written
  · exact approx key value a ⟨found, old⟩
  · exact False.elim ((Set.disjoint_left.mp finalDisjoint) ⟨value, found⟩ written)

end Flapjack.Compiler.Backend.ClosKnown.ApproxEvaluate
