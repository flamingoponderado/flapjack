module

public import Flapjack.Compiler.Inference.Infer.Pattern

@[expose] public section

/-! Source HOL pattern evaluations captured in env_rel_init_probe.out. -/
namespace Flapjack.Test.CakePatternModelParity
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Basis.Pure.MlString Flapjack.Translator.Monadic.MonadBase
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.Infer.Pattern
  Flapjack.Compiler.Inference.Infer.HOLState Flapjack.Compiler.Inference.Infer.Operations

private def loc : LocErrInfo := ⟨none, nsEmpty⟩

example (subst : Flapjack.HolFiniteMapExact Nat Flapjack.Compiler.Inference.InferT) :
    inferPatternModel loc emptyEnv (.pvar (ofString "x")) ⟨3, subst, 7⟩ =
      (.success (.uvar 3, [(ofString "x", .uvar 3)]), ⟨4, subst, 7⟩) := by
  simp [inferPatternModel, HOLState.freshUvar, Flapjack.Translator.Monadic.MonadBase.bind, ret]

example (subst : Flapjack.HolFiniteMapExact Nat Flapjack.Compiler.Inference.InferT) :
    inferPatternModel loc emptyEnv (.plit (.float64 0)) ⟨3, subst, 7⟩ =
      (.failure (none, ofString "Floats cannot be used in patterns"), ⟨3, subst, 7⟩) := by
  simp [inferPatternModel, Operations.failwith, loc]

example (subst : Flapjack.HolFiniteMapExact Nat Flapjack.Compiler.Inference.InferT) :
    inferPatternModel loc emptyEnv (.pcon none [.pvar (ofString "a"), .pvar (ofString "b")])
      ⟨3, subst, 7⟩ =
      (.success (.app [.uvar 3, .uvar 4] 9,
        [(ofString "b", .uvar 4), (ofString "a", .uvar 3)]), ⟨5, subst, 7⟩) := by
  simp [inferPatternModel, inferPatternsModel, HOLState.freshUvar,
    Flapjack.Translator.Monadic.MonadBase.bind, ret]

end Flapjack.Test.CakePatternModelParity
