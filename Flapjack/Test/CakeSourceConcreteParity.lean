import Flapjack.SemanticPrimitivesHOL.Concrete

/-! Concrete-value observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceConcreteParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def emptyEnv : SemEnv Value := ⟨.bind [] [], .bind [] []⟩
private def closure : Value := .closure emptyEnv (ofString "x") (.var (.short (ofString "x")))

#guard concreteValue (.litv (.intLit 1))
#guard concreteValue (.loc false 0)
#guard concreteValue (.conv none [.litv (.intLit 1), .vectorv [.loc true 2]])
#guard !concreteValue closure
#guard !concreteValue (.conv none [.litv (.intLit 1), .vectorv [closure]])
#guard !concreteValue (.env emptyEnv (0, 0))

end Flapjack.Test.CakeSourceConcreteParity
