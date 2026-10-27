import Flapjack.SemanticPrimitivesHOL.Operations

/-! Source equality and application observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceOpsParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def emptyEnv : SemEnv Value := ⟨.bind [] [], .bind [] []⟩
private def x : AstHOL.Exp := .var (.short (ofString "x"))
private def y : AstHOL.Exp := .var (.short (ofString "y"))
private def intV (n : Int) : Value := .litv (.intLit n)

#guard doEq (intV 3) (intV 3) = .val true
#guard doEq (intV 3) (.litv (.char 97)) = .typeError
#guard doEqList [intV 1, intV 1] [intV 2, .litv (.char 97)] = .val false
#guard doEq (.loc false 1) (.loc true 1) = .typeError
#guard doEq (.conv (some (.typeStamp (ofString "A") 7)) [])
    (.conv (some (.typeStamp (ofString "B") 7)) []) = .val false
#guard doEq (.closure emptyEnv (ofString "x") x) (.recclosure emptyEnv [] (ofString "f")) = .val true
#guard match doOpApp [.closure emptyEnv (ofString "x") x, intV 4] with
  | some (env, _) => match NamespaceHOL.nsLookup env.v (.short (ofString "x")) with
    | some (.litv (.intLit 4)) => true
    | _ => false
  | none => false
#guard (doOpApp [.recclosure emptyEnv [(ofString "f", ofString "x", x),
    (ofString "f", ofString "y", y)] (ofString "f"), intV 4]).isNone

end Flapjack.Test.CakeSourceOpsParity
