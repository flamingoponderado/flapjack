import Flapjack.SemanticPrimitivesHOL

/-! Source constructor observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceConstructorParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def a : Stamp := .typeStamp (ofString "A") 7
private def b : Stamp := .typeStamp (ofString "B") 7
private def env : NamespaceHOL.Namespace AstHOL.ModN AstHOL.ConN (Nat × Stamp) :=
  .bind [(ofString "A", (1, a))] []

#guard sameType a b
#guard !sameCtor a b
#guard sameType (.exnStamp 1) (.exnStamp 2)
#guard doConCheck env (some (.short (ofString "A"))) 1
#guard !doConCheck env (some (.short (ofString "A"))) 0
#guard match buildConv env (some (.short (ofString "A"))) [] with
  | some (.conv (some (.typeStamp name 7)) []) => name == ofString "A"
  | _ => false

-- HOL's `find_recfun` has independent second and third payload types.
example : findRecFun (ofString "f") [(ofString "f", 2, true)] = some (2, true) := by decide

end Flapjack.Test.CakeSourceConstructorParity
