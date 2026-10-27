import Flapjack.SemanticPrimitivesHOL.Control

/-! Source control and declaration observations captured from pinned HOL. -/
namespace Flapjack.Test.CakeSourceControlParity
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

private def emptyEnv : SemEnv Value := ⟨.bind [] [], .bind [] []⟩
private def x : AstHOL.Exp := .var (.short (ofString "x"))

#guard doIf (boolValue true) (1 : Nat) 2 = some 1
#guard doIf (boolValue false) (1 : Nat) 2 = some 2
#guard (doIf (.litv (.intLit 0)) (1 : Nat) 2).isNone
#guard match doLog .andalso (boolValue true) x with
  | some (.exp (.var (.short name))) => name == ofString "x"
  | _ => false
#guard match doLog .andalso (boolValue false) x with
  | some (.val (.conv (some (.typeStamp name 0)) [])) => name == ofString "False"
  | _ => false
#guard match NamespaceHOL.nsLookup (buildTdefs 5
    [([], ofString "t", [(ofString "A", [])]), ([], ofString "u", [(ofString "A", [])])])
    (.short (ofString "A")) with
  | some (0, .typeStamp name 6) => name == ofString "A"
  | _ => false
#guard !checkDupCtors ([], ofString "t", [(ofString "A", []), (ofString "A", [])])
#guard match combineDecResult emptyEnv (Result.err (.raise 3) : Result (SemEnv Value) Nat) with
  | .err (.raise 3) => true
  | _ => false

end Flapjack.Test.CakeSourceControlParity
