module

public import Flapjack.SemanticPrimitivesHOL.Control

-- Checks below run compiled code from these modules.
public meta import Flapjack.AstHOL.LitOp
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.SemanticPrimitivesHOL
public meta import Flapjack.SemanticPrimitivesHOL.Control
public meta import Flapjack.SemanticPrimitivesHOL.Thunk
@[expose] public section

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
-- HOL build_constrs is polymorphic in the constructor argument payloads.
#guard match buildConstrs 3 [(ofString "A", ([4, 5] : List Nat))] with
  | [(name, 2, .typeStamp stampName 3)] => name == ofString "A" && stampName == name
  | _ => false
#guard match buildConstrs 3 [(ofString "A", [true, false])] with
  | [(name, 2, .typeStamp stampName 3)] => name == ofString "A" && stampName == name
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
