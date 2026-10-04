import Flapjack.Pipeline

namespace Flapjack.Test.PanTargetEntryParity
open Flapjack Pancake.PanLang

private def function (name : String) (value : BitVec 8) (exported := false) : Decl (BitVec 8) :=
  .function ⟨name, false, exported, [], .return (.const value), .one⟩

private def input : List (Decl (BitVec 8)) :=
  [function "f" 1, function "main" 2, function "g" 3, function "main" 4 true]

example : panTargetMoveStartToFront "main" (.exnDecl "E" .one :: input) =
    [function "main" 2, .exnDecl "E" .one, function "f" 1,
     function "g" 3, function "main" 4 true] := rfl

-- Entire declarations, including distinguishable bodies and export flags.
example : panTargetMoveStartToFront "main" input =
    [function "main" 2, function "f" 1, function "g" 3, function "main" 4 true] := rfl
example : panTargetMoveStartToFront "main" ([] : List (Decl (BitVec 8))) = [] := rfl
example : panTargetMoveStartToFront "missing" input = input := rfl
example : panTargetMoveStartToFront "f" input = input := rfl
example : panTargetMoveStartToFront "g" input =
    [function "g" 3, function "f" 1, function "main" 2, function "main" 4 true] := rfl
example : panTargetMoveStartToFront "main" (panTargetDeclarationsWithDefaultMain
    [function "f" 1, function "g" 3]) =
    [function "main" 0, function "f" 1, function "g" 3] := rfl
example : panTargetMoveStartToFront "main"
    (panTargetDeclarationsWithDefaultMain ([] : List (Decl (BitVec 8)))) = [] := rfl

/-- Observe every field of this source fixture, rejecting other payloads. -/
private def payload : List (Decl (BitVec 8)) → Option (List (String × Nat × Bool))
  | [] => some []
  | .function ⟨name, false, exported, [], .return (.const value), .one⟩ :: rest =>
      (payload rest).map ((name, value.toNat, exported) :: ·)
  | _ => none

private def checks : Bool :=
  payload (panTargetMoveStartToFront "main" input) ==
    some [("main", 2, false), ("f", 1, false), ("g", 3, false), ("main", 4, true)] &&
  payload (panTargetMoveStartToFront "missing" input) == payload input &&
  payload (panTargetMoveStartToFront "f" input) == payload input &&
  payload (panTargetMoveStartToFront "g" input) ==
    some [("g", 3, false), ("f", 1, false), ("main", 2, false), ("main", 4, true)] &&
  payload (panTargetMoveStartToFront "main" (panTargetDeclarationsWithDefaultMain
    [function "f" 1, function "g" 3])) ==
    some [("main", 0, false), ("f", 1, false), ("g", 3, false)] &&
  payload (panTargetMoveStartToFront "main"
    (panTargetDeclarationsWithDefaultMain ([] : List (Decl (BitVec 8))))) == some []

#guard checks

def runChecks : IO Bool := do
  if !checks then throw (IO.userError "first-match entry declaration order or payload differs")
  IO.println "PASS original first-match entry movement: full duplicate payloads, missing/head/custom entry and synthesized default"
  return true
end Flapjack.Test.PanTargetEntryParity
