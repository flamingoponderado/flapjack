import Flapjack.Pancake.PanToTarget.ProductionSourceEntry

namespace Flapjack.Test.PanSourceEntryParity
open Flapjack Pancake.PanLang Pancake.PanToTarget Basis.Pure.MlString

private def function (name : String) (value : BitVec 8) (exported := false) : Decl (BitVec 8) :=
  .function ⟨name, false, exported, [], .return (.const value), .one⟩

private def payload : List (DeclHOL 8) → Option (List (String × Nat × Bool × Bool))
  | [] => some []
  | .function ⟨name, false, exported, [], .return (.const value), .one⟩ :: rest =>
      (payload rest).map ((toStringOfBytes name, value.toNat, exported, false) :: ·)
  | .exnDecl name .one :: rest =>
      (payload rest).map ((toStringOfBytes name, 0, false, true) :: ·)
  | _ => none

private def prepared (declarations : List (Decl (BitVec 8))) :=
  (panTargetMoveStartToFront "main" (panTargetDeclarationsWithDefaultMain declarations)).map declToHOL

private def completeCheck : Bool :=
  payload (prepared []) == some [] &&
  payload (prepared [function "f" 1, function "g" 3]) ==
    some [("main", 0, false, false), ("f", 1, false, false), ("g", 3, false, false)] &&
  payload (prepared [function "main" 2, function "f" 1, function "g" 3, function "main" 4 true]) ==
    some [("main", 2, false, false), ("f", 1, false, false), ("g", 3, false, false), ("main", 4, true, false)] &&
  payload (prepared [function "f" 1, function "main" 2, function "g" 3, function "main" 4 true]) ==
    some [("main", 2, false, false), ("f", 1, false, false), ("g", 3, false, false), ("main", 4, true, false)] &&
  payload (prepared [.exnDecl "E" .one, function "f" 1, function "main" 2,
      function "g" 3, function "main" 4 true]) ==
    some [("main", 2, false, false), ("E", 0, false, true), ("f", 1, false, false),
      ("g", 3, false, false), ("main", 4, true, false)]

#guard completeCheck
example {width : Nat} [NeZero width] (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    compileSourceWordNative? declarations source =
      some (panToWordCompileProgHOL .riscv (mainFirstHOL (declarations.map declToHOL))) :=
  compileSourceWordNative_original declarations source

private def missing : List (Decl (BitVec 8)) := [function "f" 7]
private theorem missingSource : ∀ d ∈ missing, DeclByteRanged d := by
  intro d member
  simp [missing] at member
  subst d
  simp [function, DeclByteRanged, FunDeclByteRanged, ProgByteRanged,
    ExpByteRanged, ListParamByteRanged, ShapeByteRanged, NameRanged]

private def missingMatches : List (Nat × Nat × WordLangProgHOL (BitVec 8)) → Bool
  | [(64, 1, .seq .skip (.seq (.call none (some 65) [0] none) .skip)),
     (65, 1, .seq (.assign 2 (.const zero)) (.seq (.return 0 [2]) .skip)),
     (66, 1, .seq (.assign 2 (.const value)) (.seq (.return 0 [2]) .skip))] => zero == 0 && value == 7
  | _ => false

private def wordCheck : Bool :=
  (match compileSourceWordNative? missing missingSource with
    | some rows => missingMatches rows
    | none => false) &&
  (match compileSourceWordNative? ([] : List (Decl (BitVec 8))) (by simp) with
    | some [] => true
    | _ => false)
#guard wordCheck

def runChecks : IO Bool := do
  if !(completeCheck && wordCheck) then throw (IO.userError "original source-entry/default native payload differs")
  IO.println "PASS complete original source preparation5cases and empty/missing nativeWord full rows, arbitrary-source kernel contract"
  return true
end Flapjack.Test.PanSourceEntryParity
