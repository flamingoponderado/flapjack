import Flapjack.Pancake.CrepToLoop.ProductionDeclarations

namespace Flapjack.Test.CrepToLoopNativeDeclarationsParity
open Flapjack CrepToLoopProduction Pancake.PanLang Basis.Pure.MlString

private def declarations : List (Decl (BitVec 8)) :=
  [.function ⟨"f", false, false, [], .call none "g" [], .one⟩,
   .function ⟨"g", false, false, [], .return (.const 7), .one⟩]

private theorem source : ∀ d ∈ declarations, DeclByteRanged d := by
  intro d member
  simp [declarations] at member
  rcases member with rfl | rfl
  all_goals simp [DeclByteRanged, FunDeclByteRanged, ListParamByteRanged,
    ProgByteRanged, ExpByteRanged, NameRanged, ShapeByteRanged]

/-- Complete original raw Crep table, before any generic arithmetic pass. -/
private def rawMatches : List (MlString × List Nat × CrepProgHOL 8) → Bool
  | [(first, [], .call none target []), (second, [], .return [.const value])] =>
    first == ofString "f" && target == ofString "g" && second == ofString "g" && value == 7
  | _ => false

/-- Complete original two-pass native Loop table and both bodies. -/
private def loopMatches : List (Nat × List Nat × HolLoopProg 8) → Bool
  | [(64, [], .mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))),
     (65, [], .mark (.seq (.mark (.assign 1 (.const value)))
       (.mark (.seq (.mark (.return [1])) (.mark .skip)))))] => value == 7
  | _ => false

def fullCheck : Bool :=
  rawMatches (sourcePrograms (compileProgNativeWithMetadata declarations source)) &&
    match compileDeclarationsToLoopNative? declarations source with
    | none => false
    | some rows => loopMatches rows

#guard fullCheck
example : compileDeclarationsToLoopNative? declarations source =
    some (compileProgHOLExact .riscv (compileProgDeclsHOLW (declarations.map declToHOL))) :=
  compileDeclarationsToLoopNative_original declarations source

def runChecks : IO Bool := do
  if !fullCheck then throw (IO.userError "original declaration/Crep/Loop complete payload differs")
  IO.println "PASS original declaration-to-native-Loop composition: complete raw Crep metadata/payload and original rows64+65/Call65, source guard derived"
  return true

end Flapjack.Test.CrepToLoopNativeDeclarationsParity
