import Flapjack.Pipeline

namespace Flapjack.Test.PanNativeFrontendPrefixParity
open Flapjack Pancake.PanLang

private def declarations : List (Decl (BitVec 8)) :=
  [.function ⟨"f", false, false, [], .return (.const 7), .one⟩,
   .function ⟨"main", false, false, [], .call none "f" [], .one⟩]

private theorem source : ∀ d ∈ declarations, DeclByteRanged d := by
  intro d member
  simp [declarations] at member
  rcases member with rfl | rfl
  all_goals simp [DeclByteRanged, FunDeclByteRanged, ListParamByteRanged,
    ProgByteRanged, ExpByteRanged, NameRanged, ShapeByteRanged]

private def cakeMatches : List (Decl (BitVec 8)) → Bool
  | [.function ⟨a, false, false, [], .seq .skip (.call none target []), .one⟩,
     .function ⟨b, false, false, [], .call none called [], .one⟩,
     .function ⟨c, false, false, [], .return (.const value), .one⟩] =>
      a == "main" && target == "main'" && b == "main'" && called == "f" &&
      c == "f" && value == 7
  | _ => false

private def rawMatches : List (CompiledFunction (BitVec 8)) → Bool
  | [⟨a, [], .seq .skip (.call none target []), .one⟩,
     ⟨b, [], .call none called [], .one⟩,
     ⟨c, [], .return [.const value], .one⟩] =>
      a == "main" && target == "main'" && b == "main'" && called == "f" &&
      c == "f" && value == 7
  | _ => false

private def loopMatches : List (Nat × List Nat × HolLoopProg 8) → Bool
  | [(64, [], .mark (.seq (.mark .skip)
        (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))),
     (65, [], .mark (.seq (.mark (.call none (some 66) [] none)) (.mark .skip))),
     (66, [], .mark (.seq (.mark (.assign 1 (.const value)))
        (.mark (.seq (.mark (.return [1])) (.mark .skip)))))] => value == 7
  | _ => false

private def fullCheck : Bool :=
  let frontend := compileFlapjackFrontendCake "main" declarations (some (.isTrue source))
  cakeMatches frontend.2.2.1 && rawMatches frontend.2.2.2 &&
    match compileFlapjackFrontendLoopNative? "main" declarations source with
    | some rows => loopMatches rows
    | none => false

#guard fullCheck
example : compileFlapjackFrontendLoopNative? "main" declarations source =
    some (compileProgHOLExact .riscv
      (compileProgDeclsHOLW ((frontendCakeDeclarations "main" declarations).map declToHOL))) :=
  compileFlapjackFrontendLoopNative_original "main" declarations source

def runChecks : IO Bool := do
  if !fullCheck then throw (IO.userError "original full frontend/native prefix payload differs")
  IO.println "PASS original native frontend prefix: full Cake declarations, raw Crep fields, original rows64/65/66 and calls65/66; source premises derived"
  return true
end Flapjack.Test.PanNativeFrontendPrefixParity
