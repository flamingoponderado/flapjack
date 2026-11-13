module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.Pancake.PanStructs.CompileDeclsExact
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.CompFuncExact
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display

@[expose] public section

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

end Flapjack.Test.PanNativeFrontendPrefixParity
