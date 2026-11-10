module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
public import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
public import Flapjack.CompileFunctionDistinct
public import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
public import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
public import Flapjack.Pancake.CrepInline.InlineRouteNames
public import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
public import Flapjack.RiscV.WordDiagnostics
public import Flapjack.RiscV.WordFuseConditions
public import Flapjack.RiscV.WordUnreach
public import Flapjack.RiscV.Lab
public import Flapjack.Display
public import Flapjack.Pancake.PanToWord

@[expose] public section

namespace Flapjack.Test.PanNativeWordPrefixParity
open Flapjack Pancake.PanLang

private def declarations (width : Nat) : List (Decl (BitVec width)) :=
  [.function ⟨"f", false, false, [], .return (.const 7), .one⟩,
   .function ⟨"main", false, false, [], .call none "f" [], .one⟩]

private theorem source (width : Nat) : ∀ d ∈ declarations width, DeclByteRanged d := by
  intro d member
  simp [declarations] at member
  rcases member with rfl | rfl
  all_goals simp [DeclByteRanged, FunDeclByteRanged, ListParamByteRanged,
    ProgByteRanged, ExpByteRanged, NameRanged, ShapeByteRanged]

/-- Entire original Word program rows, including argument counts, call
arguments/continuations, labels, variables, constant and every Seq/Skip. -/
private def payloadMatches {width : Nat} : List (Nat × Nat × WordLangProgHOL (BitVec width)) → Bool
  | [(64, 1, .seq .skip (.seq (.call none (some 65) [0] none) .skip)),
     (65, 1, .seq (.call none (some 66) [0] none) .skip),
     (66, 1, .seq (.assign 2 (.const value)) (.seq (.return 0 [2]) .skip))] => value == 7
  | _ => false

end Flapjack.Test.PanNativeWordPrefixParity
