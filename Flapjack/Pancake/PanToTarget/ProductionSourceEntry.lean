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
public import Flapjack.Pancake.PanToTarget
public import Mathlib.Data.List.TakeDrop

@[expose] public section

/-! Source-entry codec contracts for the anonymous first LET of the original
whole compiler. Reuse the reviewed `mainFirstHOL` infrastructure; there is no
independent HOL declaration to tag for this extracted operation. -/
namespace Flapjack.Pancake.PanToTarget
open Flapjack Pancake.PanLang Basis.Pure.MlString

end Flapjack.Pancake.PanToTarget
