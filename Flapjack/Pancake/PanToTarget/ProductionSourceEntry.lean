import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileExpCorrespondence
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileToCrepBridge
import Flapjack.Pancake.CrepInline.InlineRouteNames
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display
import Flapjack.Pancake.PanToTarget
import Mathlib.Data.List.TakeDrop

/-! Source-entry codec contracts for the anonymous first LET of the original
whole compiler. Reuse the reviewed `mainFirstHOL` infrastructure; there is no
independent HOL declaration to tag for this extracted operation. -/
namespace Flapjack.Pancake.PanToTarget
open Flapjack Pancake.PanLang Basis.Pure.MlString

end Flapjack.Pancake.PanToTarget
