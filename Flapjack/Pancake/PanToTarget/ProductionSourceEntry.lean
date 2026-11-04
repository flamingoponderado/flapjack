import Flapjack.Pancake.PanSimp.DeclsProduction
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileTopProduction
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionDeclarations
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

private theorem mainName_codec (name : String) (ranged : NameRanged name) :
    ofString name = ofString "main" ↔ name = "main" := by
  constructor
  · intro encoded
    have decoded := congrArg toStringOfBytes encoded
    rw [toStringOfBytes_ofString_of_bytes name ranged] at decoded
    exact decoded
  · intro same
    rw [same]

end Flapjack.Pancake.PanToTarget
