import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
import Flapjack.Pancake.PanGlobalsByteRanged
import Flapjack.Pancake.PanStructs.CompileDeclsCorrespondence
import Flapjack.Pancake.PanSimpByteRanged
import Flapjack.CompileFunctionDistinct
import Flapjack.Pancake.CrepToLoop.Optimise
import Flapjack.Pancake.CrepToLoop.ProductionCompileProg
import Flapjack.Pancake.PanToCrep.CompileProgCorrespondence
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.LoopToWord.LoopProgCarrierCodec
import Flapjack.RiscV.WordDiagnostics
import Flapjack.RiscV.WordFuseConditions
import Flapjack.RiscV.WordUnreach
import Flapjack.RiscV.Lab
import Flapjack.Display

namespace Flapjack.Test.PanTargetEntryParity
open Flapjack Pancake.PanLang

private def function (name : String) (value : BitVec 8) (exported := false) : Decl (BitVec 8) :=
  .function ⟨name, false, exported, [], .return (.const value), .one⟩

private def input : List (Decl (BitVec 8)) :=
  [function "f" 1, function "main" 2, function "g" 3, function "main" 4 true]

/-- Observe every field of this source fixture, rejecting other payloads. -/
private def payload : List (Decl (BitVec 8)) → Option (List (String × Nat × Bool))
  | [] => some []
  | .function ⟨name, false, exported, [], .return (.const value), .one⟩ :: rest =>
      (payload rest).map ((name, value.toNat, exported) :: ·)
  | _ => none

end Flapjack.Test.PanTargetEntryParity
