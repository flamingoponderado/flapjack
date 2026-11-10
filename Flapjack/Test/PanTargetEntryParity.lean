module

public import Flapjack.Pancake.Proofs.PanSimp.ProgOfHOL
public import Flapjack.Pancake.PanGlobalsByteRanged
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
