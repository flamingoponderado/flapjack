import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Test.MtiCakeBviOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Test.FullMtiInlineCakeWordOracle
import Flapjack.Test.BvlInlineCakeBviOracle
import Flapjack.Test.BvlHandleCakeBviOracle

/-! Original examples for checked multi-argument introduction. -/
namespace Flapjack.Test.ClosMtiParity
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

#guard match ClosMti.collectArgs 5 1 (.fn (ofString "f") none none 2 (.fn (ofString "g") none none 3 (.var .none 0))) with
  | (3, .fn name none none 3 (.var .none 0)) => decide (name = ofString "g")
  | _ => false
#guard match ClosMti.collectApps 4 [.var .none 3]
    (.app .none none (.var .none 0) [.var .none 1, .var .none 2]) with
  | ([.var .none 3, .var .none 1, .var .none 2], .var .none 0) => true
  | _ => false
#guard match ClosMti.compileFuel 8 true 5
    [.fn (ofString "f") none none 1 (.fn (ofString "g") none none 2 (.var .none 0)),
     .app .none none (.app .none none (.var .none 0) [.var .none 1, .var .none 2]) [.var .none 3]] with
  | some [.fn name none none 3 (.var .none 0), .app .none none (.var .none 0)
      [.var .none 3, .var .none 1, .var .none 2]] => decide (name = ofString "f")
  | _ => false
#guard (ClosMti.compileFuel 0 true 5 [.var .none 0]).isNone
#guard match ClosMti.compileFuel 0 false 5 [.var .none 0] with
  | some [.var .none 0] => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.closure_mti

private def mtiConfig : ClosToBvl.Config :=
  { ClosToBvl.defaultConfig with doMti := true, doCall := false, knownConf := none, maxApp := 2 }

#guard match SourceToFlat.compileCakeToBviMtiFuel 100 SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.MtiCakeBviOracle.matchesCaptured code
  | none => false

#guard match SourceToFlat.compileCakeToBviBvlInlineFuel 100 8 SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.BvlInlineCakeBviOracle.matchesCaptured code
  | none => false

#guard match SourceToFlat.compileCakeToBviBvlHandleFuel 100 8 100 false SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.BvlHandleCakeBviOracle.matchesCaptured code
  | none => false

private def wordConfig : DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

#guard match SourceToFlat.compileCakeToWordWithStubsAndNames64InlineFuel 100
    SourceToFlat.emptyConfig mtiConfig wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullMtiInlineCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

end Flapjack.Test.ClosMtiParity
