import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Test.MtiCakeBviOracle

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

end Flapjack.Test.ClosMtiParity
