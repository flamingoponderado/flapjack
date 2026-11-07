import Flapjack.Compiler.Backend.ClosMti
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Test.MtiCakeBviOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Test.FullMtiInlineCakeWordOracle
import Flapjack.Test.FullBvlOptimizedCakeWordOracle
import Flapjack.Test.FullClosCallCakeWordOracle
import Flapjack.Test.FullClosKnownCakeWordOracle
import Flapjack.Test.FullDefaultFrontendWordOracle
import Flapjack.Test.BvlInlineCakeBviOracle
import Flapjack.Test.BvlHandleCakeBviOracle
import Flapjack.Test.BvlOptimizedCakeBviOracle

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
#guard (ClosMti.introMultiFuel 0 5 (.var .none 0)).isNone
#guard match ClosMti.compileFuel 0 true 5 [.var .none 0] with
  | some [.var .none 0] => true
  | _ => false
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

#guard match SourceToFlat.compileCakeToBviBvlOptimizedFuel 100 8 100 false SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.BvlOptimizedCakeBviOracle.matchesCaptured code
  | none => false

#guard match SourceToFlat.compileCakeToBviBvlOptimizedFuel 100 8 100 false SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) =>
      code.map (fun (loc, _, body) => (loc, BviTailrec.hasRecFuel 100 loc body)) ==
        [(62, some false), (63, some false), (64, some false), (65, some false),
         (66, some false), (67, some false), (68, some false), (69, some false),
         (72, some false), (73, some false), (76, some false), (77, some false),
         (80, some false), (84, some false), (88, some false), (92, some false),
         (96, some false), (100, some false)]
  | none => false

#guard match SourceToFlat.compileCakeToBviTailrecCheckedFuel 100 8 100 false SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, _, _, _) => true
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

#guard match SourceToFlat.compileCakeToWord64OptimizedFuel 100 8 100 false
    SourceToFlat.emptyConfig mtiConfig wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullBvlOptimizedCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

#guard match SourceToFlat.compileCakeToWord64ConfiguredFuel 100 SourceToFlat.emptyConfig
    { mtiConfig with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) }
    BvlToBvi.defaultConfig wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _) => Flapjack.Test.FullDefaultFrontendWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

#guard match SourceToFlat.compileCakeToBviConfiguredFuel 100 SourceToFlat.emptyConfig
    { mtiConfig with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) } BvlToBvi.defaultConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, closure, config, code, names) =>
      closure.start == 64 && config.nextName1 == 0 && config.nextName2 == 74 && config.nextName3 == 75 &&
      (sptToAList config.inlines).map Prod.fst == [7, 5, 4, 2, 6] &&
      (sptToAList config.bviInlines).isEmpty && code.length == 16 &&
      (sptToAList names).map Prod.fst == [63, 67, 65, 69, 64, 96, 80, 72, 88, 68, 100, 84, 76, 92, 66, 62]
  | none => false

#guard match SourceToFlat.compileCakeToWord64OptimizedFuel 100 8 100 false
    SourceToFlat.emptyConfig { mtiConfig with doCall := true, knownConf := some (ClosKnown.defaultConfig 2) } wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullClosKnownCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

#guard match SourceToFlat.compileCakeToWord64OptimizedFuel 100 8 100 false
    SourceToFlat.emptyConfig { mtiConfig with doCall := true } wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullClosCallCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

end Flapjack.Test.ClosMtiParity
