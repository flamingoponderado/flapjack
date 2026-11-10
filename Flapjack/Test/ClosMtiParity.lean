module

public import Flapjack.Compiler.Backend.ClosMti
public import Flapjack.Test.CakeMLFlatOracle
public import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
public import Flapjack.Test.MtiCakeBviOracle
public import Flapjack.Compiler.Backend.SourceToFlat.ToWord
public import Flapjack.Test.FullMtiInlineCakeWordOracle
public import Flapjack.Test.FullBvlOptimizedCakeWordOracle
public import Flapjack.Test.FullDefaultFrontendWordOracle
public import Flapjack.Test.BvlInlineCakeBviOracle
public import Flapjack.Test.BvlHandleCakeBviOracle
public import Flapjack.Test.BvlOptimizedCakeBviOracle
public import Flapjack.Compiler.Backend.BvlInline.Program
public import Flapjack.Compiler.Backend.BvlInline.LetOp
public import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public import Flapjack.Compiler.Backend.BvlHandle.Compile
public import Flapjack.Compiler.Backend.BvlHandle.Simplify
public meta import Flapjack.Compiler.Backend.ClosLang.Syntax
public meta import Flapjack.Compiler.Backend.ClosMti
public meta import Flapjack.Test.CakeMLFlatOracle
public meta import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
public meta import Flapjack.Test.MtiCakeBviOracle
public meta import Flapjack.Test.BvlInlineCakeBviOracle
public meta import Flapjack.Test.BvlHandleCakeBviOracle
public meta import Flapjack.Test.BvlOptimizedCakeBviOracle
public meta import Flapjack.Test.FullMtiInlineCakeWordOracle
public meta import Flapjack.Compiler.Backend.SourceToFlat.ToWord
public meta import Flapjack.Test.FullBvlOptimizedCakeWordOracle
public meta import Flapjack.Test.FullDefaultFrontendWordOracle
public meta import Flapjack.Compiler.Backend.BvlInline.Program
public meta import Flapjack.Compiler.Backend.BvlInline.RemoveTicks
public meta import Flapjack.Compiler.Backend.BvlInline.LetOp
public meta import Flapjack.Compiler.Backend.BvlHandle.Simplify
public meta import Flapjack.Compiler.Backend.BvlHandle.Compile

@[expose] public section

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

-- Replay the original HOL stage probes directly, without adding partial
-- compiler entry points to the production pipeline.
private def bvlStage (withHandle : Bool) (decls : List AstHOL.Dec) :
    Option (List (Nat × Nat × Bvi.Exp)) := do
  let (_, exps) ← SourceToFlat.compileCakeToClosFuel 100 SourceToFlat.emptyConfig decls
  let (closure, bvl, _) ← ClosToBvl.compileCallMtiFuel? 100 mtiConfig exps
  let bvl := (BvlInline.tickCompileProg 8 .ln bvl).2.map fun (n, a, e) =>
    (n, a, BvlInline.letOpSing (BvlInline.removeTicksSing e))
  let bvl := if withHandle then bvl.map (fun (n, a, e) =>
    (n, a, (BvlHandle.compileSing 100 a (BvlHandle.handleSimp e)).1)) else bvl
  let (_, code, _) ← BvlToBvi.compileProgFuel 100 100 closure.start 0 bvl
  pure code

#guard match SourceToFlat.compileCakeToBviBeforeOptimizationsFuel 100 SourceToFlat.emptyConfig mtiConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.MtiCakeBviOracle.matchesCaptured code
  | none => false

#guard match bvlStage false
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some code => Flapjack.Test.BvlInlineCakeBviOracle.matchesCaptured code
  | none => false

#guard match bvlStage true
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some code => Flapjack.Test.BvlHandleCakeBviOracle.matchesCaptured code
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
  | some (_, _, _, code, _, _) => Flapjack.Test.FullBvlOptimizedCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

#guard match SourceToFlat.compileCakeToWord64OptimizedFuel 100 8 100 false
    SourceToFlat.emptyConfig { mtiConfig with doCall := true } wordConfig
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "f"))
      (.fn (ofString "x") (.fn (ofString "y") (.var (.short (ofString "x")))))] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullBvlOptimizedCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

end Flapjack.Test.ClosMtiParity
