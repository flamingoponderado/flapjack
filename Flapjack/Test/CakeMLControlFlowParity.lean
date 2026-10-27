import Flapjack.Compiler.Backend.ClosToBvl.Compile
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BviToData.Compile
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Test.EmptyCakeWordOracle
import Flapjack.Test.ReferenceCakeWordOracle
import Flapjack.Test.MatchCakeWordOracle
import Flapjack.Test.FixedStubsWordOracle
import Flapjack.Test.BignumWordOracle
import Flapjack.Test.FullCakeWordOracle

/-! A small cross-pass parity observation through word-language control flow. -/
namespace Flapjack.Test.CakeMLControlFlowParity

open Flapjack.Basis.Pure.MlString

private def config : Flapjack.Compiler.Backend.DataToWord.Config :=
  ⟨0, 0, 0, 4, false, false, false, false, false, false, .none⟩

#guard match Flapjack.Compiler.Backend.ClosToBvl.compileProg? 0 [(10, 1, .var .none 0)] with
  | some bvl => match Flapjack.Compiler.Backend.BvlToBvi.compileIncFuel 10 10 0 bvl with
    | some (0, [(loc, 1, exp)]) =>
        loc == Flapjack.bvlNumStubs + 48 &&
        match Flapjack.Compiler.Backend.BviToData.compileExpFuel 10 1 exp with
        | some data => match Flapjack.Compiler.Backend.DataToWord.compileControl? (width := 64) config loc 2 data with
          | some (.return 0 [2], 2) => true
          | _ => false
        | _ => false
    | _ => false
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.clos_to_word_control

#guard match Flapjack.Compiler.Backend.ClosToBvl.compileProg? 0
    [(10, 0, .op .none (.intOp (.const 3)) [])] with
  | some bvl => match Flapjack.Compiler.Backend.BvlToBvi.compileIncFuel 10 10 0 bvl with
    | some (0, [(loc, 0, exp)]) =>
        match Flapjack.Compiler.Backend.BviToData.compileExpFuel 10 0 exp with
        | some data => match Flapjack.Compiler.Backend.DataToWord.compileControl? (width := 64) config loc 2 data with
          | some (.seq (.assign 2 (.const 12)) (.return 0 [2]), 2) => true
          | _ => false
        | _ => false
    | _ => false
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.clos_to_bvi_constant &&
  Flapjack.Test.CakeMLFlatOracle.bvi_to_data_constant && Flapjack.Test.CakeMLFlatOracle.data_to_word_assign

private def fullWordConfig : Flapjack.Compiler.Backend.DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

private def noOptsConfig : Flapjack.Compiler.Backend.ClosToBvl.Config :=
  { Flapjack.Compiler.Backend.ClosToBvl.defaultConfig with
    maxApp := 0, doMti := false, doCall := false, knownConf := none }

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToWordWithLabelsNoOptsFuel (width := 64) 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig fullWordConfig [] with
  | some (_, _, _, code, _) => Flapjack.Test.EmptyCakeWordOracle.matchesCaptured code
  | none => false

private def compileWordFunctions? (decls : List Flapjack.AstHOL.Dec) :
    Option (List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) := do
  let (_, _, _, code, _) ← Flapjack.Compiler.Backend.SourceToFlat.compileCakeToWordWithLabelsNoOptsFuel
    100 Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig fullWordConfig decls
  pure code

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToWordNoOptsFuel (width := 64) 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig fullWordConfig [] with
  | some (_, _, 64, code, _) => code.map (fun (x : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64)) =>
      (x.1, x.2.1)) == [(62, 2), (63, 4), (64, 1), (65, 3), (66, 4), (67, 4), (68, 3),
        (69, 4), (72, 3), (76, 1), (80, 1), (84, 1), (73, 1), (88, 1)]
  | _ => false

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToWordWithStubs64NoOptsFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig fullWordConfig [] with
  | some (_, _, 64, code, _) =>
      let observe := fun (xs : List (Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64))) =>
        xs.map fun (loc, arity, body) => (loc, arity, body, 0)
      Flapjack.Test.FixedStubsWordOracle.matchesCaptured (observe (code.take 32)) &&
      Flapjack.Test.BignumWordOracle.matchesCaptured (observe ((code.drop 32).take 23)) &&
      (code.drop 55).map (fun (x : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64)) => (x.1, x.2.1)) ==
        [(62, 2), (63, 4), (64, 1), (65, 3), (66, 4), (67, 4), (68, 3),
         (69, 4), (72, 3), (76, 1), (80, 1), (84, 1), (73, 1), (88, 1)]
  | _ => false

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToWordWithStubs64NoOptsFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig fullWordConfig [] with
  | some (_, _, _, code, _) => Flapjack.Test.FullCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

#guard match compileWordFunctions?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.app .opref [.lit (.intLit 1)])] with
  | some code => Flapjack.Test.ReferenceCakeWordOracle.matchesCaptured code
  | none => false
#guard match compileWordFunctions?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.let_ (some (ofString "y")) (.app .opref [.lit (.intLit 1)]) (.var (.short (ofString "y"))))] with
  | some code => Flapjack.Test.ReferenceCakeWordOracle.matchesCaptured code
  | none => false
#guard match compileWordFunctions?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.app .opref [.mat (.lit (.intLit 1))
        [(.plit (.intLit 1), .lit (.intLit 2)), (.pany, .lit (.intLit 3))]])] with
  | some code => Flapjack.Test.MatchCakeWordOracle.matchesCaptured code
  | none => false

end Flapjack.Test.CakeMLControlFlowParity
