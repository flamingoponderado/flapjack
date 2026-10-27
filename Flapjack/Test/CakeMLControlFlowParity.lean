import Flapjack.Compiler.Backend.ClosToBvl.Compile
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BviToData.Compile
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Compiler.Backend.SourceToFlat.ToData
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Test.EmptyCakeWordOracle
import Flapjack.Test.ReferenceCakeWordOracle
import Flapjack.Test.MatchCakeWordOracle

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

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToDataNoOptsFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig [] with
  | some (_, _, _, code, _) =>
      let entry := code.filter fun (x : Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog) =>
        [64, 76, 80, 84, 73, 88].contains x.1
      match entry.mapM fun (x : Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog) => do
        let word ← Flapjack.Compiler.Backend.DataToWord.compileControl? (width := 64) fullWordConfig x.1 2 x.2.2
        pure (x.1, x.2.1, word) with
      | some word => Flapjack.Test.EmptyCakeWordOracle.matchesCaptured word
      | none => false
  | none => false

private def compileFunction92? (decls : List Flapjack.AstHOL.Dec) :
    Option (List (Nat × Nat × (Flapjack.WordLangProgHOL (BitVec 64) × Nat))) := do
  let (_, _, _, code, _) ← Flapjack.Compiler.Backend.SourceToFlat.compileCakeToDataNoOptsFuel 100
    Flapjack.Compiler.Backend.SourceToFlat.emptyConfig noOptsConfig decls
  let selected := code.filter fun (x : Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog) => x.1 == 92
  selected.mapM fun (x : Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog) => do
    let word ← Flapjack.Compiler.Backend.DataToWord.compileControl? (width := 64) fullWordConfig x.1 2 x.2.2
    pure (x.1, x.2.1, word)

#guard match compileFunction92?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x")) (.app .opref [.lit (.intLit 1)])] with
  | some code => Flapjack.Test.ReferenceCakeWordOracle.matchesCaptured code
  | none => false
#guard match compileFunction92?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.let_ (some (ofString "y")) (.app .opref [.lit (.intLit 1)]) (.var (.short (ofString "y"))))] with
  | some code => Flapjack.Test.ReferenceCakeWordOracle.matchesCaptured code
  | none => false
#guard match compileFunction92?
    [.dlet Flapjack.Misc.Location.unknownLoc (.pvar (ofString "x"))
      (.app .opref [.mat (.lit (.intLit 1))
        [(.plit (.intLit 1), .lit (.intLit 2)), (.pany, .lit (.intLit 3))]])] with
  | some code => Flapjack.Test.MatchCakeWordOracle.matchesCaptured code
  | none => false

end Flapjack.Test.CakeMLControlFlowParity
