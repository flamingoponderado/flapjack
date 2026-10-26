import Flapjack.Compiler.Backend.ClosToBvl.Compile
import Flapjack.Compiler.Backend.BvlToBvi.Compile
import Flapjack.Compiler.Backend.BviToData.Compile
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Test.CakeMLFlatOracle

/-! A small cross-pass parity observation through word-language control flow. -/
namespace Flapjack.Test.CakeMLControlFlowParity

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

end Flapjack.Test.CakeMLControlFlowParity
