import Flapjack.Compiler.Backend.BviInline
import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
import Flapjack.Test.CakeMLFlatOracle
import Flapjack.Test.InlineCakeBviOracle
import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Test.FullInlineCakeWordOracle

/-! Original wrapper-inlining and full-program observations. -/
namespace Flapjack.Test.BviInlineParity
open Flapjack Flapjack.Compiler.Backend

private def wrapper : Bvi.Exp :=
  .letCall 2 3 11 [.var 0, .var 1] (.op (.blockOp (.cons 7)) [.var 1, .var 0])

#guard BviInline.canonicalWrapper 10 2 wrapper
#guard !(BviInline.canonicalWrapper 11 2 wrapper)
#guard match BviInline.compileProgFuel 100 [(10, 2, wrapper), (12, 0, .call 5 (some 10) [.var 3, .var 4] none)] with
  | some (_, [(10, 2, .letCall 2 0 11 [.var 0, .var 1] (.op (.blockOp (.cons 7)) [.var 1, .var 0])),
      (12, 0, .let [.var 3, .var 4] (.letCall 2 0 11 [.var 0, .var 1] (.op (.blockOp (.cons 7)) [.var 1, .var 0])))]) => true
  | _ => false
#guard match BviInline.inlineExpFuel 100 (sptInsert 10 (2, wrapper) .ln)
    (.call 4 (some 10) [.var 3, .var 4] (some (.tick (.var 0)))) with
  | some (.call 4 (some 10) [.var 3, .var 4] (some (.tick (.var 0)))) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.bvi_inline_wrapper

private def noOpts : ClosToBvl.Config :=
  { ClosToBvl.defaultConfig with maxApp := 0, doMti := false, doCall := false, knownConf := none }
#guard match SourceToFlat.compileCakeToBviInlineFuel 100 SourceToFlat.emptyConfig noOpts [] with
  | some (_, _, _, code, _, _) => Flapjack.Test.InlineCakeBviOracle.matchesCaptured code
  | none => false

private def wordConfig : DataToWord.Config :=
  ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩
#guard match SourceToFlat.compileCakeToWordWithStubsAndNames64InlineFuel 100 SourceToFlat.emptyConfig noOpts wordConfig [] with
  | some (_, _, _, code, _, _) => Flapjack.Test.FullInlineCakeWordOracle.matchesCaptured
      (code.map fun (loc, arity, body) => (loc, arity, body, 0))
  | none => false

end Flapjack.Test.BviInlineParity
