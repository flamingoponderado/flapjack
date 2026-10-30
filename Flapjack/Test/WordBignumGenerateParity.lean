import Flapjack.Compiler.Backend.WordBignum.Generate
import Flapjack.Test.BignumWordOracle

/-! Compare every generated 64-bit stub with the pinned HOL compiler output. -/
namespace Flapjack.Test.WordBignumGenerateParity
open Flapjack.Compiler.Backend.WordBignum

def matchesOriginal : Bool :=
  match generateStubs 64 39 with
  | none => false
  | some entries => BignumWordOracle.matchesCaptured
      (entries.map fun (location, arity, code) => (location, arity, code, 0))

#guard matchesOriginal

end Flapjack.Test.WordBignumGenerateParity
