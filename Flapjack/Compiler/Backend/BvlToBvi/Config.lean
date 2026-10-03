import Flapjack.Compiler.Backend.Bvl.Syntax
import Flapjack.Compiler.Backend.Bvi.Syntax
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.BvlToBvi

/-- Complete source configuration. Both inline trees retain the distinct original
expression carriers and arities; HOL spt maps remain literal Spt trees.
The source initializer is separate and depends on backend_common's stub counts. -/
@[hol "cakeml/compiler/backend/bvl_to_bviScript.sml" "config"]
structure Config where
  inlineSizeLimit : Nat
  expCut : Nat
  splitMainAtSeq : Bool
  nextName1 : Nat
  nextName2 : Nat
  nextName3 : Nat
  doTailrec : Bool
  doTmc : Bool
  inlines : Spt (Nat × Bvl.Exp)
  bviInlines : Spt (Nat × Bvi.Exp)

end Flapjack.Compiler.Backend.BvlToBvi
