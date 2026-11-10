module

public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordToStackRegFormat
public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

namespace Flapjack.Test.ProductionLocations
open Flapjack RiscV RiscV.CakeRegAlloc

/-! Kernel fixtures for actual operand locations. No HOL simulation or
executed lowering equivalence is asserted by these tests. -/
end Flapjack.Test.ProductionLocations
