module

public import Flapjack.RiscV.WordToStack
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap
public import Flapjack.RiscV.Backend
public import Flapjack.RiscV.Encoding

@[expose] public section

/-! Matching executed observations of the original overflow constructors.
The full original HOL results live in word_overflow_production_probe.out.
These are carrier/consumer fixtures, not a full pass simulation theorem. -/
namespace Flapjack.Test.WordOverflowProduction
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordOverflowProduction
