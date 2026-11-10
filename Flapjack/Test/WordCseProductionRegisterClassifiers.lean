module

public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap

@[expose] public section

/-! Original register-classifier observations at executed CSE callers.
Overflow observations are extended in WordOverflowProduction; FP remains
on the full carrier frontier. -/
namespace Flapjack.Test.WordCseProductionRegisterClassifiers
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordCseProductionRegisterClassifiers
