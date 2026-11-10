module

public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap

@[expose] public section

/-! Source-shaped instruction-key observations at the actual CSE boundary.
Memory catch-all keys are distinct from load-fact keys. No simulation claim. -/
namespace Flapjack.Test.WordCseProductionInstructionKeys
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordCseProductionInstructionKeys
