module

public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Std.Data.TreeMap

@[expose] public section

/-! Original key_load_* and key_heap_* observations at production callers.
These are routing correspondences, not a CSE simulation theorem. -/
namespace Flapjack.Test.WordCseProductionLoadHeapKeys
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordCseProductionLoadHeapKeys
