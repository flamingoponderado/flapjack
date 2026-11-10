module

public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.Domain

@[expose] public section

/-! Same-input kernel replay of fresh original complete dead-code output trees. -/
namespace Flapjack.Test.WordToStackDeadCodecParity
open Flapjack Flapjack.RiscV

end Flapjack.Test.WordToStackDeadCodecParity
