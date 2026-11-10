module

public import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
public import Flapjack.Compiler.Backend.RegAlloc.ProductionBijection
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

@[expose] public section

namespace Flapjack.Test.WordAllocInstructionProducerParity
open Flapjack.WordAlloc Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-! Replay the four original HOL observations in
word_alloc_instruction_producer_probe.out and their executed producer results.
The literal catchall is preserved; these are not allocator-success claims. -/

end Flapjack.Test.WordAllocInstructionProducerParity
