import Flapjack.Compiler.Backend.WordAlloc.ProductionInstructionClashTree

namespace Flapjack.Test.WordAllocInstructionProducerParity
open Flapjack.WordAlloc Flapjack.RegAlloc Flapjack.Compiler.Encoders.Asm

/-! Replay the four original HOL observations in
word_alloc_instruction_producer_probe.out and their executed producer results.
The literal catchall is preserved; these are not allocator-success claims. -/

-- gdi_load16_zero=T
example :
    getDeltaInst (.mem .load16 1 (.addr 2 0) : HolInst 64) = .delta [] [] ∧
    wordClashTreeDeltaInst (.mem .load16 1 2 : WordInst (BitVec 64)) = .delta [] [] := by
  simp only [getDeltaInst, wordClashTreeDeltaInst, and_self]

-- gdi_store16_zero=T
example :
    getDeltaInst (.mem .store16 1 (.addr 2 0) : HolInst 64) = .delta [] [] ∧
    wordClashTreeDeltaInst (.mem .store16 1 2 : WordInst (BitVec 64)) = .delta [] [] := by
  simp only [getDeltaInst, wordClashTreeDeltaInst, and_self]

-- gdi_load16_offset=T
example :
    getDeltaInst (.mem .load16 1 (.addr 2 255) : HolInst 8) = .delta [] [] ∧
    wordClashTreeDeltaInst (.memOffset .load16 1 2 255 : WordInst (BitVec 8)) = .delta [] [] := by
  simp only [getDeltaInst, wordClashTreeDeltaInst, and_self]

-- gdi_store16_offset=T
example :
    getDeltaInst (.mem .store16 1 (.addr 2 255) : HolInst 8) = .delta [] [] ∧
    wordClashTreeDeltaInst (.memOffset .store16 1 2 255 : WordInst (BitVec 8)) = .delta [] [] := by
  simp only [getDeltaInst, wordClashTreeDeltaInst, and_self]

end Flapjack.Test.WordAllocInstructionProducerParity
