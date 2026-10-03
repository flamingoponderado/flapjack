import Flapjack.Compiler.Backend.WordAlloc.ClashTreeProg
import Flapjack.Compiler.Backend.RegAlloc.ProductionBijection
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

namespace Flapjack.WordAlloc

/-! Executed/native producer correspondence, without independent HOL originals.
The encoder preserves buffer operands; the literal source read order is value
then address. This order also affects the allocator's produced name numbering,
so membership equality alone would not establish the producer equation. -/

theorem codeBufferClashTree_production {width : Nat} [NeZero width]
    (address value : Nat) (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative
      (Flapjack.wordClashTree (.codeBufferWrite address value : WordProg (BitVec width)) context) =
      getClashTree (.codeBufferWrite address value : WordLangProgHOL (BitVec width))
        (context.map (fun pair => wordCutsetsToHOL pair)) := by
  simp only [Flapjack.wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree]

theorem dataBufferClashTree_production {width : Nat} [NeZero width]
    (address value : Nat) (context : List (List Nat × List Nat)) :
    RegAlloc.productionClashTreeToNative
      (Flapjack.wordClashTree (.dataBufferWrite address value : WordProg (BitVec width)) context) =
      getClashTree (.dataBufferWrite address value : WordLangProgHOL (BitVec width))
        (context.map (fun pair => wordCutsetsToHOL pair)) := by
  simp only [Flapjack.wordClashTree, RegAlloc.productionClashTreeToNative, getClashTree]

end Flapjack.WordAlloc
