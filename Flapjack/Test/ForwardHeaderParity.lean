import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap

/-! Replay the one-bit forwarding-header shift from
`word_gc_functions_probe.out`, through the actual heap assertion. -/
namespace Flapjack.Test.ForwardHeaderParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

example (conf : Config) :
    wordEl (0 : BitVec 1)
        (.forwardPointer 1 (.word (0 : BitVec 1)) 0) conf =
      SetSep.star (SetSep.one ((0 : BitVec 1), WordLocW.word (0 : BitVec 1)))
        (Misc.wordListExists (0 + StackRemove.bytesInWord 1) 0) := by
  simp [wordEl]

end Flapjack.Test.ForwardHeaderParity
