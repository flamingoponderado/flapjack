import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack.Compiler.Backend.DataToWord

/-- Original numeric heap-word limit. The HOL type dimension is observed only
through dimword and the wordLang shift overload (word_shift); arbitrary config
fields and both dimension branches are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def maxHeapLimit (width : Nat) [NeZero width] (config : Config) : Nat :=
  min ((2 ^ width) / (2 ^ shiftLength config))
    ((2 ^ width) / (2 ^ (Flapjack.wordShiftAmount width + 1)))

end Flapjack.Compiler.Backend.DataToWord
