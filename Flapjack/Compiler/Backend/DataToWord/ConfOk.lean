import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.BackendCommon

namespace Flapjack.Compiler.Backend.DataToWord

/-- Exact HOL `conf_ok_def` (`data_to_wordScript.sml:109-114`): the shift length
fits below the word width and covers the word shift, and the length field is
nonzero and leaves room for a tag byte. The HOL type dimension is observed only
through `dimindex` and the wordLang `shift` overload (`word_shift`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def confOk (width : Nat) [NeZero width] (c : Config) : Prop :=
  shiftLength c < width ∧ Flapjack.wordShiftAmount width ≤ shiftLength c ∧
    c.lenSize ≠ 0 ∧ c.lenSize + 7 < width

end Flapjack.Compiler.Backend.DataToWord
