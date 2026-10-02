import Flapjack.Compiler.Backend.DataToWord.Config

/-!
# `data_to_word` configuration helpers: original-oracle rows

Kernel replay of the six rows of `scripts/hol-probes/data_to_word_config_probe.out`.
-/

namespace Flapjack.Test.DataToWordConfigParity

open Flapjack.Compiler.Backend.DataToWord

private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, hasFpOps := false, hasFpTern := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

-- shift_length=8
example : shiftLength conf = 8 := rfl
-- small_shift_length=4
example : smallShiftLength conf = 4 := rfl
-- gen_size_nil_64=0xFFFFFFFFFFFFFFF8w
example : (getGenSize [] : BitVec 64) = 0xFFFFFFFFFFFFFFF8 := by decide
-- gen_size_ten_64=80w
example : (getGenSize [10, 20] : BitVec 64) = 80 := by decide
-- gen_size_overflow_64=0xFFFFFFFFFFFFFFF8w
example : (getGenSize [2305843009213693952] : BitVec 64) = 0xFFFFFFFFFFFFFFF8 := by decide
-- gen_size_three_32=12w
example : (getGenSize [3] : BitVec 32) = 12 := by decide

def runChecks : IO Bool := do
  IO.println "PASS data_to_word shift_length/small_shift_length/get_gen_size match six original HOL rows"
  pure true

end Flapjack.Test.DataToWordConfigParity
