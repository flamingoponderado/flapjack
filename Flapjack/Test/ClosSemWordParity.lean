import Flapjack.Compiler.Backend.Semantics.ClosSem.Word

/-! Concrete closure-word edge cases. The Boolean comparison observations
are captured in `scripts/hol-probes/clos_sem_word_probe.out`; byte arithmetic
and conversion examples also exercise the Lean implementation where HOL's
choice expressions remain unreduced in that capture. -/
namespace Flapjack.Test.ClosSemWordParity
open Flapjack.Compiler.Backend.ClosSem

example : doWordAppIntegral (.wordOpw .w8 .add) [.number 255, .number 2] = some (.number 1) := rfl
example : doWordAppIntegral (.wordOpw .w8 .add) [.number (-1), .number 2] = none := rfl
example : doWordAppIntegral (.wordFromWord false) [.number 256] = none := rfl
example : doWordAppIntegral (.wordShift .w8 .asr 7) [.number 128] = some (.number 255) := rfl
example : doWordAppIntegral .wordFromInt [.number (-1)] = some (.word64 (BitVec.ofInt 64 (-1))) := rfl
example : doWordAppIntegral (.wordFromWord true) [.word64 (BitVec.ofNat 64 511)] = some (.number 255) := rfl
example : doWordAppIntegral (.wordTest .w8 (.compare .lt)) [.number 127, .number 128] =
    some (.block 1 []) := rfl
example : doWordAppIntegral (.wordTest .w8 (.altCompare .lt)) [.number 1, .number 2] = none := rfl
example : doWordAppIntegral (.wordOpw .w64 .add) [.word64 5, .word64 9] = some (.word64 14) := rfl
example : doWordAppIntegral (.wordShift .w64 .lsl 3) [.word64 7] = some (.word64 56) := rfl

end Flapjack.Test.ClosSemWordParity
