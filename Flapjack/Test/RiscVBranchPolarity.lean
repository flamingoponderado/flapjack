import Flapjack.RiscV.Lab
import Flapjack.RiscV.Encoding

/-! Fresh original riscv_ast/riscv_encode byte vectors from
scripts/hol-probes/riscv_jumpcmp_polarity_probe.out. These compare the actual
executed Lab emitter across all eight predicates, both operand forms and both
short/long ranges. Untagged regression infrastructure, not a HOL proof port. -/
namespace Flapjack.Test.RiscVBranchPolarity
open Flapjack Flapjack.RiscV
end Flapjack.Test.RiscVBranchPolarity
