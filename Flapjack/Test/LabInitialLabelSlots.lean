import Flapjack.Compiler.Backend.StackToLab.RuntimeLabels
import Flapjack.Compiler.Encoders.RiscV.Target
import Flapjack.Compiler.Backend.RiscVConfig.Executable

namespace Flapjack.Test.LabInitialLabelSlots
open Flapjack Flapjack.RiscV

/-! Production regression for native sections, which have no synthetic entry
labels. HOL lab_to_targetScript enc_line_def initializes every Label with the
encoded Skip length, including labels among the first two lines. -/

/-! Relocation budget regression: a changing stored length must not be emitted
when no subsequent sweep can confirm convergence. Empty programs converge in
one sweep; an undersized plain instruction needs a second sweep. -/
private def relocationContext : WordFfiContext := { services := [] }
end Flapjack.Test.LabInitialLabelSlots
