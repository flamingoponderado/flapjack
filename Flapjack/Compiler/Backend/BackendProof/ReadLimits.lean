import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Backend.Semantics.TargetSem.State
import Flapjack.Compiler.Backend.StackNames.OperandNames
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit

/-! backendProofScript.sml: `read_limits_def`, the stack/heap limits read from the
initial machine state, used in the conclusion of the Pancake top-level theorem. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackNames

/-- Exact HOL `backendProof$read_limits_def` (`backendProofScript.sml:2871-2878`):
`get_stack_heap_limit (2 * max_heap_limit (:'a) c.data_conf - 1)` of the three
registers named 2, 3, 4. HOL's `asm_conf` argument is not used by the body and is
retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def readLimits {width : Nat} [NeZero width] {state projection : Type}
    (_asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (mc : MachineConfig width state projection) (ms : state) : Nat × Nat :=
  StackRemove.Proofs.InitLimits.getStackHeapLimit
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.getReg ms (findNameSpt c.stackConf.regNames 2),
     mc.target.getReg ms (findNameSpt c.stackConf.regNames 3),
     mc.target.getReg ms (findNameSpt c.stackConf.regNames 4))

end Flapjack.Compiler.Backend.BackendProof
