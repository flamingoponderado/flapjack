import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.Encoding
import Flapjack.Compiler.Backend.LabToTarget.Compile
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.Backend

/-!
# Executed Lab-to-target route through the reviewed `lab_to_target$compile`

The executed RV64 image is produced by the reviewed
`LabToTarget.compile` (`lab_to_target$compile_def`: `filter_skip`,
`remove_labels`, `prog_to_bytes`, `get_shmem_info` and the configuration
update) with the exact native `riscv_config` and the original
`riscv_lab_conf`. The executed Lab program is decoded to the native section
carrier by the existing `ExecutedCodec.programFromExecuted?`; a codec failure is
a lowering failure. The output sections are the byte ranges recorded by the
original `sec_pos_len` (`get_symbols`) of the returned configuration.

Other word widths keep the existing stored-length linker, for which no native
`riscv_config` exists.
-/

namespace Flapjack.RiscV

open Flapjack.Compiler.Backend

/-- Split the reviewed `lab_to_target` byte image into the sections recorded by
its `sec_pos_len` (Flapjack output adapter; no HOL original). -/
def sectionsOfSymbols {width : Nat} [NeZero width] (bytes : List (BitVec 8)) :
    List (Nat × Nat × Nat) → List (EncodedRiscVSection width)
  | [] => []
  | (label, position, length) :: rest =>
      { label, address := BitVec.ofNat width position,
        bytes := (bytes.drop position).take length } :: sectionsOfSymbols bytes rest

end Flapjack.RiscV
