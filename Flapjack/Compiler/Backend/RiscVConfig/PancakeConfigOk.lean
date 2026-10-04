import Flapjack.Compiler.Compiler
import Flapjack.Compiler.Backend.RiscVConfig.Proofs

/-!
# `backend_config_ok` for the executed Pancake RISC-V configuration

Pancake's driver (`compilerScript.sml:744-747`, `compile_pancake_64`) compiles with
`pancake_backend_conf riscv_backend_config`, i.e. `riscv_backend_config` with
`data_conf.gc_kind := None`, whereas HOL's `riscv_backend_config_ok`
(`riscv_configProofScript.sml:27-52`) is stated for `riscv_backend_config` itself. HOL has
no theorem for the modified record, so the results here are Flapjack-specific and carry
no `@[hol]` tag. They are derived from the original `backend_config_ok_def`
(`backendProofScript.sml`): no conjunct of that definition reads `data_conf.gc_kind`
(`conf_ok` and `max_heap_limit` use only the tag/length/padding sizes), so the predicate
is unchanged by `pancake_backend_conf`.
-/

namespace Flapjack.Compiler.Backend.RiscVConfig

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.RiscV.Target

/-- `backend_config_ok` does not depend on `data_conf.gc_kind`, so it holds of
`pancake_backend_conf c` exactly when it holds of `c` (Flapjack-specific; no HOL original). -/
theorem backendConfigOk_pancakeBackendConf_iff {width : Nat} [NeZero width]
    (asmConf : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (c : Backend.Config) :
    backendConfigOk asmConf (Flapjack.Compiler.pancakeBackendConf c) ↔
      backendConfigOk asmConf c :=
  Iff.rfl

/-- `backend_config_ok riscv_config (pancake_backend_conf riscv_backend_config)`: the
configuration check for the GC-free configuration that Pancake actually compiles with,
from the tagged port of HOL `riscv_backend_config_ok` (Flapjack-specific; no HOL
original). -/
theorem riscvPancakeBackendConfigOk :
    backendConfigOk riscvConfig (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig) :=
  (backendConfigOk_pancakeBackendConf_iff riscvConfig riscvBackendConfig).2 riscvBackendConfigOk

/-- The configuration Pancake compiles with is the GC-free one (sanity check). -/
theorem riscvPancakeBackendConfig_gcKind :
    (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).dataConf.gcKind = .none :=
  rfl

end Flapjack.Compiler.Backend.RiscVConfig
