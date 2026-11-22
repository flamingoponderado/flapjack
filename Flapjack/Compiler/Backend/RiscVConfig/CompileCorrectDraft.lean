import Flapjack.Compiler.Backend.BackendProof.CompileCorrectDraft
import Flapjack.Compiler.Backend.RiscVConfig.Proofs

set_option autoImplicit false

/-! Draft (untagged) of HOL `riscv_compile_correct`
(`riscv_configProofScript.sml:79-86`): `compile_correct` instantiated at
`riscv_config`, `riscv_backend_config` and an `is_riscv_machine_config` machine,
with `backend_config_ok`, `mc_conf_ok` and `mc_init_ok` discharged by
`riscv_backend_config_ok`, `riscv_machine_config_ok` and `riscv_init_ok`, and
`heap_regs riscv_backend_config.stack_conf.reg_names` evaluated to `(11,13)`.

HOL's theorem is produced by `SIMP_RULE`, so its exact printed shape still has
to be captured from HOL before tagging. It is derived here from the
`compile_correct` statement, which is itself taken as a hypothesis until
`compile_correct'` is proved. -/
namespace Flapjack.Compiler.Backend.RiscVConfig.Draft

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.BackendProof.Draft
open Flapjack.SemanticsHOL Flapjack.SemanticPrimitivesHOL Flapjack.PrimTypesHOL
open Flapjack.SemanticsPropsHOL Flapjack.Compiler.Encoders.RiscV.Target

/-- `heap_regs riscv_backend_config.stack_conf.reg_names = (11,13)`, the `EVAL`
step of HOL's derivation. -/
theorem heapRegs_riscvBackendConfig :
    heapRegs riscvBackendConfig.stackConf.regNames = (11, 13) := by
  have hnames : riscvBackendConfig.stackConf.regNames = riscvNames := rfl
  simp only [heapRegs, hnames, StackNames.findNameSpt, riscvNames_lookup_eq]
  decide

/-- The statement of HOL `riscv_compile_correct` for fixed free variables. -/
noncomputable def riscvCompileCorrectStmt {F : Type} [Nonempty F]
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (cbspace dataSp : Nat)
    (ms : RiscV.L3.riscv_state) : Prop :=
  isRiscvMachineConfig mc →
  BackendDefs.compile riscvConfig riscvBackendConfig prog = some (bytes, bitmaps, c') →
    match holThe (primSemEnv ffi) with
    | (s, env) =>
      ¬ semanticsProg s env prog .fail ∧
          installed bytes cbspace bitmaps dataSp c'.labConf.ffiNames (11, 13) mc
            c'.labConf.shmemExtra ms →
        ∀ b, machineSemHOL mc ffi ms b → extendWithResourceLimitHOL (semanticsProg s env prog) b

/-- HOL `riscv_compile_correct`, from the RISC-V instance of `compile_correct`. -/
theorem riscvCompileCorrect_of_compileCorrect {F : Type} [Nonempty F]
    (prog : List AstHOL.Dec) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Flapjack.Compiler.Backend.Backend.Config) (ffi : HolFfiState F)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection) (cbspace dataSp : Nat)
    (ms : RiscV.L3.riscv_state)
    (hcc : compileCorrectStmt riscvConfig riscvBackendConfig prog bytes bitmaps c' ffi mc
      cbspace dataSp ms) :
    riscvCompileCorrectStmt prog bytes bitmaps c' ffi mc cbspace dataSp ms := by
  intro hmc hcomp
  have h := hcc hcomp
  revert h
  rw [heapRegs_riscvBackendConfig]
  rcases holThe (primSemEnv ffi) with ⟨s, env⟩
  intro h ⟨hfail, hinst⟩
  exact h ⟨hfail, riscvBackendConfigOk, riscvMachineConfigOk mc hmc, riscvInitOk mc hmc, hinst⟩

end Flapjack.Compiler.Backend.RiscVConfig.Draft
