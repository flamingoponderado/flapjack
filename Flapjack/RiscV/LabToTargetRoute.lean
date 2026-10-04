import Flapjack.RiscV.LabDiagnostics
import Flapjack.RiscV.InitializedRuntime
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

/-- Executed lab projection of the complete reviewed Pancake/RISC-V backend
configuration, including the original riscv_lab_conf quotation. No separate HOL
name; execution uses the checked whole-record realization. -/
def riscvLabConf : LabToTarget.Config :=
  RiscVConfig.pancakeRiscVBackendConfig.labConf

/-- Every previous lab field is retained by the native configuration adoption. -/
theorem riscvLabConf_defaults : riscvLabConf =
    { labels := .ln, secPosLen := [], pos := 0, initClock := 5, ffiNames := none,
      shmemExtra := [], hashSize := 104729 } := rfl

/-- Split the reviewed `lab_to_target` byte image into the sections recorded by
its `sec_pos_len` (Flapjack output adapter; no HOL original). -/
def sectionsOfSymbols {width : Nat} [NeZero width] (bytes : List (BitVec 8)) :
    List (Nat × Nat × Nat) → List (EncodedRiscVSection width)
  | [] => []
  | (label, position, length) :: rest =>
      { label, address := BitVec.ofNat width position,
        bytes := (bytes.drop position).take length } :: sectionsOfSymbols bytes rest

/-- RV64 Lab-to-target through the reviewed `LabToTarget.compile` with the
native `riscv_config` and `riscv_lab_conf`; returns the reviewed byte image and
configuration. Codec failure and HOL's `NONE` are both `none`. -/
def labToTargetRiscV (program : LabProgram (Word 64)) :
    Option (List (BitVec 8) × LabToTarget.Config) := do
  let native ← StackToLab.ExecutedCodec.programFromExecuted? program
  LabToTarget.compile Compiler.Encoders.RiscV.Target.riscvConfig riscvLabConf native

/-- Executed stack projection of the complete reviewed Pancake/RISC-V backend
configuration, including the original riscv_stack_conf quotation. No separate
HOL name. Dynamic arguments of runtime initialization remain explicit. -/
def riscvStackConf : StackToLab.Config :=
  RiscVConfig.pancakeRiscVBackendConfig.stackConf

/-- Every previous stack field is retained by the native configuration adoption. -/
theorem riscvStackConf_defaults : riscvStackConf =
    { regNames := RiscVConfig.riscvNames, jump := false, perfCalls := false } := rfl

/-- RV64 Stack-to-target through the reviewed passes: the native Stack sections
(Word-to-Stack bodies with the native Raise/StoreConsts stubs, as
`initializedRuntimeLab?`) are compiled by the reviewed `stack_to_lab$compile`
with `riscv_stack_conf`, the Pancake data configuration and exactly the heap,
stack-pointer and address-offset arguments of `from_stack`, then by
`lab_to_target$compile` with `riscv_lab_conf`. This is the body of the reviewed
`Backend.fromStack` before bitmap attachment (see `stackToRiscV_fromStack`). -/
def stackToRiscV (registerCount : Nat) (programs : List (Nat × StackProg Nat)) :
    Option (List (BitVec 8) × LabToTarget.Config) := do
  let native ← StackToLab.InitializedProduction.nativeInputs? (width := 64) programs
  let source := StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3))
  let support :=
    [(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
     (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)]
  let asmConf := Compiler.Encoders.RiscV.Target.riscvConfig
  LabToTarget.compile asmConf riscvLabConf
    (StackToLab.compile riscvStackConf initializedRuntimeDataConfig
      (2 * DataToWord.maxHeapLimit 64 initializedRuntimeDataConfig - 1)
      (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset (support ++ source))

/-- The executed RV64 bytes are the bytes of the reviewed `from_stack` for every
backend configuration whose stack, data and lab components are the RISC-V/Pancake
ones used here (Flapjack routing fact; no HOL original). -/
theorem stackToRiscV_fromStack (config : Backend.Config) (names : Spt Basis.Pure.MlString.MlString)
    {Bitmaps : Type} (bitmaps : Bitmaps)
    (hStack : config.stackConf = riscvStackConf)
    (hData : config.dataConf = initializedRuntimeDataConfig)
    (hLab : config.labConf = riscvLabConf)
    (registerCount : Nat) (programs : List (Nat × StackProg Nat))
    (native : List (Nat × StackLang.HolProg 64))
    (hNative : StackToLab.InitializedProduction.nativeInputs? (width := 64) programs = some native) :
    (stackToRiscV registerCount programs).map Prod.fst =
      (Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig config names
        ([(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
          (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)] ++
          StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3)))
        bitmaps).map Prod.fst := by
  simp only [stackToRiscV, hNative, Option.bind_eq_bind, Option.bind_some, Backend.fromStack,
    Backend.fromLab, hStack, hData, hLab]
  generalize LabToTarget.compile (width := 64) _ _ _ = out
  rcases out with _ | ⟨bytes, lab⟩ <;> rfl

/-- The actual RV64 route uses the full reviewed Pancake backend constant.
No field-match or successful-codec premise is needed: failed native input decoding
is retained as none on both sides. This is Flapjack routing infrastructure, not
an upstream compiler simulation theorem. -/
theorem stackToRiscV_pancakeBackendConfig (names : Spt Basis.Pure.MlString.MlString)
    {Bitmaps : Type} (bitmaps : Bitmaps)
    (registerCount : Nat) (programs : List (Nat × StackProg Nat)) :
    (stackToRiscV registerCount programs).map Prod.fst =
      (StackToLab.InitializedProduction.nativeInputs? (width := 64) programs).bind
        (fun native =>
          (Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
            (Compiler.pancakeBackendConf RiscVConfig.riscvBackendConfig) names
            ([(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
              (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)] ++
              StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3)))
            bitmaps).map Prod.fst) := by
  cases hNative : StackToLab.InitializedProduction.nativeInputs? (width := 64) programs with
  | none => simp [stackToRiscV, hNative]
  | some native =>
      simp only [Option.bind_some]
      exact stackToRiscV_fromStack
        (Compiler.pancakeBackendConf RiscVConfig.riscvBackendConfig) names bitmaps
        rfl rfl rfl registerCount programs native hNative

/-- Executed sections of a Lab program: at width 64 the reviewed
`labToTargetRiscV` image split by its `sec_pos_len`; at other widths the
existing stored-length linker and instruction encoder. -/
def labProgramToRiscVSections {width : Nat} [NeZero width] (context : WordFfiContext)
    (program : LabProgram (Word width)) : Option (List (EncodedRiscVSection width)) :=
  if h : width = 64 then by
    subst h
    exact (labToTargetRiscV program).map fun (bytes, config) =>
      sectionsOfSymbols bytes config.secPosLen
  else
    (compileLabProgramLinkedWithNativeInitialization context program).map encodeLinkedSections

/-- At width 64 the executed bytes are exactly the reviewed
`lab_to_target$compile` image (Flapjack routing fact; no HOL original). -/
theorem labProgramToRiscVSections_rv64 (context : WordFfiContext)
    (program : LabProgram (Word 64)) :
    labProgramToRiscVSections context program =
      (labToTargetRiscV program).map fun (bytes, config) =>
        sectionsOfSymbols bytes config.secPosLen := by
  simp [labProgramToRiscVSections]

/-- Frame metadata must use the same ordered byte names as the final native
code. This production boundary check has no separate HOL declaration. -/
def frameFfiNamesAgree (config : LabToTarget.Config) (names : List String) : Bool :=
  match config.ffiNames with
  | none => false
  | some actual =>
      actual.take names.length ==
        names.map (fun name => HolFfiName.extCall (Basis.Pure.MlString.ofString name)) &&
      (actual.drop names.length).all (fun name => match name with
        | .sharedMem _ => true
        | .extCall _ => false)

/-- Executed Stack-to-RISC-V sections. At width 64 the reviewed
`stackToRiscV` (the `from_stack` body: `stack_to_lab$compile` then
`lab_to_target$compile`) is split by its `sec_pos_len`; other widths keep the
native Stack-to-Lab composition of `initializedRuntimeLab?` and the existing
linker. Arguments and error behaviour match
`compileStackProgramNatListLinkedWithSimpleGcAndStoreConstsToRiscVCakeChecked`. -/
def compileStackProgramNatListToRiscVSectionsCakeChecked
    [NeZero width] (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (_allocConfig : StackAllocConfig) (_gcConfig : StackGcConfig)
    (_storeConstsLocation registerCount : Nat)
    (entryLabel _initialLabel : Nat)
    (programs : List (Nat × StackProg Nat))
    (expectedFfiNames : Option (List String) := none) :
    Except LabLoweringError (List (EncodedRiscVSection width)) :=
  if entryLabel ≠ 0 || removeConfig.bytesInWord ≠ width / 8 then
    .error { sectionId := 0, position := 0, feature := .loweringFailure }
  else if h : width = 64 then by
    subst h
    exact match stackToRiscV registerCount programs with
      | some (bytes, config) =>
          if expectedFfiNames.all (frameFfiNamesAgree config) then
            .ok (sectionsOfSymbols bytes config.secPosLen)
          else .error { sectionId := 0, position := 0, feature := .loweringFailure }
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
  else
    let removeConfig := cakeStackRemoveConfig removeConfig
    let bounds := (BitVec.ofInt width (-2048), BitVec.ofNat width 2047)
    match initializedRuntimeLab? removeConfig.jump bounds
        removeConfig.stackPointer stackFunctionFirstLabel registerCount programs with
    | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
    | some lab => match labProgramToRiscVSections context lab with
      | some sections => .ok sections
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }

end Flapjack.RiscV
