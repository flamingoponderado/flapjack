import Flapjack.RiscV.LabToTargetRoute

namespace Flapjack.RiscV
open Flapjack.Compiler.Backend

/-- Flapjack production composition, with no independent HOL declaration.
The actual native-input rejection branch remains inside the option bind.
The complete backend output retains bytes, arbitrary bitmap payload, updated
laboratory configuration and original symbol attachment, not just byte projection. -/
theorem stackToRiscV_fullBackendOutput (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString) {Bitmaps : Type} (bitmaps : Bitmaps)
    (hStack : config.stackConf = riscvStackConf)
    (hData : config.dataConf = initializedRuntimeDataConfig)
    (hLab : config.labConf = riscvLabConf)
    (registerCount : Nat) (programs : List (Nat × StackProg Nat)) :
    Backend.attachBitmaps names config bitmaps (stackToRiscV registerCount programs) =
      ((StackToLab.InitializedProduction.nativeInputs? (width := 64) programs).bind
        fun native => Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
          config names
          ([(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
            (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)] ++
            StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3)))
          bitmaps) := by
  unfold stackToRiscV
  cases hn : StackToLab.InitializedProduction.nativeInputs? (width := 64) programs with
  | none => rfl
  | some native =>
    simp only [Option.bind_eq_bind, Option.bind_some, Backend.fromStack, Backend.fromLab,
      hStack, hData, hLab]


/-- Flapjack-specific actual checked section adapter composition. No independent
HOL theorem: the full original backend output is routed through the executed
section/FFI guard adapter. Native input and compiler rejection remain observable,
and no accepted-input, successful compilation or desired-output premise is used. -/
theorem checkedSections_fullBackendOutput (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString) {Bitmaps : Type} (bitmaps : Bitmaps)
    (hStack : config.stackConf = riscvStackConf)
    (hData : config.dataConf = initializedRuntimeDataConfig)
    (hLab : config.labConf = riscvLabConf)
    (context : WordFfiContext) (removeConfig : StackRemoveConfig)
    (allocConfig : StackAllocConfig) (gcConfig : StackGcConfig)
    (storeLocation registerCount entryLabel initialLabel : Nat)
    (programs : List (Nat × StackProg Nat)) (expectedFfiNames : Option (List String)) :
    compileStackProgramNatListToRiscVSectionsCakeChecked (width := 64)
      context removeConfig allocConfig gcConfig storeLocation registerCount
      entryLabel initialLabel programs expectedFfiNames =
    if entryLabel ≠ 0 || removeConfig.bytesInWord ≠ 64 / 8 then
      .error { sectionId := 0, position := 0, feature := .loweringFailure }
    else
      match (StackToLab.InitializedProduction.nativeInputs? (width := 64) programs).bind
        (fun native => Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
          config names
          ([(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
            (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)] ++
            StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3)))
          bitmaps) with
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
      | some (bytes, _, updated) =>
          if expectedFfiNames.all (frameFfiNamesAgree updated.labConf) then
            .ok (sectionsOfSymbols bytes updated.labConf.secPosLen)
          else .error { sectionId := 0, position := 0, feature := .loweringFailure } := by
  rw [← stackToRiscV_fullBackendOutput config names bitmaps hStack hData hLab]
  unfold compileStackProgramNatListToRiscVSectionsCakeChecked
  simp only [dite_true]
  cases ho : stackToRiscV registerCount programs with
  | none => simp [Backend.attachBitmaps]
  | some output =>
    rcases output with ⟨bytes, lab⟩
    simp [Backend.attachBitmaps]

/-- Proof-side final output adapter using the original full backend tuple.
No HOL original; this exposes the actual failure and section projection boundary. -/
def runtimeSectionsFromBackend (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString) {Bitmaps : Type} (bitmaps : Bitmaps)
    (removeConfig : StackRemoveConfig) (registerCount entryLabel : Nat)
    (programs : List (Nat × StackProg Nat)) (expectedFfiNames : Option (List String)) :
    Except LabLoweringError (List (EncodedRiscVSection 64)) :=
    if entryLabel ≠ 0 || removeConfig.bytesInWord ≠ 64 / 8 then
      .error { sectionId := 0, position := 0, feature := .loweringFailure }
    else
      match (StackToLab.InitializedProduction.nativeInputs? (width := 64) programs).bind
        (fun native => Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
          config names
          ([(Flapjack.raiseStubLocation, WordToStack.Native.raiseStubNative false registerCount),
            (Flapjack.storeConstsStubLocation, WordToStack.Native.storeConstsStubNative registerCount)] ++
            StackToLab.RuntimeLabels.originalInputs (native.filter (fun entry => entry.1 >= 3)))
          bitmaps) with
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure }
      | some (bytes, _, updated) =>
          if expectedFfiNames.all (frameFfiNamesAgree updated.labConf) then
            .ok (sectionsOfSymbols bytes updated.labConf.secPosLen)
          else .error { sectionId := 0, position := 0, feature := .loweringFailure }

/-- Local adapter identity retaining both compiler and FFI-guard rejection.
Flapjack infrastructure; no independent HOL declaration. -/
theorem runtimeSectionsFromBackend_actual (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString) {Bitmaps : Type} (bitmaps : Bitmaps)
    (hStack : config.stackConf = riscvStackConf)
    (hData : config.dataConf = initializedRuntimeDataConfig)
    (hLab : config.labConf = riscvLabConf)
    (removeConfig : StackRemoveConfig) (registerCount entryLabel : Nat)
    (programs : List (Nat × StackProg Nat)) (expectedFfiNames : Option (List String)) :
    runtimeSectionsFromBackend config names bitmaps removeConfig registerCount entryLabel
      programs expectedFfiNames =
    if entryLabel ≠ 0 || removeConfig.bytesInWord ≠ 64 / 8 then
      .error { sectionId := 0, position := 0, feature := .loweringFailure }
    else match stackToRiscV registerCount programs with
      | some (bytes, lab) =>
          if expectedFfiNames.all (frameFfiNamesAgree lab) then
            .ok (sectionsOfSymbols bytes lab.secPosLen)
          else .error { sectionId := 0, position := 0, feature := .loweringFailure }
      | none => .error { sectionId := 0, position := 0, feature := .loweringFailure } := by
  unfold runtimeSectionsFromBackend
  rw [← stackToRiscV_fullBackendOutput config names bitmaps hStack hData hLab]
  cases ho : stackToRiscV registerCount programs with
  | none => simp [Backend.attachBitmaps]
  | some output => rcases output with ⟨bytes, lab⟩; simp [Backend.attachBitmaps]

end Flapjack.RiscV
