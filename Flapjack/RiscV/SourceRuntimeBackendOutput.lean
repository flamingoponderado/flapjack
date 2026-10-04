import Flapjack.RiscV.RuntimeImageBackendOutput
import Flapjack.RiscV.PipelineDiagnostics

namespace Flapjack
open Compiler.Backend
-- Compare the original width-polymorphic generated matchers with the concrete
-- RV64 matchers directly, including the dependent parser equality binder.
set_option smartUnfolding false in
/-- Actual RV64 source runtime-image equation through the complete original
backend result. This Flapjack routing theorem has no independent HOL original.
Every actual frontend/allocation/codec/compiler/FFI error remains in the RHS;
there is no successful-pass or accepted-input assumption. -/
theorem sourceRuntimeImage_fullBackendOutput (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString)
    (hStack : config.stackConf = RiscV.riscvStackConf)
    (hData : config.dataConf = RiscV.initializedRuntimeDataConfig)
    (hLab : config.labConf = RiscV.riscvLabConf)
    (architecture : RiscV.Architecture) (bytesInWord : RiscV.Word 64)
    (fromNat : Int → RiscV.Word 64) (services : List (FunName × Nat))
    (removeConfig : StackRemoveConfig) (start : FunName) (source : String) :
    compileFlapjackRiscVSourceRuntimeImageChecked architecture bytesInWord
      fromNat services removeConfig start source =
  match hparse : Parser.parseTopDecs fromNat source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let warnings := checked.2
          let parsedByteRanged := Parser.parseTopDecs_declByteRanged
            fromNat source false declarations hparse
          let targetByteRanged := panTargetDeclarationsWithDefaultMain_byteRanged
            declarations parsedByteRanged
          match compileFlapjackEntryCake architecture bytesInWord (fun value => fromNat value)
              start (panTargetDeclarationsWithDefaultMain declarations)
              (some (.isTrue targetByteRanged)) with
          | none => .error .entryNotFound
          | some pipeline =>
              -- Same production Crep-to-Loop route as `pipeline.loop`, at the
              -- runtime-image label base.
              let loop := pipelineLoopFunctionsSource architecture stackFunctionFirstLabel
                pipeline.crepe
              let sourceWords := panToWordCompileProg loop
              let discoveryWords :=
                sourceWords.map
                  (fun (label, arity, body) => (label, arity, wordProgDCE body))
              /- The source-shaped list has the same section order after the
                 source loop conversion, so mirror Cake before exporting. -/
              let discoveredNames :=
                (discoveryWords.reverse.flatMap
                  (fun entry : Nat × Nat × WordProg (RiscV.Word 64) =>
                    RiscV.wordProgFfiNamesCake (wordFfiDiscoveryBody entry.2.2))).eraseDups
              let discoveredServices := discoveredNames.zip (List.range discoveredNames.length)
              let _services := services ++ discoveredServices
              match pipelineWordFunctionsAllocatedWithSpillsAndFullSsaAndBitmapsFromWordChecked
                  (RiscV.wordStackInitialBitmaps false) sourceWords with
              | .error error =>
                  .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                    pipeline.crepe error)
              | .ok (functions, bitmaps) =>
                  -- At RV64 the bytes come from the reviewed `lab_to_target$compile`
                  -- (`RiscV.labProgramToRiscVSections`).
                  match RiscV.runtimeSectionsFromBackend config names bitmaps removeConfig
                      RiscV.CakeRegAlloc.cakeRiscVRegisterCount 0
                      (functions.map (fun (label, _, body) => (label, body)))
                      (some discoveredNames) with
                  | .error error =>
                      .error (sourceRiscVImageErrorOfLowering stackFunctionFirstLabel
                        pipeline.crepe (.labToRiscV error))
                  | .ok sections =>
                      .ok { crepe := pipeline.crepe, bitmaps, sections,
                            warnings, ffiNames := discoveredNames }
 := by
  have hcallback (bitmaps : RiscV.WordStackBitmapState)
      (programs : List (Nat × StackProg Nat)) (expected : Option (List String)) :
      RiscV.runtimeSectionsFromBackend config names bitmaps removeConfig
        RiscV.CakeRegAlloc.cakeRiscVRegisterCount 0 programs expected =
      RiscV.compileStackProgramNatListToRiscVSectionsCakeChecked (width := 64)
        { services := [] } removeConfig {} {} 0 RiscV.CakeRegAlloc.cakeRiscVRegisterCount 0
        0 programs expected := by
    exact (RiscV.checkedSections_fullBackendOutput config names bitmaps hStack hData hLab
      { services := [] } removeConfig {} {} 0 RiscV.CakeRegAlloc.cakeRiscVRegisterCount 0
      0 programs expected).symm
  simp_rw [hcallback]
  with_unfolding_all rfl

end Flapjack
