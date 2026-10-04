import Flapjack.RiscV.LabToTargetRoute

namespace Flapjack.RiscV
open Flapjack.Compiler.Backend

/-- Flapjack runtime-image output adapter, with no independent HOL declaration.
Retains the complete original backend tuple while adding sections from the
returned laboratory configuration. Compiler rejection remains NONE. -/
def backendRuntimeImage {Bitmaps : Type}
    (output : Option (List (BitVec 8) × Bitmaps × Backend.Config)) :
    Option (List (BitVec 8) × Bitmaps × List (EncodedRiscVSection 64) × Backend.Config) :=
  output.map fun (bytes, bitmaps, config) =>
    (bytes, bitmaps, sectionsOfSymbols bytes config.labConf.secPosLen, config)

/-- Actual original native Word-to-Stack/full backend composition at the output
adapter. This is Flapjack routing infrastructure, not a new HOL semantics port.
All compileNative stubs, bitmaps and updated word/lab configuration are retained;
there is no accepted-output premise and no label filter, insertion or relabeling. -/
theorem fromWord_runtimeImage (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString)
    (program : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    backendRuntimeImage (Backend.fromWord Compiler.Encoders.RiscV.Target.riscvConfig
      config names program) =
    let (bitmaps, wordConf, _frames, stack) := WordToStack.Native.compileNative
      Compiler.Encoders.RiscV.Target.riscvConfig config.stackConf.perfCalls program
    backendRuntimeImage (Backend.fromStack Compiler.Encoders.RiscV.Target.riscvConfig
      {config with wordConf := wordConf} names stack bitmaps) := rfl

end Flapjack.RiscV
