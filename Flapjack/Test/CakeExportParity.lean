import Flapjack.RiscV.CakeArtifactFormat
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Test.CakeExportOracle

/-! Byte-for-byte comparison with the pinned HOL RISC-V exporter, including
CakeML startup, bitmap data, FFI ordering and escaped symbols. -/
namespace Flapjack.Test.CakeExportParity
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend

private def config : Backend.Config :=
  let c := RiscVConfig.riscvBackendConfigExecutable
  { c with labConf := { c.labConf with ffiNames := some [.extCall (ofString "put"), .extCall (ofString "get")] }
           symbols := [(ofString "a+", 2, 4), (ofString "F", 6, 3)] }

#guard RiscV.CakeArtifactFormat.assembly [0, 171, 255] [4, 17] config == CakeExportOracle.expected

#guard RiscV.CakeArtifactFormat.assembly [0, 171, 255] [4, 17]
  { config with exported := [ofString "a+", ofString "F"] } true == CakeExportOracle.expectedRet

end Flapjack.Test.CakeExportParity
