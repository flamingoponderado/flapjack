import Flapjack.RiscV.ArtifactFormat
import Flapjack.RiscV.NativeCLIAdapter
import Flapjack.Compiler.Backend.Backend

/-! CakeML RISC-V assembly output for the normal non-returning entry point.
This uses the shared export frame and adds CakeML's bitmap initialization,
which is omitted by the Pancake export path. -/
namespace Flapjack.RiscV.CakeArtifactFormat
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

/-- Format the compiled tuple using the original non-returning CakeML RISC-V
startup, FFI, bitmap, byte, and symbol conventions. -/
def assembly (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (config : Backend.Config) : String :=
  let output := Flapjack.RiscV.pancakeAssemblyFrame
    ((Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map toStringOfBytes)
    bytes (bitmaps.map BitVec.toNat) (Flapjack.RiscV.NativeCLI.symbolLines config.symbols)
  output.replace "     ld      a2,cdecl(cml_stack)    # arg3: first address of stack\n"
    ("     la      t3,cake_bitmaps\n" ++
     "     sd      t3, 0(a1)              # store bitmap pointer\n" ++
     "     ld      a2,cdecl(cml_stack)    # arg3: first address of stack\n")

end Flapjack.RiscV.CakeArtifactFormat
