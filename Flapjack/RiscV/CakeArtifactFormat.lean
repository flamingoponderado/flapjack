import Flapjack.RiscV.ArtifactFormat
import Flapjack.RiscV.NativeCLIAdapter
import Flapjack.Compiler.Backend.Backend

/-! CakeML RISC-V assembly output, including bitmap initialization and the
optional returning entry points from the pinned exporter. -/
namespace Flapjack.RiscV.CakeArtifactFormat
open Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString

/-- The returning entry sequence is a local exporter constant in the pinned
RISC-V script, rather than a HOL theory declaration. -/
private def returnEntryLines : List String :=
  ["",
   "",
   "cml_enter:",
   "     addi    sp, sp, -104",
   "     sd      ra, 0(sp)",
   "     sd      s11, 8(sp)",
   "     sd      s10, 16(sp)",
   "     sd      s9, 24(sp)",
   "     sd      s8, 32(sp)",
   "     sd      s7, 40(sp)",
   "     sd      s6, 48(sp)",
   "     sd      s5, 56(sp)",
   "     sd      s4, 64(sp)",
   "     sd      s3, 72(sp)",
   "     sd      s2, 80(sp)",
   "     sd      s1, 88(sp)",
   "     sd      s0, 96(sp)",
   "     j       cake_main",
   "     .p2align 4",
   "",
   "",
   "cake_enter:",
   "     addi    sp, sp, -104",
   "     sd      ra, 0(sp)",
   "     sd      s11, 8(sp)",
   "     sd      s10, 16(sp)",
   "     sd      s9, 24(sp)",
   "     sd      s8, 32(sp)",
   "     sd      s7, 40(sp)",
   "     sd      s6, 48(sp)",
   "     sd      s5, 56(sp)",
   "     sd      s4, 64(sp)",
   "     sd      s3, 72(sp)",
   "     sd      s2, 80(sp)",
   "     sd      s1, 88(sp)",
   "     sd      s0, 96(sp)",
   "     la      t1, can_enter",
   "     ld      t2, 0(t1)",
   "     beq     t2, zero, cake_err3",
   "     sd      zero, 0(t1)",
   "     la      t1, ret_base",
   "     ld      s10, 0(t1)",
   "     la      t1, ret_stack",
   "     ld      s8, 0(t1)",
   "     la      t1, ret_stackend",
   "     ld      s9, 0(t1)",
   "     la      ra, cake_return",
   "     jr      t0",
   "     .p2align 4",
   "",
   "",
   "cml_return:",
   "     la      t1, ret_base",
   "     sd      s10, 0(t1)",
   "     la      t1, ret_stack",
   "     sd      s8, 0(t1)",
   "     la      t1, ret_stackend",
   "     sd      s9, 0(t1)",
   "",
   "cake_return:",
   "     la      t1, can_enter",
   "     li      t2, 1",
   "     sd      t2, 0(t1)",
   "     ld      s0, 96(sp)",
   "     ld      s1, 88(sp)",
   "     ld      s2, 80(sp)",
   "     ld      s3, 72(sp)",
   "     ld      s4, 64(sp)",
   "     ld      s5, 56(sp)",
   "     ld      s6, 48(sp)",
   "     ld      s7, 40(sp)",
   "     ld      s8, 32(sp)",
   "     ld      s9, 24(sp)",
   "     ld      s10, 16(sp)",
   "     ld      s11, 8(sp)",
   "     ld      ra, 0(sp)",
   "     addi    sp, sp, 104",
   "     ret",
   "     .p2align 4",
   "",
   "",
   "cake_err3:",
   "     li      a0, 3",
   "     j       cdecl(cml_err)",
   "     .p2align 4",
   ""]

/-- Flapjack formatting helper: render the exporter wrappers in symbol order.
Unlike HOL `export_funcs`, this takes the whole backend configuration. -/
private def exportWrappers (config : Backend.Config) : String :=
  String.join (config.symbols.zipIdx.filterMap fun ((name, _, _), index) =>
    if name ∈ config.exported then
      let raw := toStringOfBytes name
      let label := "cml_" ++ String.join (raw.toList.map Flapjack.RiscV.NativeCLI.escapeSymChar) ++
        "_" ++ toString index
      some ("\n     .globl  cdecl(" ++ raw ++ ")\n" ++
        "     .type   " ++ raw ++ ", function\n" ++
        "cdecl(" ++ raw ++ "):\n" ++
        "     la      t0, " ++ raw ++ "_jmp\n" ++
        "     j       cake_enter\n" ++ raw ++ "_jmp:\n" ++
        "     j       " ++ label ++ "\n")
    else none)

/-- Flapjack formatting infrastructure combining the shared Pancake frame with
CakeML startup, FFI, bitmap, symbol and optional returning-entry conventions.
It takes a backend configuration rather than the HOL exporter inputs. -/
def assembly (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (config : Backend.Config)
    (mainReturn : Bool := false) : String :=
  let output := Flapjack.RiscV.pancakeAssemblyFrame
    ((Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map toStringOfBytes)
    bytes (bitmaps.map BitVec.toNat) (Flapjack.RiscV.NativeCLI.symbolLines config.symbols)
  let output := output.replace "     ld      a2,cdecl(cml_stack)    # arg3: first address of stack\n"
    ("     la      t3,cake_bitmaps\n" ++
     "     sd      t3, 0(a1)              # store bitmap pointer\n" ++
     "     ld      a2,cdecl(cml_stack)    # arg3: first address of stack\n")
  if mainReturn then
    let output := output.replace "cdecl(cml_stackend): .quad 0\n"
      ("cdecl(cml_stackend): .quad 0\n" ++
       "ret_base: .quad 0\nret_stack: .quad 0\nret_stackend: .quad 0\ncan_enter: .quad 0\n")
    let output := output.replace "     j       cake_main\n" "     j       cml_enter\n"
    let output := output.replace "cake_exit:\n     tail cdecl(cml_exit)\n"
      "cake_exit:\n     j    cml_return\n"
    output ++ String.intercalate "\n" (returnEntryLines ++ [""]) ++ exportWrappers config
  else output

end Flapjack.RiscV.CakeArtifactFormat
