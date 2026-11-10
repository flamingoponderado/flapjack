module

public import Flapjack.Compiler.Backend.SourceToFlat.ToWord
public import Flapjack.Compiler.Backend.RegAlloc.Executable
public import Flapjack.Compiler.Backend.WordToWord.FastCompile
public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
public import Flapjack.Compiler.Backend.DataToWord.Names
public import Flapjack.Compiler.Backend.WordToStack.StubNames
public import Flapjack.Compiler.Backend.StackAlloc.StubNames
public import Flapjack.Compiler.Backend.StackRemove.StubNames

@[expose] public section

/-! CakeML AST to RISC-V backend compositions. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Assemble the original backend stub-name prefix over BVI output names. This
is Flapjack composition infrastructure, not a separate HOL declaration. -/
def backendNames (names : Spt Basis.Pure.MlString.MlString) : Spt Basis.Pure.MlString.MlString :=
  sptUnion (sptFromAList (DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- Run the configured CakeML AST-to-RISC-V path. The bignum mini-program is
captured from pinned HOL and compiled in Lean; unsupported cases return `none`.
No whole-compiler correctness theorem or final-byte correspondence is claimed. -/
def compileCakeToRiscVConfiguredFuel (fuel : Nat) (config : Backend.Config)
    (decls : List AstHOL.Dec) : Option (List (BitVec 8) × List (BitVec 64) × Backend.Config) := do
  let asmConf := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let dataConf := Backend.ensureFpConfOk asmConf config.dataConf
  let (source, closure, bvlConfig, program, names) ←
    compileCakeToWord64ConfiguredFuel fuel config.sourceConf config.closConf config.bvlConf dataConf decls
  let (col, program) := WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let config := { config with sourceConf := source, closConf := closure, bvlConf := bvlConfig }
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  Backend.fromWord asmConf config (backendNames names) program

end Flapjack.Compiler.Backend.SourceToFlat
