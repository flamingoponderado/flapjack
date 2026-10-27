import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

/-! Restricted CakeML AST to RISC-V backend composition. -/
namespace Flapjack.Compiler.Backend.SourceToFlat

/-- Execute the existing RISC-V word optimizer and backend after the checked
source-to-word route. The caller supplies the symbol-name map: source and
stub name propagation, the default frontend optimizations, and the generic
bignum generator are not yet ported here. This partial Flapjack composition
is not the original whole-compiler definition or a correctness theorem. -/
def compileCakeToRiscVNoOptsFuel (fuel : Nat) (config : Backend.Config)
    (names : Spt Basis.Pure.MlString.MlString) (decls : List AstHOL.Dec) :
    Option (List (BitVec 8) × List (BitVec 64) × Backend.Config) := do
  let asmConf := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let dataConf := { config.dataConf with hasFpOps := decide (1 < asmConf.fpRegCount), hasFpTern := false }
  let (source, closure, start, program, _) ←
    compileCakeToWordWithStubs64NoOptsFuel fuel config.sourceConf config.closConf dataConf decls
  let closure := { closure with start := start }
  let (col, program) := WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let config := { config with sourceConf := source, closConf := closure }
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  Backend.fromWord asmConf config names program

end Flapjack.Compiler.Backend.SourceToFlat
