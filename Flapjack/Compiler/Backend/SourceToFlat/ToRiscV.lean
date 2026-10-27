import Flapjack.Compiler.Backend.SourceToFlat.ToWord
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.WordToWord.FastCompile
import Flapjack.Compiler.Backend.Backend
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Backend.DataToWord.Names
import Flapjack.Compiler.Backend.WordToStack.StubNames
import Flapjack.Compiler.Backend.StackAlloc.StubNames
import Flapjack.Compiler.Backend.StackRemove.StubNames

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

/-- Assemble the original backend stub-name prefix over BVI output names. This
is Flapjack composition infrastructure, not a separate HOL declaration. -/
def backendNames (names : Spt Basis.Pure.MlString.MlString) : Spt Basis.Pure.MlString.MlString :=
  sptUnion (sptFromAList (DataToWord.stubNames () ++ WordToStack.stubNames () ++
    StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- Execute the restricted source-to-RISC-V route with its propagated BVI and
runtime symbol names. The default frontend optimizations and the generic bignum
generator are still absent, and no whole-compiler correctness theorem is claimed. -/
def compileCakeToRiscVNamedNoOptsFuel (fuel : Nat) (config : Backend.Config)
    (decls : List AstHOL.Dec) : Option (List (BitVec 8) × List (BitVec 64) × Backend.Config) := do
  let asmConf := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let dataConf := { config.dataConf with hasFpOps := decide (1 < asmConf.fpRegCount), hasFpTern := false }
  let (source, closure, start, program, _, names) ←
    compileCakeToWordWithStubsAndNames64NoOptsFuel fuel config.sourceConf config.closConf dataConf decls
  let closure := { closure with start := start }
  let (col, program) := WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let config := { config with sourceConf := source, closConf := closure }
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  Backend.fromWord asmConf config (backendNames names) program

/-- Execute the named RISC-V route after the checked multi-argument and BVI
inlining passes. Other frontend optimizations and the generic bignum generator
remain missing; this is not the full original compiler or its correctness proof. -/
def compileCakeToRiscVInlineFuel (fuel : Nat) (config : Backend.Config)
    (decls : List AstHOL.Dec) : Option (List (BitVec 8) × List (BitVec 64) × Backend.Config) := do
  let asmConf := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let dataConf := { config.dataConf with hasFpOps := decide (1 < asmConf.fpRegCount), hasFpTern := false }
  let (source, closure, start, program, _, names) ←
    compileCakeToWordWithStubsAndNames64InlineFuel fuel config.sourceConf config.closConf dataConf decls
  let closure := { closure with start := start }
  let (col, program) := WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let config := { config with sourceConf := source, closConf := closure }
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  Backend.fromWord asmConf config (backendNames names) program

/-- Execute the BVL-optimized, BVI-inlined restricted route through RISC-V.
Other frontend optimizations and the generic bignum generator remain missing. -/
def compileCakeToRiscVOptimizedFuel (fuel inlineLimit cutSize : Nat) (splitSeq : Bool)
    (config : Backend.Config) (decls : List AstHOL.Dec) :
    Option (List (BitVec 8) × List (BitVec 64) × Backend.Config) := do
  let asmConf := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let dataConf := { config.dataConf with hasFpOps := decide (1 < asmConf.fpRegCount), hasFpTern := false }
  let (source, closure, start, program, _, names) ←
    compileCakeToWord64OptimizedFuel fuel inlineLimit cutSize splitSeq config.sourceConf config.closConf dataConf decls
  let closure := { closure with start := start }
  let (col, program) := WordToWord.compileWith RegAlloc.regAllocExecutable config.wordToWordConf asmConf program
  let config := { config with sourceConf := source, closConf := closure }
  let config := { config with wordToWordConf := { config.wordToWordConf with colOracle := col } }
  Backend.fromWord asmConf config (backendNames names) program

end Flapjack.Compiler.Backend.SourceToFlat
