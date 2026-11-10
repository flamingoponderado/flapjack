module

public import Flapjack.Compiler.Backend.SourceToFlat.ToWordIncremental
public import Flapjack.Compiler.Backend.Backend
public import Flapjack.Compiler.Backend.WordToWord.FastCompile
public import Flapjack.Compiler.Backend.RegAlloc.Executable
public import Flapjack.Compiler.Encoders.RiscV.Target.Configuration

@[expose] public section

/-! Checked incremental CakeML compilation through the RISC-V backend. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack

/-- Compile an incremental source batch using the shared word, stack and
RISC-V target passes. The outer option reports an unsupported checked frontend
stage. The inner option is the source target assembler result: its failure
retains the source, closure, BVL and bitmap-length updates, while leaving the
lab configuration unchanged. The colouring oracle is not consumed in this
incremental path. Correspondence and end-to-end correctness remain open. -/
def compileCakeIncToRiscVFuel (fuel : Nat) (config : Backend.Config)
    (envId : Nat × Nat) (declarations : List AstHOL.Dec) :
    Option (Backend.Config × Option (List (BitVec 8) × List (BitVec 64))) := do
  let asm := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  let data := Backend.ensureFpConfOk asm config.dataConf
  let ((source, closure, bvl), program) ←
    compileCakeIncToWord64Fuel fuel (config.sourceConf, config.closConf, config.bvlConf)
      data envId declarations
  let registers := asm.regCount - (5 + asm.avoidRegs.length)
  let program := program.map fun p => WordToWord.fullCompileSingleWith RegAlloc.regAllocExecutable
    asm.twoRegArith registers config.wordToWordConf.regAlg asm (p, none)
  let (stack, _, bitmaps) := WordToStack.Native.compileWordToStackNative asm config.stackConf.perfCalls
    registers program (.nil, config.wordConf.bitmapsLength)
  let lab := StackToLab.compileNoStubs config.stackConf.regNames config.stackConf.jump asm.addrOffset
    (asm.regCount - (3 + asm.avoidRegs.length)) stack
  let updatedWord := { config.wordConf with bitmapsLength := bitmaps.2 }
  let updated := { config with sourceConf := source, closConf := closure, bvlConf := bvl, wordConf := updatedWord }
  match LabToTarget.compile asm config.labConf lab with
  | none => pure (updated, none)
  | some (bytes, labConfig) =>
    pure ({ updated with labConf := labConfig }, some (bytes, appListAppend bitmaps.1))

/-- Runtime-evaluation interface for the checked RISC-V incremental compiler.
For this 64-bit target the source `upper_w2w` bitmap conversion is the identity.
Both checked frontend failure and target assembly failure produce `none`, as
required by the evaluation interface. This is not yet a reviewed HOL port. -/
def compileCakeIncForEvalFuel (fuel : Nat)
    (input : (Nat × Nat) × Backend.Config × List AstHOL.Dec) :
    Option (Backend.Config × List (BitVec 8) × List (BitVec 64)) := do
  let (config, target) ← compileCakeIncToRiscVFuel fuel input.2.1 input.1 input.2.2
  let (bytes, bitmaps) ← target
  pure (config, bytes, bitmaps)

end Flapjack.Compiler.Backend.SourceToFlat
