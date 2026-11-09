import Flapjack.Compiler.Backend.WordToStack.Guard
import Flapjack.Compiler.Backend.LabToTarget.EncodingGuard
import Flapjack.Compiler.Encoders.RiscV.Unsupported
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.RiscV.NativeSource

/-!
# Word-to-stack and register-range guard tests

Pins the Flapjack-only guards added before native encoding: the word-to-stack
guard rejects exactly the constructs `compNative` would silently lower to
`Skip` (remaining `Assign`/`Store`, a `Set` of `BitmapBase` or a non-`Var`
expression, and a `ShareInst` whose expression is not an address), including
nested sub-programs; the encoding guard rejects an `Asm` register outside the
target's register count or in its avoid set, and the two shapes `riscvAst` maps
to the fail encoding that the RISC-V configuration never emits (`LongDiv`,
`FP`).  `Skip` stays accepted: it is the padding instruction and its fail
encoding is the intended no-op.  A normal program passes all guards, and the
checked pipeline produces exactly the bytes of the reviewed
`compileProgAsmFast`.  The reviewed `@[hol]` definitions are untouched.
-/

namespace Flapjack.Test.WordStackGuard

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.WordToStack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV
open Flapjack.Compiler.Encoders.RiscV.Target (riscvConfig)
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Basis.Pure.MlString

/-! ## Word-to-stack guard -/

private def assignProgram : WordLangProgHOL (BitVec 64) := .assign 0 (.var 1)

private def storeProgram : WordLangProgHOL (BitVec 64) := .store (.var 1) 0

private def bitmapBaseProgram : WordLangProgHOL (BitVec 64) :=
  .set .bitmapBase (.var 0)

private def nonVarSetProgram : WordLangProgHOL (BitVec 64) :=
  .set .currHeap (.const 0)

private def nonAddressShareProgram : WordLangProgHOL (BitVec 64) :=
  .shareInst .load 0 (.const 0)

private def nestedAssignProgram : WordLangProgHOL (BitVec 64) :=
  .seq .skip (.assign 0 (.var 0))

private def callAssignProgram : WordLangProgHOL (BitVec 64) :=
  .call (some ([], (.ln, .ln), .assign 0 (.var 0), 0, 0)) none [] none

private def handlerStoreProgram : WordLangProgHOL (BitVec 64) :=
  .call none none [] (some (0, .store (.var 0) 0, 0, 0))

private def supportedProgram : WordLangProgHOL (BitVec 64) :=
  .seq (.set .currHeap (.var 1)) (.shareInst .load 0 (.var 2))

private def skipProgram : WordLangProgHOL (BitVec 64) := .skip

-- Each silent-drop construct is located, carrying the function number.
#guard decide
  (firstUncompilable [(3, 1, assignProgram)] = some (.unsupported 3 .assign))

#guard decide
  (firstUncompilable [(3, 1, storeProgram)] = some (.unsupported 3 .store))

#guard decide
  (firstUncompilable [(3, 1, bitmapBaseProgram)] = some (.unsupported 3 .setBitmapBase))

#guard decide
  (firstUncompilable [(3, 1, nonVarSetProgram)] = some (.unsupported 3 .setNonVar))

#guard decide
  (firstUncompilable [(3, 1, nonAddressShareProgram)] =
    some (.unsupported 3 .shareInstNonAddress))

-- The traversal follows `compNative` into `seq` and call continuations.
#guard decide
  (firstUncompilable [(3, 1, nestedAssignProgram)] = some (.unsupported 3 .assign))

#guard decide
  (firstUncompilable [(3, 1, callAssignProgram)] = some (.unsupported 3 .assign))

#guard decide
  (firstUncompilable [(3, 1, handlerStoreProgram)] = some (.unsupported 3 .store))

-- Constructs the pass actually lowers are accepted.
#guard decide (firstUncompilable [(3, 1, supportedProgram)] = none)

#guard decide (firstUncompilable [(3, 1, skipProgram)] = none)

-- The first failing row wins, in list order.
#guard decide
  (firstUncompilable [(3, 1, skipProgram), (4, 1, storeProgram)] =
    some (.unsupported 4 .store))

#guard wordStackGuardFailureDescription (.unsupported 7 .assign) =
  "word-to-stack: function 7 contains a remaining Assign, which word-to-stack would drop"

#guard wordStackGuardFailureDescription (.unsupported 2 .shareInstNonAddress) =
  "word-to-stack: function 2 contains a ShareInst whose expression is not an address, " ++
    "which word-to-stack would drop"

/-! ## Encoding guard: register ranges and unsupported shapes -/

private def asmLine (instruction : AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64)) :
    GuardLine 64 :=
  .asm instruction [] 0

private def labSection (lines : List (GuardLine 64)) : GuardSection 64 := ⟨0, lines⟩

-- A register at or above the target register count is reported as out of range.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.const 32 0)))]] =
    some (.outOfRange 0 0 32))

-- Registers in the target's avoid set are reported as reserved.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.const 0 0)))]] =
    some (.avoided 0 0 0))

#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.const 31 0)))]] =
    some (.avoided 0 0 31))

-- A `cbw` line encodes as `Store8 right (Addr left 0)`, so both registers count.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported [labSection [asmLine (.cbw 0 1)]] =
    some (.avoided 0 0 0))

-- Line indices count every line, including labels.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [.label 0 0 0, asmLine (.asmi (.inst (.const 33 0)))]] =
    some (.outOfRange 0 1 33))

-- Section indices count sections in order.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.const 1 0)))],
       labSection [asmLine (.asmi (.inst (.const 40 0)))]] =
    some (.outOfRange 1 0 40))

-- In-range registers are accepted, including memory operands.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.const 1 0)))]] = none)

#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.mem .load 1 (.addr 10 0))))]] = none)

-- `LabAsm` registers are chosen by `stack_to_lab`, not carried from source.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [.labAsm (.jump (.lab 0 0)) 0 [] 0]] = none)

#guard encodingGuardFailureDescription (.outOfRange 2 5 40) =
  "lab-to-target: section 2 line 5 uses register 40, which is outside the target's register count"

#guard encodingGuardFailureDescription (.avoided 0 1 0) =
  "lab-to-target: section 0 line 1 uses register 0, which the target reserves"

-- The two unsupported shapes `riscvAst` maps to the fail encoding are rejected.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.arith (.longDiv 1 10 11 12 13))))]] =
    some (.unsupported 0 0 .longDiv))

#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.fp (.fpAdd 1 2 3))))]] =
    some (.unsupported 0 0 .fp))

-- A supported instruction with a supported register still passes.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst (.arith (.div 1 10 11))))]] = none)

-- `Skip` is the padding instruction; its fail encoding is the intended no-op.
#guard decide
  (firstUnencodable riscvConfig riscvUnsupported
      [labSection [asmLine (.asmi (.inst .skip))]] = none)

#guard encodingGuardFailureDescription (.unsupported 0 3 .longDiv) =
  "lab-to-target: section 0 line 3 cannot be encoded: LongDiv has no RISC-V encoding " ++
    "(the encoder emits the fail encoding)"

#guard encodingGuardFailureDescription (.unsupported 1 2 .fp) =
  "lab-to-target: section 1 line 2 cannot be encoded: a floating-point instruction " ++
    "has no RISC-V encoding (the encoder emits the fail encoding)"

/-! ## A normal program passes both guards -/

private def normalSource : String := "fun 1 main() { return 0; }"

-- The checked pipeline accepts the program and produces exactly the bytes and
-- bitmaps of the reviewed `compileProgAsmFast`.
#guard
  match Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) normalSource with
  | .ok declarations =>
      let program := Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL)
      let config := Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig
      match compileProgAsmFastChecked riscvUnsupported config riscvConfig program,
            compileProgAsmFast config riscvConfig program with
      | .ok (bytes, bitmaps, _), some (bytes', bitmaps', _) =>
          bytes == bytes' && bitmaps == bitmaps'
      | _, _ => false
  | .error _ => false

-- The driver still compiles the same source, with an artifact.
#guard
  match RiscV.NativeSource.compile normalSource with
  | .ok out => out.artifact.isSome
  | .error _ => false

-- The new driver errors render with the established prefix and located detail.
#guard
  sourceRiscVImageErrorDescription (.wordStackGuard (.unsupported 7 .assign)) =
    "native backend compilation failed: word-to-stack: function 7 contains a remaining " ++
      "Assign, which word-to-stack would drop"

#guard
  sourceRiscVImageErrorDescription (.labEncodingGuard (.outOfRange 2 5 40)) =
    "native backend compilation failed: lab-to-target: section 2 line 5 uses register 40, " ++
      "which is outside the target's register count"

end Flapjack.Test.WordStackGuard
