import Flapjack.Compiler.Backend.LabToTarget.Diagnostics
import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
import Flapjack.RiscV.NativeSource
import Flapjack.RiscV.NativeCLIAdapter

/-!
# Located backend-failure diagnostics

Pins the structured `lab_to_target` failure reported by the Flapjack-only
`compileWithReason` sibling: the FFI-subset check, the missing zero-offset
label check, the agreement with the reviewed `compile`/`compileLab` on success
and failure, and the CLI text `native backend compilation failed: ...` for a
real source program.  These are driver diagnostics; the reviewed `@[hol]`
`compile_lab_def`/`compile_def` are untouched.
-/

namespace Flapjack.Test.BackendFailureDiagnostic

open Flapjack Flapjack.Compiler.Backend LabToTarget
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target (riscvConfig)
open Flapjack.Basis.Pure.MlString

/-- A one-line lab section carrying a single `CallFFI` line. -/
private def ffiSection :
    List (Section (Line (AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64))
      (AsmWithLab HolCmp (HolRegImm 64) MlString) (BitVec 64))) :=
  [⟨0, [.labAsm (.callFFI (ofString "inc")) 0 [] 0]⟩]

/-- A one-line lab section jumping to a zero-offset label that is never defined. -/
private def missingLabelSection :
    List (Section (Line (AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64))
      (AsmWithLab HolCmp (HolRegImm 64) MlString) (BitVec 64))) :=
  [⟨0, [.labAsm (.jump (.lab 7 0)) 0 [] 0]⟩]

/-- A one-line lab section that needs no encoding work. -/
private def labelSection :
    List (Section (Line (AsmOrCbw (HolAsm 64) HolMemop (HolAddr 64))
      (AsmWithLab HolCmp (HolRegImm 64) MlString) (BitVec 64))) :=
  [⟨0, [.label 0 0 0]⟩]

private def labConfig (ffiNames : Option (List HolFfiName)) : LabToTarget.Config :=
  { labels := .ln, secPosLen := [], pos := 0, initClock := 5, ffiNames := ffiNames,
    shmemExtra := [], hashSize := 104729 }

-- The FFI-subset stage is located: the program uses one FFI entry while the
-- configured `ffi_names` list is empty.
#guard decide
  ((compileWithReason riscvConfig (labConfig (some [])) ffiSection) =
    .error (.ffiSubset 1 0))

-- The missing-zero-label stage is located, with the offending label.
#guard decide
  ((compileWithReason riscvConfig (labConfig none) missingLabelSection) =
    .error (.missingZeroLabel 7))

-- On a program the reviewed `compile` accepts, the located sibling returns
-- exactly the same tuple.
#guard decide
  ((compileWithReason riscvConfig (labConfig none) labelSection).toOption =
    compile riscvConfig (labConfig none) labelSection)

#guard labLoweringFailureDescription (.ffiSubset 1 0) =
  "lab-to-target: the program uses 1 FFI entries but the configured ffi_names list has 0"

#guard labLoweringFailureDescription (.missingZeroLabel 7) =
  "lab-to-target: label 7 has no zero-offset entry in the computed label map"

#guard labLoweringFailureDescription (.encodingOk 2 5) =
  "lab-to-target: section 2 line 5 cannot be encoded for this target"

#guard labLoweringFailureDescription .clockExhausted =
  "lab-to-target: label layout did not converge within the configured initial clock"

private def ffiSource : String := "fun 1 main() { @inc(0, 0, 0, 0); return 0; }"

private def ffiEmptyConfig : Compiler.Backend.Backend.Config :=
  { Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig with
    labConf := { Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig.labConf with
      ffiNames := some [] } }

-- A source program whose only external call is rejected by an empty
-- configured FFI list becomes a located artifact failure, not a bare `none`.
#guard
  match RiscV.NativeSource.compileWithConfig ffiEmptyConfig ffiSource with
  | .error (.artifactFailure (.ffiSubset 1 0)) => true
  | _ => false

-- The CLI text keeps the original prefix and appends the located detail.
#guard
  match RiscV.NativeSource.compileWithConfig ffiEmptyConfig ffiSource with
  | .error error =>
      sourceRiscVImageErrorDescription error =
        "native backend compilation failed: lab-to-target: the program uses 1 FFI " ++
          "entries but the configured ffi_names list has 0"
  | .ok _ => false

-- The default configuration still compiles the same program, with an artifact.
#guard
  match RiscV.NativeSource.compile ffiSource with
  | .ok out => out.artifact.isSome
  | .error _ => false

end Flapjack.Test.BackendFailureDiagnostic
