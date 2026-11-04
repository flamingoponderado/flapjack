import Flapjack.RiscV.InitializedRuntime
import Flapjack.Compiler.Backend.StackToLab.Production
import Flapjack.RiscV.Lab

/-!
# Checked Lab-to-RISC-V diagnostics

The historical Lab compiler returns `Option` so existing callers keep their
pass-local API.  That loses the reason and source position when a target-only
pseudo-operation is outside the current RISC-V runtime contract.  This module
adds a checked boundary with a structured, section/position-tagged error while
leaving the established Option entrypoints unchanged.
-/

namespace Flapjack.RiscV

inductive LabUnsupportedFeature where
  | heapAlloc
  | halt
  | longDiv
  | loweringFailure
  deriving DecidableEq, Repr

structure LabLoweringError where
  sectionId : Nat
  position : Nat
  feature : LabUnsupportedFeature
  deriving DecidableEq, Repr

def labLoweringError (sectionId position : Nat)
    (feature : LabUnsupportedFeature) : LabLoweringError :=
  { sectionId, position, feature }

def labPlainUnsupportedFeature [NeZero width] :
    LabPlain (Word width) → Option LabUnsupportedFeature
  | .word (.arith (.longDiv _ _ _ _ _)) => some .longDiv
  | _ => none

def labPlainLoweringError [NeZero width] (sectionId position : Nat)
    (operation : LabPlain (Word width)) : LabLoweringError :=
  { sectionId, position,
    feature := (labPlainUnsupportedFeature operation).getD .loweringFailure }

end Flapjack.RiscV
