import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.RiscVConfig.Names
import Flapjack.Compiler.Backend.StackToLab.ExecutedInput
import Flapjack.Compiler.Backend.StackLang.ProductionWordBoundary
import Flapjack.Compiler.Backend.StackLang.ProductionMacros

/-!
Executed production input boundary for the native Stack-to-Lab section pass.
Flapjack-specific infrastructure, with no HOL declaration. Native word payloads
are converted before flattening, production macro leaves are expanded using the
reviewed projection, non-byte FFI names and residual operations are rejected.
The output is the literal native prog_to_section result through its lossless
supported output codec. No independent labFlatten fallback, global seed maximum,
or extra entry labels are introduced. This does not prove upstream StackRemove
or Word-to-Stack semantics, nor discharge their supported-input invariants.
-/
namespace Flapjack.Compiler.Backend.StackToLab.Production
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Complete partial production input codec with honest boundary failures. -/
def toNative? {width : Nat} [NeZero width] (program : StackProg Nat) : Option (HolProg width) :=
  if byteNames program then do
    let projected ← ProductionMacros.projectMacros (natToWord program)
    productionToHolProg projected
  else none

/-- Exact reviewed native section lowering, preserving its own seed/entry convention. -/
def section? {width : Nat} [NeZero width] (input : Nat × StackProg Nat) :
    Option (LabSection (BitVec width)) := do
  let native ← toNative? input.2
  ExecutedInput.sectionToExecuted? (input.1, native)

/-- Every successful production section identifies its actual converted native
input and recovers the exact reviewed native output. No target evaluation is
assumed and this codec theorem is not a pass-simulation statement. -/
theorem section_recover {width : Nat} [NeZero width]
    (input : Nat × StackProg Nat) (output : LabSection (BitVec width))
    (accepted : section? input = some output) :
    ∃ native, toNative? input.2 = some native ∧
      ExecutedInput.PostRemoval native ∧
      ExecutedCodec.sectionFromExecuted? output = some (progToSectionHOL (input.1, native)) := by
  simp [section?, Option.bind_eq_some_iff] at accepted
  obtain ⟨native, converted, lowered⟩ := accepted
  exact ⟨native, converted, ExecutedInput.section_postRemoval _ _ lowered,
    ExecutedInput.section_recover _ _ lowered⟩

/-- Actual native removal and register renaming before native section lowering.
This Flapjack production boundary is not a HOL simulation theorem. -/
def removedSection? {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (input : Nat × StackProg Nat) :
    Option (LabSection (BitVec width)) := do
  let native ← toNative? input.2
  let removed := Flapjack.Compiler.Backend.StackRemove.progComp jump bounds pointer (input.1, native)
  let renamed := Flapjack.Compiler.Backend.StackNames.progCompEntryHOL
    Flapjack.Compiler.Backend.RiscVConfig.riscvNames removed
  ExecutedInput.sectionToExecuted? renamed

/-- Every successful executed native removal/renaming/section boundary recovers
its actual complete native tree and literal native section output. This is a
codec correspondence, not an evaluator or pass-correctness theorem. -/
theorem removedSection_recover {width : Nat} [NeZero width] (jump : Bool)
    (bounds : BitVec width × BitVec width) (pointer : Nat) (input : Nat × StackProg Nat)
    (output : LabSection (BitVec width)) (accepted : removedSection? jump bounds pointer input = some output) :
    ∃ native, toNative? input.2 = some native ∧
      let renamed := Flapjack.Compiler.Backend.StackNames.progCompHOL
        Flapjack.Compiler.Backend.RiscVConfig.riscvNames
        (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer native)
      ExecutedInput.PostRemoval renamed ∧
        ExecutedCodec.sectionFromExecuted? output = some (progToSectionHOL (input.1, renamed)) := by
  cases converted : toNative? (width := width) input.2 with
  | none => simp [removedSection?, converted] at accepted
  | some native =>
      have lowered : ExecutedInput.sectionToExecuted?
          (input.1, Flapjack.Compiler.Backend.StackNames.progCompHOL
            Flapjack.Compiler.Backend.RiscVConfig.riscvNames
            (Flapjack.Compiler.Backend.StackRemove.comp jump bounds pointer native)) = some output := by
        simpa [removedSection?, converted, Flapjack.Compiler.Backend.StackRemove.progComp,
          Flapjack.Compiler.Backend.StackNames.progCompEntryHOL] using accepted
      exact ⟨native, rfl, ExecutedInput.section_postRemoval _ _ lowered,
        ExecutedInput.section_recover _ _ lowered⟩

end Flapjack.Compiler.Backend.StackToLab.Production
