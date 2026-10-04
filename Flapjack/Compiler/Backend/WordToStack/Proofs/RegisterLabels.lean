import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Compiler.Backend.StackProps.CodeLabels

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps

/-- Both register-write helpers preserve empty referenced-code labels for an
arbitrary callback whose results have no labels. The conjunction of implications
matches the original proved val after its explicit IMP_CONJ_THM simplification.
No register/frame bounds or calling convention premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getCodeLabelsWReg {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (register : Nat) (frame : Nat × Nat × Nat) :
    ((∀ n, getCodeLabels (g n) = ∅) →
      getCodeLabels (wRegWrite1Native g register frame) = ∅) ∧
    ((∀ n, getCodeLabels (g n) = ∅) →
      getCodeLabels (wRegWrite2Native g register frame) = ∅) := by
  constructor <;> intro h
  · simp only [wRegWrite1Native]
    split <;> simp [getCodeLabels,h]
  · simp only [wRegWrite2Native]
    split <;> simp [getCodeLabels,h]

end Flapjack.Compiler.Backend.WordToStack.Native
