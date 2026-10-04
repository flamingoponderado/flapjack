import Flapjack.Compiler.Backend.Semantics.StackSem.Labels
import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Ordered continuation-label extraction from the original StackProps script.
This proof-script helper preserves order and duplicates; it does not evaluate
programs or assert a compiler-pass simulation. -/
namespace Flapjack.StackPropsCodeLabels
open Flapjack.Compiler.Backend.StackLang

/-- Full original ordered extraction on the faithful program carrier. Both
outer Call labels precede labels nested in the return and exception bodies.
A Call without a return continuation ignores its exception handler. The
ignored instruction and FFI fields retain their exact carrier types. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def extractLabels {width : Nat} [NeZero width] : HolProg width → List (Nat × Nat)
  | .call returns _ handler =>
      match returns with
      | none => []
      | some (returnBody, _link, first, second) =>
          let returnRest := extractLabels returnBody
          match handler with
          | none => [(first, second)] ++ returnRest
          | some (handlerBody, handlerFirst, handlerSecond) =>
              [(first, second), (handlerFirst, handlerSecond)] ++
                returnRest ++ extractLabels handlerBody
  | .loop body => extractLabels body
  | .seq first second => extractLabels first ++ extractLabels second
  | .ite _ _ _ first second => extractLabels first ++ extractLabels second
  | _ => []
termination_by program => sizeOf program
decreasing_by all_goals simp_wf <;> omega

/-- Full original successful code lookup implies containment of every label
in the returned program. Register keys are arbitrary; register and program
word dimensions are independent. The only premise is the original successful
lookup; no domain, branch, target-evaluation or representation premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem findCodeImpGetLabels {registerWidth : Nat} {programWidth : Nat}
    [NeZero registerWidth] [NeZero programWidth] {κ : Type}
    (target : Sum Nat κ) (regs : HolFiniteMapExact κ (WordLocW registerWidth))
    (code : Spt (HolProg programWidth)) (program : HolProg programWidth)
    (h : StackSemControl.findCode target regs code = some program) :
    ∀ label, StackSem.getLabelsExact program label → StackSem.locCheckExact code label := by
  have lookup : ∃ key, sptLookup key code = some program := by
    cases target with
    | inl key => exact ⟨key, h⟩
    | inr reg =>
        cases hr : regs.lookup reg with
        | none => simp [StackSemControl.findCode, hr] at h
        | some value =>
            cases value with
            | word value => simp [StackSemControl.findCode, hr] at h
            | loc key offset =>
                cases offset with
                | zero => exact ⟨key, by simpa [StackSemControl.findCode, hr] using h⟩
                | succ offset => simp [StackSemControl.findCode, hr] at h
  intro label hl
  obtain ⟨key, hk⟩ := lookup
  exact Or.inr ⟨key, program, hk, hl⟩

end Flapjack.StackPropsCodeLabels
