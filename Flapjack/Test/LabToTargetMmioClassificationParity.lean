import Flapjack.Compiler.Backend.LabToTarget.MmioClassification
import Flapjack.Compiler.Backend.Semantics.TargetSem.State

namespace Flapjack.Test.LabToTargetMmioClassificationParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩

/-- Test notation for the complete source conjunction, including both bounded
classification families. This is Flapjack test infrastructure, not a HOL port. -/
private def Classification (names : List HolFfiName) (index : Nat) : Prop :=
  index ≤ names.length ∧
    (∀ j, j < index → ∃ name, holEl j names = .extCall name) ∧
    (∀ j, index ≤ j ∧ j < names.length →
      ∃ operation, holEl j names = .sharedMem operation)

private theorem classifyAppend (externalNames suffix : List HolFfiName)
    (h : (∀ x ∈ suffix, ∀ s, x ≠ HolFfiName.extCall s) ∧
      (∀ x ∈ externalNames, ∃ s, x = HolFfiName.extCall s)) :
    Classification (externalNames++suffix) externalNames.length :=
  mmioPcsMinIndex_isSome _ _ (mmioPcsMinIndex_append _ _ h)

private def guest := HolFfiName.extCall (Flapjack.Basis.Pure.MlString.ofString "guest")

example : Classification [] 0 := by
  simpa using classifyAppend [] [] ⟨by simp, by simp⟩
example : Classification [guest] 1 := by
  simpa using classifyAppend [guest] [] ⟨by simp, by simp [guest]⟩
example : Classification [.sharedMem .mappedRead] 0 := by
  simpa using classifyAppend [] [.sharedMem .mappedRead] ⟨by simp, by simp⟩
example : Classification [.sharedMem .mappedWrite] 0 := by
  simpa using classifyAppend [] [.sharedMem .mappedWrite] ⟨by simp, by simp⟩
example : Classification [guest,.sharedMem .mappedRead,.sharedMem .mappedWrite] 1 := by
  simpa using classifyAppend [guest] [.sharedMem .mappedRead,.sharedMem .mappedWrite]
    ⟨by simp, by simp [guest]⟩
example : Classification [guest,guest,.sharedMem .mappedRead,.sharedMem .mappedWrite] 2 := by
  simpa using classifyAppend [guest,guest] [.sharedMem .mappedRead,.sharedMem .mappedWrite]
    ⟨by simp, by simp [guest]⟩
example : Classification [guest,guest,guest,guest,.sharedMem .mappedRead] 4 := by
  simpa using classifyAppend [guest,guest,guest,guest] [.sharedMem .mappedRead]
    ⟨by simp, by simp [guest]⟩
example : ¬ 3 ≤ [guest].length := by decide
example : ¬ ∃ name, holEl 0 [HolFfiName.sharedMem .mappedRead] = .extCall name := by
  simp [holEl, holHd]

example (names : List HolFfiName) (index : Nat) :
    mmioPcsMinIndex names = some index → index ≤ names.length ∧
    (∀ j, j < index → ∃ name, holEl j names = .extCall name) ∧
    (∀ j, index ≤ j ∧ j < names.length →
      ∃ operation, holEl j names = .sharedMem operation) :=
  mmioPcsMinIndex_isSome names index

example {width : Nat} [NeZero width] {state projection : Type}
    (mc : MachineConfig width state projection) (index : Nat)
    (hs : mmioPcsMinIndex mc.ffiNames = some index) :
    index ≤ mc.ffiNames.length ∧
    (∀ j, j < index → ∃ name, holEl j mc.ffiNames = .extCall name) ∧
    (∀ j, index ≤ j ∧ j < mc.ffiNames.length →
      ∃ operation, holEl j mc.ffiNames = .sharedMem operation) :=
  mmioPcsMinIndex_isSome _ _ hs

end Flapjack.Test.LabToTargetMmioClassificationParity
