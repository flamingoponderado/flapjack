import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics

/-! Whole-program data semantics boundary cases. -/
namespace Flapjack.Test.DataSemSemantics
open Flapjack
open Flapjack.Compiler.Backend
open DataSem

example : computeLimits 7 true false true (123, 456) = ⟨456, 7, 123, true, false, true⟩ := by
  rfl

example {C F : Type} (s : State C F) : evaluateSafe .skip s = s.safeForSpace := by
  simp [evaluateSafe, evaluate]

example {C F : Type} (s : State C F) : evaluatePeak .skip s = s.peakHeapLength := by
  simp [evaluatePeak, evaluate]

/-- A missing entry point is a fatal error at the initial call. -/
example {C F : Type} (ffi : HolFfiState F) (oracle : CompileOracle C)
    (compiler : Compiler C) (limits : Limits) (sizes : Spt Nat) (start : Nat) :
    semantics ffi .ln oracle compiler limits sizes start = .fail := by
  classical
  unfold semantics
  apply ite_eq_left
  refine ⟨0, ?_⟩
  simp [evaluate, initialState, getVars, findCode, sptLookup]

end Flapjack.Test.DataSemSemantics
