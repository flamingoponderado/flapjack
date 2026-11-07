import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics

/-! Congruence for the factored flat observational semantics. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL

/-- Flat observational semantics agrees when evaluation at every clock has
the same result and FFI state. This is Flapjack infrastructure for the
factored semantics, not a separate HOL theorem port. -/
theorem semantics_eq_of_same_observations {C F : Type} (config : InstallConfig C)
    (ffi : HolFfiState F) (source target : List FlatLang.Exp)
    (same : ∀ clock,
      (evaluateDecs (initialState ffi clock config) source).2 =
        (evaluateDecs (initialState ffi clock config) target).2 ∧
      (evaluateDecs (initialState ffi clock config) source).1.ffi =
        (evaluateDecs (initialState ffi clock config) target).1.ffi) :
    semantics config ffi source = semantics config ffi target := by
  classical
  have failureEq : (∃ clock, (evaluateDecs (initialState ffi clock config) source).2 = some (.abort .typeError)) ↔
      (∃ clock, (evaluateDecs (initialState ffi clock config) target).2 = some (.abort .typeError)) := by
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · exact (same clock).1.symm.trans h
    · exact (same clock).1.trans h
  have terminatingEq : terminatingObservation config ffi source = terminatingObservation config ffi target := by
    funext behavior
    unfold terminatingObservation
    apply propext
    constructor
    · rintro ⟨clock, state, result, outcome, run, outcomeEq, behaviorEq⟩
      have observed := same clock
      rw [run] at observed
      refine ⟨clock, (evaluateDecs (initialState ffi clock config) target).1, result, outcome, ?_, outcomeEq, ?_⟩
      · apply Prod.ext
        · rfl
        · exact observed.1.symm
      · simpa [← observed.2] using behaviorEq
    · rintro ⟨clock, state, result, outcome, run, outcomeEq, behaviorEq⟩
      have observed := same clock
      rw [run] at observed
      refine ⟨clock, (evaluateDecs (initialState ffi clock config) source).1, result, outcome, ?_, outcomeEq, ?_⟩
      · apply Prod.ext
        · rfl
        · exact observed.1
      · simpa [observed.2] using behaviorEq
  have tracesEq :
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluateDecs (initialState ffi clock config) source).1.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList (evaluateDecs (initialState ffi clock config) target).1.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor <;> rintro ⟨clock, h⟩ <;> refine ⟨clock, ?_⟩
    · simpa [(same clock).2] using h
    · simpa [← (same clock).2] using h
  unfold semantics
  simp only [failureEq]
  rw [terminatingEq, tracesEq]

end Flapjack.Compiler.Backend.FlatSem
