module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Semantics
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateLimitsSwap
public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluateStackFrameSizesSwap
public import Flapjack.HolRef

@[expose] public section

/-!
# Whole-program semantics under the zero limits and the empty frame-size map

Counterpart of `cakeml/compiler/backend/semantics/dataPropsScript.sml:2873`
`semantics_zero_limits`: configuring `zero_limits` and starting with `LN` as the
frame-size map does not change the whole-program behaviour. The proof composes
the already reviewed `evaluate_zero_limits_FST`/`_ffi` and
`evaluate_stack_frame_sizes_FST`/`_ffi` step lemmas, which say that the initial
call's result component and final FFI state are unaffected by either swap.

The private helpers have no separate HOL original: they are the per-clock
projection facts that HOL's proof derives inline with `rw`/`fs` before
comparing the two `semantics` unfoldings.
-/

namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Both swaps leave the initial call's result component and final FFI state
    unchanged. Flapjack infrastructure for `semantics_zero_limits`; no separate
    HOL original. -/
private theorem initialCallRun_swap {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C)
    (compiler : Compiler C) (limits : Limits) (frameSizes : Spt Nat)
    (start clock : Nat) :
    (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)).1 =
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true zeroLimits .ln clock)).1 ∧
    (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)).2.ffi =
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true zeroLimits .ln clock)).2.ffi := by
  have runSwap : initialState ffi code oracle compiler true zeroLimits .ln clock =
      { { initialState ffi code oracle compiler true limits frameSizes clock with
          limits := zeroLimits } with stackFrameSizes := .ln } := rfl
  constructor
  · rw [evaluate_zero_limits_FST (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)
        (none : Option (Result (List DataSem.Value) DataSem.Value))
        (initialState ffi code oracle compiler true limits frameSizes clock),
      evaluate_stack_frame_sizes_FST (.call none (some start) [] none)
        { initialState ffi code oracle compiler true limits frameSizes clock with
          limits := zeroLimits }
        (none : Option (Result (List DataSem.Value) DataSem.Value))
        { initialState ffi code oracle compiler true limits frameSizes clock with
          limits := zeroLimits },
      runSwap]
  · rw [evaluate_zero_limits_ffi (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)
        (none : Option (Result (List DataSem.Value) DataSem.Value))
        (initialState ffi code oracle compiler true limits frameSizes clock),
      evaluate_stack_frame_sizes_ffi (.call none (some start) [] none)
        { initialState ffi code oracle compiler true limits frameSizes clock with
          limits := zeroLimits }
        (none : Option (Result (List DataSem.Value) DataSem.Value))
        { initialState ffi code oracle compiler true limits frameSizes clock with
          limits := zeroLimits },
      runSwap]

/-- Configuring `zero_limits` and the empty frame-size map does not change the
    data-language whole-program behaviour. Port of HOL `semantics_zero_limits`. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "semantics_zero_limits"]
theorem semantics_zero_limits {C F : Type} (ffi : HolFfiState F)
    (code : Spt (Nat × DataLang.Prog)) (oracle : CompileOracle C)
    (compiler : Compiler C) (limits : Limits) (frameSizes : Spt Nat) (start : Nat) :
    semantics ffi code oracle compiler limits frameSizes start =
      semantics ffi code oracle compiler zeroLimits .ln start := by
  classical
  have fstEq : ∀ clock,
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)).1 =
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true zeroLimits .ln clock)).1 :=
    fun clock => (initialCallRun_swap ffi code oracle compiler limits frameSizes start clock).1
  have ffiEq : ∀ clock,
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true limits frameSizes clock)).2.ffi =
      (evaluate (.call none (some start) [] none)
        (initialState ffi code oracle compiler true zeroLimits .ln clock)).2.ffi :=
    fun clock => (initialCallRun_swap ffi code oracle compiler limits frameSizes start clock).2
  have failEq :
      (∃ clock, match (evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true limits frameSizes clock)).1 with
        | none => True
        | some (.err error) =>
          error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
        | _ => False) ↔
      (∃ clock, match (evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true zeroLimits .ln clock)).1 with
        | none => True
        | some (.err error) =>
          error ≠ .abort .timeoutError ∧ ∀ event, error ≠ .abort (.ffiError event)
        | _ => False) := by
    apply exists_congr
    intro clock
    rw [fstEq clock]
  have observationEq :
      terminatingObservation ffi code oracle compiler limits frameSizes start =
      terminatingObservation ffi code oracle compiler zeroLimits .ln start := by
    funext behavior
    apply propext
    constructor
    · rintro ⟨clock, state, result, outcome, run, ending, observed⟩
      cases nextRun : evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true zeroLimits .ln clock) with
      | mk res' state' =>
        have resultEq := fstEq clock
        rw [run, nextRun] at resultEq
        simp only [] at resultEq
        subst resultEq
        have ffiSame := ffiEq clock
        rw [run, nextRun] at ffiSame
        simp only [] at ffiSame
        exact ⟨clock, state', result, outcome, nextRun, ending, by rw [observed, ffiSame]⟩
    · rintro ⟨clock, state, result, outcome, run, ending, observed⟩
      cases firstRun : evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true limits frameSizes clock) with
      | mk res' state' =>
        have resultEq := fstEq clock
        rw [run, firstRun] at resultEq
        simp only [] at resultEq
        subst resultEq
        have ffiSame := ffiEq clock
        rw [run, firstRun] at ffiSame
        simp only [] at ffiSame
        exact ⟨clock, state', result, outcome, firstRun, ending, by rw [observed, ← ffiSame]⟩
  have traceEq :
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true limits frameSizes clock)).2.ffi.ioEvents) =
      (fun trace => ∃ clock, trace = HolLList.fromList
        (evaluate (.call none (some start) [] none)
          (initialState ffi code oracle compiler true zeroLimits .ln clock)).2.ffi.ioEvents) := by
    funext trace
    apply propext
    constructor
    · rintro ⟨clock, traceEq'⟩
      refine ⟨clock, ?_⟩
      rw [ffiEq clock] at traceEq'
      exact traceEq'
    · rintro ⟨clock, traceEq'⟩
      refine ⟨clock, ?_⟩
      rw [← ffiEq clock] at traceEq'
      exact traceEq'
  unfold semantics
  dsimp only
  rw [observationEq, traceEq]
  refine ite_congr (propext failEq) ?_ ?_
  · intro _
    rfl
  · intro _
    rfl

end Flapjack.Compiler.Backend.DataProps
