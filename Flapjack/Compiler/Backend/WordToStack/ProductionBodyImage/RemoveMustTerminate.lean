import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordRemove

/-! Native compiler infrastructure for the actual post-allocation removal pass.
HOL's `full_compile_single` applies this pass before WordToStack. These compiler
equations have no separately named HOL originals and carry no HOL tags. They
retain arbitrary inputs, all bitmap state, and both optional Call continuations;
no target evaluation or successful-output premise is needed. -/

namespace Flapjack.ProductionBodyImage
open Compiler.Backend Compiler.Backend.WordToStack.Native
open Compiler.Backend.WordRemove Compiler.Encoders.Asm

/-- Removing termination annotations preserves the complete original maximum,
including the original tail-call handler convention. -/
theorem maxVarRemoveMustTerminate {width : Nat} [NeZero width]
    (native : WordLangProgHOL (BitVec width)) :
    maxVarHOL (removeMustTerminate native) = maxVarHOL native := by
  cases nativeEquation : native with
  | seq first second =>
    simp [removeMustTerminate, maxVarHOL, maxVarRemoveMustTerminate first,
      maxVarRemoveMustTerminate second]
  | mustTerminate body =>
    simp [removeMustTerminate, maxVarHOL, maxVarRemoveMustTerminate body]
  | loop liveIn body liveOut =>
    simp [removeMustTerminate, maxVarHOL, maxVarRemoveMustTerminate body]
  | ite op condition right first second =>
    cases right <;> simp [removeMustTerminate, maxVarHOL,
      maxVarRemoveMustTerminate first, maxVarRemoveMustTerminate second]
  | call returns target arguments handler =>
    rcases returnsEquation : returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handlerEquation : handler with _ | ⟨exception, continuation, h1, h2⟩ <;>
      simp [removeMustTerminate, maxVarHOL]
    all_goals rw [maxVarRemoveMustTerminate body]
    all_goals try rw [maxVarRemoveMustTerminate continuation]
  | _ => simp [removeMustTerminate, maxVarHOL]
termination_by sizeOf native
decreasing_by all_goals subst_vars; decreasing_trivial

/-- The whole lowering result, not just its body, is unchanged by the actual
post-allocation annotation removal, at every incoming bitmap state and frame. -/
theorem compNativeRemoveMustTerminate {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (perf : Bool)
    (native : WordLangProgHOL (BitVec width))
    (bitmaps : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    compNative config perf (removeMustTerminate native) bitmaps frame =
      compNative config perf native bitmaps frame := by
  cases nativeEquation : native with
  | seq first second =>
    simp [removeMustTerminate, compNative,
      compNativeRemoveMustTerminate config perf first,
      compNativeRemoveMustTerminate config perf second]
  | mustTerminate body =>
    simp [removeMustTerminate, compNative, compNativeRemoveMustTerminate config perf body]
  | loop liveIn body liveOut =>
    simp [removeMustTerminate, compNative, compNativeRemoveMustTerminate config perf body]
  | ite op condition right first second =>
    simp [removeMustTerminate, compNative,
      compNativeRemoveMustTerminate config perf first,
      compNativeRemoveMustTerminate config perf second]
  | call returns target arguments handler =>
    rcases returnsEquation : returns with _ | ⟨values, sets, body, l1, l2⟩ <;>
      rcases handlerEquation : handler with _ | ⟨exception, continuation, h1, h2⟩ <;>
      simp [removeMustTerminate, compNative]
    all_goals rw [compNativeRemoveMustTerminate config perf body]
    all_goals try rw [compNativeRemoveMustTerminate config perf continuation]
    all_goals simp
  | _ => simp [removeMustTerminate, compNative]
termination_by sizeOf native
decreasing_by all_goals subst_vars; decreasing_trivial

/-- Complete program output, frame and final bitmap state are preserved. -/
theorem compileProgNativeRemoveMustTerminate {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (perf : Bool)
    (native : WordLangProgHOL (BitVec width)) (arity registers : Nat)
    (bitmaps : AppList (BitVec width) × Nat) :
    compileProgNative config perf (removeMustTerminate native) arity registers bitmaps =
      compileProgNative config perf native arity registers bitmaps := by
  simp only [compileProgNative, maxVarRemoveMustTerminate,
    compNativeRemoveMustTerminate]

/-- The complete ordered native function traversal preserves identifiers,
frames and threaded bitmap state through the real final Word removal pass. -/
theorem compileWordToStackNativeRemoveMustTerminate {width : Nat} [NeZero width]
    {Identifier : Type} (config : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (Identifier × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : AppList (BitVec width) × Nat) :
    compileWordToStackNative config perf registers
      (rows.map fun (identifier, arity, body) =>
        (identifier, arity, removeMustTerminate body)) bitmaps =
      compileWordToStackNative config perf registers rows bitmaps := by
  induction rows generalizing bitmaps with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨identifier, arity, body⟩
    simp only [List.map_cons, compileWordToStackNative,
      compileProgNativeRemoveMustTerminate, ih]

/-- Whole native top-level output equality includes bitmap words, exact Spt
configuration, the complete frame list and both prepended stub bodies. -/
theorem compileNativeRemoveMustTerminate {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (perf : Bool)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    compileNative config perf (rows.map fun (identifier, arity, body) =>
      (identifier, arity, removeMustTerminate body)) = compileNative config perf rows := by
  simp only [compileNative, compileWordToStackNativeRemoveMustTerminate]

end Flapjack.ProductionBodyImage
