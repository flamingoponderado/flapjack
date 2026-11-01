import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

/-! Local and control frames for memory primitive application. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Allocating a reference changes the reference store but preserves the
local and control fields used by the pass simulation. -/
theorem doAppAux_ref_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .ref) args state = .val (value, next)) : SameLocalControl state next := by
  simp [doAppAux, applyNonFfi] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful array allocation preserves locals and control fields. -/
theorem doAppAux_refArray_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .refArray) args state = .val (value, next)) : SameLocalControl state next := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi] at run
        case number count =>
          by_cases negative : count < 0
          · simp [negative] at run
          · simp [negative] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful GC-configuration primitive preserves locals and control. -/
theorem doAppAux_configGC_frame {C F : Type} (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.memOp .configGC) args state = .val (value, next)) : SameLocalControl state next := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi] at run
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi] at run
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Lift a memory auxiliary frame through resource bookkeeping. -/
theorem doApp_mem_frame_of_aux {C F : Type} (op : ClosLang.MemOp)
    (auxFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doAppAux (.memOp op) args before = .val (value, after) → SameLocalControl before after)
    (args : List Value) (state next : State C F) (value : Value)
    (run : doApp (.memOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.memOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := doSpace_frame (.memOp op) args state accounted space
    have second := auxFrame args _ next value run
    have second' : SameLocalControl accounted next := by
      simpa [SameLocalControl, doStack, doLimSafe] using second
    exact first.trans second'

end Flapjack.Compiler.Backend.DataSem
