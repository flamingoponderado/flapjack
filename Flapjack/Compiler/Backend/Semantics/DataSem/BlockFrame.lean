import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFrame

/-! Local and control frames for block primitive application. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- Lift an auxiliary block frame through the dispatcher's space and stack
bookkeeping. This is Flapjack infrastructure for pass simulations. -/
theorem doApp_block_frame_of_aux {C F : Type} (op : ClosLang.BlockOp)
    (auxFrame : ∀ (args : List Value) (before after : State C F) (value : Value),
      doAppAux (.blockOp op) args before = .val (value, after) → SameLocalControl before after)
    (args : List Value) (state next : State C F) (value : Value)
    (run : doApp (.blockOp op) args state = .val (value, next)) : SameLocalControl state next := by
  simp only [doApp] at run
  cases space : doSpace (.blockOp op) args state with
  | none => simp [space] at run
  | some accounted =>
    simp only [space] at run
    have first := doSpace_frame (.blockOp op) args state accounted space
    have second := auxFrame args _ next value run
    have second' : SameLocalControl accounted next := by
      simpa [SameLocalControl, doStack, doLimSafe] using second
    exact first.trans second'

/-- A successful block tag comparison preserves locals and control fields. -/
theorem doAppAux_tagEq_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doAppAux (.blockOp (.tagEq tag)) args state = .val (value, next)) :
    SameLocalControl state next := by
  cases args with
  | nil => simp [doAppAux, applyNonFfi] at run
  | cons arg rest =>
    cases rest with
    | cons other tail => simp [doAppAux, applyNonFfi] at run
    | nil =>
      cases arg <;> simp [doAppAux, applyNonFfi] at run
      all_goals obtain ⟨rfl, rfl⟩ := run
      all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A successful block tag comparison preserves locals and control fields
through the full dispatcher. -/
theorem doApp_tagEq_frame {C F : Type} (tag : Nat) (args : List Value)
    (state next : State C F) (value : Value)
    (run : doApp (.blockOp (.tagEq tag)) args state = .val (value, next)) :
    SameLocalControl state next :=
  doApp_block_frame_of_aux (.tagEq tag) (doAppAux_tagEq_frame tag) args state next value run

end Flapjack.Compiler.Backend.DataSem
