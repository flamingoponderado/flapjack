module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Batteries.Data.List.Basic

@[expose] public section

/-! Data-language stack frame size relations. -/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack.Compiler.Backend.DataSem

/-- Stack frames have the same accounted size. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "same_stack_size_def"]
def sameStackSize (x y : Stack) : Prop := sizeOfStackFrame x = sizeOfStackFrame y

/-- Pointwise equal frame sizes give equal total stack sizes. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "same_stack_size_size_of_stack"]
theorem sameStackSize_sizeOfStack (xs ys : List Stack) (related : List.Forall₂ sameStackSize xs ys) :
    sizeOfStack xs = sizeOfStack ys := by
  induction related with
  | nil => rfl
  | cons frame rest ih =>
    simp only [sizeOfStack, List.foldr_cons] at ih ⊢
    rw [frame, ih]

end Flapjack.Compiler.Backend.DataProps
