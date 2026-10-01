import Flapjack.Compiler.Backend.WordToStack.Proofs.Frames

/-! Original handler_val observations using independent non-word carriers.
The function-valued fixtures also check that no equality or decidability
requirement has been imposed on any ignored payload type. -/
namespace Flapjack.Test.WordToStackHandlerValGeneralityParity
open Flapjack.WordToStackProofs

example : handlerVal ([] : List (Option Bool × Nat × List Nat)) = 1 := by cbv
example : handlerVal [((none : Option Bool), 77, ([] : List Nat))] = 2 := by cbv
example : handlerVal [(some false, (77 : Nat), ([] : List Nat))] = 5 := by cbv
example : handlerVal [((none : Option Bool), (11 : Nat), [1,2,3])] = 5 := by cbv
example : handlerVal [(some true, (11 : Nat), [7,9])] = 7 := by cbv
example : handlerVal [((none : Option Bool), (11 : Nat), [1,2]),
    (some false, 77, []), (none, 0, [3])] = 10 := by cbv
example : handlerVal [((none : Option Bool), (fun n : Nat => n + 1), [9])] = 3 := by cbv
example : handlerVal [(some false, true,
    [(fun n : Nat => n), (fun n : Nat => n + 1)])] = 7 := by cbv

example {α β γ : Type} (ignored : β) (frame : List γ)
    (tail : List (Option α × β × List γ)) :
    handlerVal ((none, ignored, frame) :: tail) = 1 + frame.length + handlerVal tail := rfl
example {α β γ : Type} (handler : α) (ignored : β) (frame : List γ)
    (tail : List (Option α × β × List γ)) :
    handlerVal ((some handler, ignored, frame) :: tail) = 4 + frame.length + handlerVal tail := rfl

end Flapjack.Test.WordToStackHandlerValGeneralityParity
