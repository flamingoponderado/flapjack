import Flapjack.Compiler.Backend.StackNames
import Flapjack.Compiler.Backend.Semantics.StackSem.Labels

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemLabels

/-- Untagged candidate for HOL get_labels_comp (stack_namesProofScript287-293).
The words qualifier checker cannot yet resolve HolProg; acceptance remains open.
Unconditional label-set preservation under register renaming.
The function equality retains extensional HOL set equality and imposes no
renaming bijection, evaluation, or target-label premise. -/
theorem getLabelsComp {width : Nat} [NeZero width]
    (names : Flapjack.FiniteMap Nat Nat) (p : HolProg width) :
    getLabels (progComp names p) = getLabels p := by
  induction p using progComp.induct <;>
    try simp_all [progComp, getLabels]
  case case11 rh target handler ihHandler ihReturn =>
    cases rh with
    | none =>
      cases handler with
      | none => rfl
      | some h =>
        obtain ⟨body, l1, l2⟩ := h
        rfl
    | some ret =>
      obtain ⟨body, reg, l1, l2⟩ := ret
      cases handler with
      | none => simp_all [progComp, getLabels]
      | some h =>
        obtain ⟨body, l1, l2⟩ := h
        simp_all [progComp, getLabels]

end Flapjack.Compiler.Backend.StackNames
