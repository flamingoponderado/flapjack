import Flapjack.Lab

namespace Flapjack.Compiler.Backend.StackNames

/-- Flapjack production projection check, not a HOL theorem port: the broad
StackProg carrier remains distinct from HolProg. Both non-tail Call variants
now rename the integer link field as HOL comp does. -/
theorem stackMapRegisters_call_link {α : Type} (map : Nat → Nat)
    (body : Flapjack.StackProg α) (link returnLabel entryLabel : Nat)
    (target : Flapjack.StackCallTarget)
    (handler : Option (Flapjack.StackProg α × Nat × Nat)) :
    Flapjack.stackMapRegisters map (.call (some (body, link, returnLabel, entryLabel)) target handler) =
      .call (some (Flapjack.stackMapRegisters map body, map link, returnLabel, entryLabel))
        (Flapjack.stackMapCallTarget map target)
        (handler.map fun (p, e, h) => (Flapjack.stackMapRegisters map p, e, h)) := by
  cases handler with
  | none => simp [Flapjack.stackMapRegisters]
  | some h => obtain ⟨p, e, h⟩ := h; simp [Flapjack.stackMapRegisters]

/-- Local old/new output evidence: the executed Lab flatten projection ignores
Call link metadata. This unconditional equality covers both handler forms;
it does not establish whole StackProg/HolProg transition correspondence. -/
theorem labFlatten_call_link_irrelevant {α : Type} (tail : Bool)
    (sectionId counter : Nat) (continues breaks : List Nat)
    (body : Flapjack.StackProg α) (oldLink newLink returnLabel entryLabel : Nat)
    (target : Flapjack.StackCallTarget)
    (handler : Option (Flapjack.StackProg α × Nat × Nat)) :
    Flapjack.labFlatten tail sectionId counter continues breaks
      (.call (some (body, oldLink, returnLabel, entryLabel)) target handler) =
    Flapjack.labFlatten tail sectionId counter continues breaks
      (.call (some (body, newLink, returnLabel, entryLabel)) target handler) := by
  cases handler with
  | none => simp [Flapjack.labFlatten]
  | some h => obtain ⟨p, e, h⟩ := h; simp [Flapjack.labFlatten]

end Flapjack.Compiler.Backend.StackNames
