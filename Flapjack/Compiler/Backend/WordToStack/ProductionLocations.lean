import Flapjack.RiscV.CakeRegAlloc
import Flapjack.Compiler.Backend.WordToStackRegFormat
import Flapjack.RiscV.WordDeadCode

namespace Flapjack
open RiscV RiscV.CakeRegAlloc

private theorem lookupNameMap {β : Type u} (names : List Nat) (value : Nat → β)
    (name : Nat) :
    lookupNatInfo name (names.map (fun key => (key, value key))) =
      if name ∈ names then some (value name) else none := by
  induction names with
  | nil => simp [lookupNatInfo]
  | cons head tail ih =>
      by_cases equal : head = name
      · subst head
        simp [lookupNatInfo]
      · simp [lookupNatInfo, equal, Ne.symm equal, ih]

/-- Actual colour location agrees with the literal native formatting operation
for every colour and frame, including odd colours and natural subtraction at
out-of-range slots. No evenness or in-frame premise is needed for this equation.
Flapjack-only representation relation, not a HOL semantic theorem. -/
theorem cakeColourLocation_formatVar (k frame colour : Nat) :
    cakeColourLocation k frame colour =
      match Compiler.Backend.WordToStackRegFormat.formatVar k (some (colour / 2)) with
      | .inl register => .register register
      | .inr slot => .stack (frame - 1 - (slot - k)) := by
  by_cases below : colour / 2 < k
  · simp [cakeColourLocation, Compiler.Backend.WordToStackRegFormat.formatVar, below]
  · simp [cakeColourLocation, Compiler.Backend.WordToStackRegFormat.formatVar, below]

/-- Lookup in the actual allocator's location map, with its real name collection
and actual total colouring. Duplicate names are permitted; every duplicate
gets the same location. Absent names remain absent. No desired lookup equality
or successful allocation is assumed. This is Flapjack infrastructure. -/
theorem cakeColourWordSpillState_lookup {α : Type u}
    (k : Nat) (parameters : List Nat) (program : WordProg α)
    (colouring : NatInfoMap Nat) (name : Nat) :
    lookupNatInfo name (cakeColourWordSpillState k parameters program colouring).locations =
      if name ∈ parameters ++ wordProgVariables program then
        some (cakeColourLocation k (cakeColourFrameSlots k parameters program colouring).2
          (CakeAlloc.totalColour colouring name))
      else none := by
  unfold cakeColourWordSpillState
  dsimp only
  rw [lookupNameMap]
  simp

/-- The actual successful retained allocator supplies this location relation
from its own colouring and final program. The name domain uses the original
parameters passed to the allocator, exactly as its implementation does, not
the renamed parameter list. A success equation names the observed result;
no desired output location or reconstructed colouring is assumed. -/
theorem retainedAllocator_locationLookup {α : Type}
    [OfNat α 0] [WordCseHash α] [BEq α]
    (label : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (name : Nat) :
    lookupNatInfo name output.allocation.locations =
      if name ∈ parameters ++ wordProgVariables output.program then
        some (cakeColourLocation cakeRiscVRegisterCount
          (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).2
          (CakeAlloc.totalColour output.colouring name))
      else none := by
  rw [cakeAllocateWordFunctionAfterDeadWithColour_allocation label parameters program output allocated]
  exact cakeColourWordSpillState_lookup _ _ _ _ name

/-- Native operand-format correspondence for the actual retained allocation
lookup. This keeps absence explicit, covers the full original name domain,
and uses the observed allocation's own colouring. It does not address the
scheduler's `NONE` temporary, scratch conventions, body/bitmap equivalence,
or full pass correctness. There is no HOL theorem for this production map. -/
theorem retainedAllocator_nativeLocationLookup {α : Type}
    [OfNat α 0] [WordCseHash α] [BEq α]
    (label : Nat) (parameters : List Nat) (program : WordProg α)
    (output : CakeAllocationWithColour α)
    (allocated : cakeAllocateWordFunctionAfterDeadWithColour label parameters program = some output)
    (name : Nat) :
    lookupNatInfo name output.allocation.locations =
      if name ∈ parameters ++ wordProgVariables output.program then
        some (match Compiler.Backend.WordToStackRegFormat.formatVar cakeRiscVRegisterCount
            (some (CakeAlloc.totalColour output.colouring name / 2)) with
          | .inl register => .register register
          | .inr slot => .stack
              ((cakeColourFrameSlots cakeRiscVRegisterCount parameters
                output.program output.colouring).2 - 1 - (slot - cakeRiscVRegisterCount)))
      else none := by
  rw [retainedAllocator_locationLookup label parameters program output allocated name]
  split
  · rw [cakeColourLocation_formatVar]
  · rfl

end Flapjack
