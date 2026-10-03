import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSAAllocation
import Flapjack.Compiler.Backend.WordToStack.ProductionLocations

namespace Flapjack.WordAlloc
open RiscV RiscV.CakeRegAlloc

/-- The shared allocator consumer constructs its returned spill state from its
own final program and colouring, for any actual SSA and dead-code producers.
This is implementation correspondence, with no HOL semantic original. -/
theorem allocatorWithSsa_spillState {α : Type} [OfNat α 0] [WordCseHash α] [BEq α]
    (dead : WordProg α → WordProg α)
    (ssa : Nat → WordProg α → Option (WordSsaState × List Nat × WordProg α))
    (label : Nat) (parameters : List Nat) (source : WordProg α)
    (output : CakeAllocationWithColour α)
    (produced : cakeAllocateWordFunctionAfterDeadWithColourWithSsa dead ssa label parameters source = some output) :
    output.allocation = cakeColourWordSpillState cakeRiscVRegisterCount
      parameters output.program output.colouring := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourWithSsa at produced
  split at produced <;> simp_all
  cases ssaResult : ssa parameters.length source with
  | none => simp [ssaResult] at produced
  | some result =>
    rcases result with ⟨state, formals, body⟩
    simp only [ssaResult, Option.bind_some] at produced
    repeat' (split at produced <;> simp_all)
    all_goals rcases produced with ⟨_, _, _, rfl⟩
    all_goals rfl

/-- The actual native SSA entry supplies the complete constructor relation.
Success identifies the observed result; it does not assume its locations or
frame equation. No assertion of HOL pass simulation is made here. -/
theorem nativeAllocator_spillState {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source = some output) :
    output.allocation = cakeColourWordSpillState cakeRiscVRegisterCount
      parameters output.program output.colouring := by
  unfold cakeAllocateWordFunctionAfterDeadWithColourNativeSSA at produced
  cases encoded : wordLangProgToHOL source with
  | none => simp [encoded] at produced
  | some native =>
    simp only [encoded, Option.bind_some] at produced
    exact allocatorWithSsa_spillState _ _ label parameters source output produced

/-- Every lookup in the actual native SSA allocation uses the producer's own
original-parameter/final-program domain and total colouring. Absent keys remain
absent. This does not infer move operand bounds or full state simulation. -/
theorem nativeAllocator_locationLookup {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source = some output)
    (name : Nat) :
    lookupNatInfo name output.allocation.locations =
      if name ∈ parameters ++ wordProgVariables output.program then
        some (cakeColourLocation cakeRiscVRegisterCount
          (cakeColourFrameSlots cakeRiscVRegisterCount parameters output.program output.colouring).2
          (CakeAlloc.totalColour output.colouring name))
      else none := by
  rw [nativeAllocator_spillState label parameters source output produced]
  exact Flapjack.cakeColourWordSpillState_lookup _ _ _ _ name

/-- The actual native SSA spill cursor is the complete native frame occupancy,
including the original argument-area floor. This is a production projection,
not a narrowed HOL correctness theorem. -/
theorem nativeAllocator_frameOccupancy {width : Nat} [NeZero width]
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : CakeAllocationWithColour (BitVec width))
    (produced : cakeAllocateWordFunctionAfterDeadWithColourNativeSSA label parameters source = some output) :
    output.allocation.nextSpill =
      max ((wordProgCakeMaxVar output.colouredProgram / 2 + 1) - cakeRiscVRegisterCount)
        (parameters.length - cakeRiscVRegisterCount) := by
  rw [nativeAllocator_spillState label parameters source output produced]
  exact cakeColourWordSpillState_nextSpill_eq_occupancy _ _ _ _

end Flapjack.WordAlloc
