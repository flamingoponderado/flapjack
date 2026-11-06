import Flapjack.Compiler.Backend.BviToData.Proofs.Value
import Flapjack.Compiler.Backend.Semantics.DataSem.Control
import Flapjack.Compiler.Backend.Semantics.BviSem.Thunk

/-! Thunk inspection under the BVI-to-data value projection. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- Project the value carried by a data-language thunk result. -/
def projectThunkResult : DataSem.DestThunkResult → BviSem.DestThunkResult
  | .badRef => .badRef
  | .notThunk => .notThunk
  | .isThunk mode value => .isThunk mode (dataToBviValue value)

/-- Lookup-related reference stores inspect projected thunk values identically.
This is Flapjack infrastructure for the pass simulation. -/
theorem destThunk_projection (value : DataSem.Value)
    (dataRefs : Spt (BvlSem.Ref DataSem.Value)) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    BviSem.destThunk (dataToBviValue value) bviRefs = projectThunkResult (DataSem.destThunk value dataRefs) := by
  cases value with
  | number n => simp [dataToBviValue, BviSem.destThunk, DataSem.destThunk, projectThunkResult]
  | word64 w => simp [dataToBviValue, BviSem.destThunk, DataSem.destThunk, projectThunkResult]
  | block timestamp tag values => simp [dataToBviValue, BviSem.destThunk, DataSem.destThunk, projectThunkResult]
  | codePtr label => simp [dataToBviValue, BviSem.destThunk, DataSem.destThunk, projectThunkResult]
  | refPtr bit address =>
    simp only [dataToBviValue, BviSem.destThunk, DataSem.destThunk]
    rw [related address]
    cases found : sptLookup address dataRefs with
    | none => simp [projectThunkResult]
    | some ref =>
      cases ref with
      | valueArray values => simp [dataToBviRef, projectThunkResult]
      | byteArray flag bytes => simp [dataToBviRef, projectThunkResult]
      | mutBlock tag finished left current right => simp [dataToBviRef, projectThunkResult]
      | thunk mode body => cases bit <;> simp [dataToBviRef, projectThunkResult]

/-- The evaluated-thunk update restriction is invariant under value and
reference projection. This is Flapjack primitive-simulation infrastructure. -/
theorem badThunkUpdate_projection (mode : AstHOL.ThunkMode) (value : DataSem.Value)
    (dataRefs : Spt (BvlSem.Ref DataSem.Value)) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (related : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef) :
    BvlSem.badThunkUpdate mode (dataToBviValue value) bviRefs ↔
      DataSem.badThunkUpdate mode value dataRefs := by
  have inspected := destThunk_projection value dataRefs bviRefs related
  rw [BviSem.destThunk_fromBvl] at inspected
  unfold BvlSem.badThunkUpdate DataSem.badThunkUpdate
  cases hd : DataSem.destThunk value dataRefs <;>
    cases hb : BvlSem.destThunk (dataToBviValue value) bviRefs <;>
    simp_all [projectThunkResult, BviSem.fromBvlThunkResult]

end Flapjack.Compiler.Backend.BviToData
